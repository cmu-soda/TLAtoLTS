package tlc2;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDefNode;
import tlc2.tool.impl.FastTool;

public class TraceReproducer {
	private static final String TLC_JAR_PATH = System.getProperty("user.home") + "/bin/tla2tools.jar";
    
	/**
	 * Returns a set of invariants (names) that are violated. Returns an empty set if no violations are found.
	 * @param trace
	 * @param tla
	 * @param cfg
	 * @param globalAlphabet
	 * @return
	 */
	public static Set<String> reproduceTrace(final List<String> trace, final String tla, final String cfg, final Set<String> globalAlphabet) {
		final String tlaName = tla.replaceAll("\\.tla", "");
		final String cfgName = cfg.replaceAll("\\.cfg", "");
		final String tlaFile = tlaName + ".tla";
		final String cfgFile = cfgName + ".cfg";
		
		// create a formula that says: at each time step i, we must take action i in <trace> (the given AlloyTrace)
		final String cexIdxVar = "cexTraceIdx";
		final String errVar = "err";
		final String inTraceConstraint = IntStream.range(0, trace.size())
				.mapToObj(i -> {
					final String act = trace.get(i);
					final String errVarChange = i < trace.size()-1 ? errVar+"' = "+errVar : errVar+"' = TRUE";
					return "/\\ " + cexIdxVar + " = " + i + " => " + act + " /\\ " + errVarChange;
				})
				.collect(Collectors.joining("\n"));
		final String outTraceConstraint = "/\\ " + cexIdxVar + " >= " + trace.size() + " => FALSE";
		final String traceConstraint = inTraceConstraint + "\n" + outTraceConstraint;
		
		// use the original TLA+ file to construct the reproducer spec
		TLC tlc = new TLC();
		tlc.createLTS(tlaFile, cfgFile, false);

    	final FastTool ft = (FastTool) tlc.tool;
		final String moduleName = tlc.getModelName();
		final ModuleNode mn = ft.getModule(moduleName);
		final List<OpDefNode> moduleNodes = Utils.toArrayList(mn.getOpDefs())
				.stream()
				// only retain module for the .tla file
				.filter(d -> moduleName.equals(d.getOriginallyDefinedInModuleNode().getName().toString()))
				.filter(d -> !d.getName().toString().equals("vars")) // remove the vars decl; we insert this manually
				.collect(Collectors.toList());
		
		List<String> strModuleNodes = moduleNodes
				.stream()
				.map(d -> {
					final String dname = d.getName().toString();
					final boolean isInternalAct = !globalAlphabet.contains(dname);
					if (tlc.actionsInSpec().contains(dname)) {
						if (isInternalAct) {
							d.addConjunct(cexIdxVar + "' = " + cexIdxVar);
						} else {
							d.addConjunct(cexIdxVar + "' = " + cexIdxVar + " + 1");
						}
					}
					else if (dname.equals("Init")) {
						d.addConjunct(cexIdxVar + " = 0");
						d.addConjunct(errVar + " = FALSE");
					}
					return d;
				 })
				.map(d -> d.toTLA())
				.collect(Collectors.toList());
		
		// add the trace constraint and the new spec decl to the list of muldes
		final String tcfName = "TraceConstraint";
		final String tcfSpecName = "TraceConstraintSpec";
		final String traceConstraintDecl = tcfName + " ==\n" + traceConstraint;
		final String internalActionDecl = "InternalAction == UNCHANGED<<cexTraceIdx,err>>";
		final String specVarDecl = tcfSpecName + " == Init /\\ [][Next /\\ (" + tcfName + " \\/ InternalAction)]_vars";
		strModuleNodes.add(traceConstraintDecl);
		strModuleNodes.add(internalActionDecl);
		strModuleNodes.add(specVarDecl);
		
		// gather all the consts
		final Map<String, Set<String>> sortElementsMap = createSortElementsMap(tlc, true);
		final Set<String> sortConsts = sortElementsMap.values()
				.stream()
				.reduce((Set<String>)new HashSet<String>(),
						(acc,l) -> Utils.union(acc, l.stream().collect(Collectors.toSet())),
						(l1,l2) -> Utils.union(l1,l2));
		final Set<String> allConsts = Utils.union(sortConsts, tlc.constantsInSpec().stream().collect(Collectors.toSet()));
		
		// construct the spec
		final String specName = "CexTrace";
		final String specBody = String.join("\n\n", strModuleNodes);
		
        final String specDecl = "--------------------------- MODULE " + specName + " ---------------------------";
        final String endModule = "=============================================================================";
        
        final List<String> moduleWhiteList =
        		Arrays.asList("Bags", "FiniteSets", "Functions", "Integers", "Json", "Naturals", "Randomization",
        				"NaturalsInduction", "RealTime", "Sequences", "SequencesExt", "TLC", "TLCExt");
        ArrayList<String> moduleNameList = Utils.filterArrayWhiteList(moduleWhiteList, ft.getModuleNames());
        // ensure that the naturals are included so we can increment the cexIdxVar
        if (!moduleNameList.contains("Naturals")) {
        	moduleNameList.add("Naturals");
        }
        // ensure that TLC is included for the definition of @@
        if (!moduleNameList.contains("TLC")) {
        	moduleNameList.add("TLC");
        }
        
        final Set<String> stateVars = Utils.union(tlc.stateVarsInSpec(), Utils.setOf(cexIdxVar,errVar));

        final String moduleList = String.join(", ", moduleNameList);
        final String constantsDecl = allConsts.isEmpty() ? "" : "CONSTANTS " + String.join(", ", allConsts);
        final String varList = String.join(", ", stateVars);
        final String modulesDecl = moduleList.isEmpty() ? "" : "EXTENDS " + moduleList;
        final String varsDecl = "VARIABLES " + varList;
        final String varsListDecl = "vars == <<" + varList + ">>";
        
        StringBuilder builder = new StringBuilder();
        builder.append(specDecl).append("\n");
        builder.append(modulesDecl).append("\n");
        builder.append("\n");
        builder.append(constantsDecl).append("\n");
        builder.append("\n");
        builder.append(varsDecl).append("\n");
        builder.append("\n");
        builder.append(varsListDecl).append("\n");
        builder.append("\n\n");
        builder.append(specBody);
        builder.append("\n");
        builder.append(endModule).append("\n");

        final String traceInSpecTla = specName + ".tla";
        Utils.writeFile(traceInSpecTla, builder.toString());
        
        // create the config file for the TLA+ reproducer
        StringBuilder cfgBuilder = new StringBuilder();
        final List<String> cfgLines = Utils.fileContents(cfgFile)
        		.stream()
        		.filter(l -> !l.contains("SPECIFICATION"))
        		.collect(Collectors.toList());
        final String cfgContent = String.join("\n", cfgLines) + "\nSPECIFICATION " + tcfSpecName + "\n";
        cfgBuilder.append(cfgContent);
        cfgBuilder.append("CONSTANTS\n");
        sortConsts.stream()
        		.filter(c -> !Utils.isIntegerString(c))
        		.forEach(c -> {
                	final String constAssg = c + "=" + c + "\n";
                	cfgBuilder.append(constAssg);
        		});
        final String traceInSpecCfg = specName + ".cfg";
        Utils.writeFile(traceInSpecCfg, cfgBuilder.toString());
        
        // run the spec and see if there is an error. the trace appears in the spec iff there is an error
        // use iterative deepening 
        final String[] cmd = {"java", "-jar", TLC_JAR_PATH, "-cleanup", "-deadlock", "-continue", "-config", traceInSpecCfg, traceInSpecTla};
		try {
			// run TLC and capture the output
			Process proc = Runtime.getRuntime().exec(cmd);
			List<String> tlcOutputLines = new ArrayList<>();
			BufferedReader tlcReader = new BufferedReader(new InputStreamReader(proc.getInputStream()));
			for (String line; (line = tlcReader.readLine()) != null; ) {
				tlcOutputLines.add(line);
			}
			
			// delete the temporary CexTrace.tla and CexTrace.cfg files that we create
			Runtime.getRuntime().exec(new String[]{"rm", "-f", traceInSpecTla});
			Runtime.getRuntime().exec(new String[]{"rm", "-f", traceInSpecCfg});
			
			// parse the output from TLC and find any invariants that were violated
			final Pattern invPattern = Pattern.compile("Error: Invariant (.*) is violated\\.");
			final Set<String> violatedInvariants = tlcOutputLines
					.stream()
					.filter(l -> l.matches(invPattern.pattern()))
					.map(l -> {
						final Matcher invMatcher = invPattern.matcher(l);
						Utils.assertTrue(invMatcher.find(), "Could not find regex in output!");
						return invMatcher.group(1);
					})
					.collect(Collectors.toSet());
			return violatedInvariants;
		}
		catch (IOException e) {
			Utils.assertTrue(false, "Error reproducing the trace");
		}
		return new HashSet<>(); // no invariants violated
	}
	
	private static Map<String, Set<String>> createSortElementsMap(TLC tlc, boolean sanitize) {
		// create a map of sort -> elements (elements = atoms)
		Map<String, Set<String>> sortElements = new HashMap<>();
		for (final List<String> constList : tlc.tool.getModelConfig().getConstantsAsList()) {
			if (constList.size() == 2) {
				// constList is a CONSTANT assignment
				final String sort = constList.get(0);
				final Set<String> elems = parseElements(constList.get(1), sanitize);
				if (elems != null) {
					sortElements.put(sort, elems);
				}
			}
		}
		return sortElements;
	}
	
	/**
	 * We expect <rawElems> to encode a set. If it doesn't, we throw.
	 * @param rawElems
	 * @return
	 */
	private static Set<String> parseElements(final String rawSet, boolean sanitize) {
		final String trimmedRawSet = rawSet.trim(); // to be extra defensive
		final char rawSetFirstChar = trimmedRawSet.charAt(0);
		final char rawSetLastChar = trimmedRawSet.charAt(trimmedRawSet.length()-1);
        // Uncomment to allow (ignore) non-set constants
		//if (!(rawSetFirstChar == '{' && rawSetLastChar == '}')) {
			//return null;
		//}
		Utils.assertTrue(rawSetFirstChar == '{' && rawSetLastChar == '}',
				"Sorts must be sets of elements; encountered not set value: " + rawSet);
		
		final String rawElems = trimmedRawSet.substring(1, trimmedRawSet.length()-1).trim();
		final List<String> tokens = Utils.toArrayList(rawElems.split(" "))
				.stream()
				.filter(e -> !e.equals(","))
				.collect(Collectors.toList());
		
		final List<List<String>> tokenGroups = createTokenGroups(tokens);
		return tokenGroups
				.stream()
				.map(g -> sanitize ? sanitizeTokensForAlloy(g) : recreateRawToken(g))
				.collect(Collectors.toSet());
	}
	
	private static List<List<String>> createTokenGroups(final List<String> tokens) {
		List<List<String>> groups = new ArrayList<>();
		int parenDepth = 0;
		List<String> curGroup = new ArrayList<>();
		for (int i = 0; i < tokens.size(); ++i) {
			final String tok = tokens.get(i);
			final boolean isLeftParen = tok.equals("{");
			final boolean isRightParen = tok.equals("}");
			
			// if the token is a curly brace (I'm overloading "curly brace" as "paren")
			if (isLeftParen) {
				++parenDepth;
			}
			else if (isRightParen) {
				--parenDepth;
			}
			else {
				// if it's not a paren, add it to the current token group
				curGroup.add(tok);
			}
			
			// when the parens are balanced we've completed a new token group
			if (parenDepth == 0) {
				groups.add(curGroup);
				curGroup = new ArrayList<>();
			}
		}
		return groups;
	}
	
	/**
	 * this code stub will ensure that curly braces and numbers are in a format where
	 * they can be correctly used in an Alloy file.
	 * @param toks
	 * @return
	 */
	private static String sanitizeTokensForAlloy(final List<String> toks) {
		if (toks.isEmpty()) {
			return "";
		}
		final boolean isSet = toks.size() > 1;
		if (isSet) {
			final String toksStr = toks
					.stream()
					.map(t -> t.trim())
					.collect(Collectors.joining());
			// add underscores to mark sets
			return "_" + toksStr + "_";
		} else {
			final String elem = toks.get(0).trim();
			// precede numbers with "NUM" to get the Alloy file to compile
			return elem.matches("[0-9]+") ? "NUM"+elem : elem;
		}
	}
	
	private static String recreateRawToken(final List<String> toks) {
		if (toks.isEmpty()) {
			return "";
		}
		final boolean isSet = toks.size() > 1;
		if (isSet) {
			final String toksStr = toks
					.stream()
					.map(t -> t.trim())
					.collect(Collectors.joining(","));
			return "{" + toksStr + "}";
		} else {
			final String elem = toks.get(0).trim();
			return elem;
		}
	}
}
