package tlc2;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import net.automatalib.automaton.fsa.CompactNFA;

public class Main {

    public static void main(String[] args) {
        if (args.length == 2 || args.length == 3) {
        	final String tla = args[0];
        	final String cfg = args[1];
        	final boolean ignoreErrors = args.length == 3 && args[2].equals("--ignore-errs");
        	CompactNFA<String> lts = new TLC().createLTS(tla, cfg, ignoreErrors);
        	FSPVisitor.printFSP(lts, lts.getInputAlphabet());
        }
        else if (args.length == 4 && args[2].equals("--reproduce")) {
        	final String tla = args[0];
        	final String cfg = args[1];
        	final String rawTrace = args[3];
        	final List<String> trace = Utils.toArrayList(rawTrace.split(","));
        	final Set<String> alphabet = new TLC().createLTS(tla, cfg, false).getInputAlphabet().stream().collect(Collectors.toSet());
        	final Set<String> violatedInvs = TraceReproducer.reproduceTrace(trace, tla, cfg, alphabet);
        	if (violatedInvs.isEmpty()) {
        		System.out.println("Trace is safe.");
        	}
        	else {
        		System.out.println("The following invariants are violated by the trace:");
        		for (final String inv : violatedInvs) {
        			System.out.println(inv);
        		}
        	}
        }
        else {
        	System.out.println("usage: TLAtoLTS <tla> <cfg> [--ignore-errs] [--reproduce trace]");
        }
        System.exit(0);
    }
}
