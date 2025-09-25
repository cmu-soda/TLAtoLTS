package tlc2;

import java.util.HashSet;
import java.util.Set;

import net.automatalib.alphabet.Alphabet;
import net.automatalib.automaton.fsa.NFA;
import net.automatalib.common.util.Holder;
import net.automatalib.util.ts.traversal.TSTraversal;
import net.automatalib.util.ts.traversal.TSTraversalAction;
import net.automatalib.util.ts.traversal.TSTraversalVisitor;

public class FSPVisitor<S, I> implements TSTraversalVisitor<S, I, S, Integer> {
	private StringBuilder builder;
	private NFA<S, I> nfa;
	private Set<S> visited;
	private Alphabet<I> alphabet;
	
	public FSPVisitor(NFA<S, I> nfa, Alphabet<I> alphabet) {
		this.builder = new StringBuilder();
		this.nfa = nfa;
		this.visited = new HashSet<>();
		this.alphabet = alphabet;
	}

	@Override
	public TSTraversalAction processInitial(S state, Holder<Integer> dummy) {
		return TSTraversalAction.EXPLORE;
	}

	@Override
	public boolean startExploration(S state, Integer dummy) {
		if (!visited.contains(state)) {
            visited.add(state);
            if (builder.lastIndexOf(" | ") == builder.length() - 3) {;
                builder.setLength(builder.length() - 3);
                builder.append("),\n");
            }
            builder.append("S" + state + " = (");
            return true;
        }
		return false;
	}

	@Override
	public TSTraversalAction processTransition(S source, Integer dummyIn, I input, S transition, S succ, Holder<Integer> dummyOut) {
        // check deadlock state
        boolean isDeadlock = true;
        for (I a : alphabet) {
            if (!nfa.getTransitions(succ, a).isEmpty()) {
                isDeadlock = false;
                break;
            }
        }
        final String action = input.toString().toLowerCase();
        if (!nfa.isAccepting(succ)) {
        	builder.append(action + " -> ERROR | ");
            return TSTraversalAction.IGNORE;
        } else if (isDeadlock) {
            builder.append(action + " -> STOP | ");
            return TSTraversalAction.IGNORE;
        } else {
            builder.append(action + " -> S" + succ + " | ");
            return TSTraversalAction.EXPLORE;
        }
	}
	
	public static <S,I> void printFSP(NFA<S,I> nfa, Alphabet<I> alphabet) {
		FSPVisitor<S,I> visitor = new FSPVisitor<>(nfa,alphabet);
	    TSTraversal.breadthFirst(nfa, alphabet, visitor);
	    if (visitor.builder.lastIndexOf(" | ") == visitor.builder.length() - 3) {
	    	visitor.builder.setLength(visitor.builder.length() - 3);
	    	visitor.builder.append(").");
	    }
	    System.out.println(visitor.builder.toString());
	}
}