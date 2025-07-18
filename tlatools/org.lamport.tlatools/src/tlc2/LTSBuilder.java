package tlc2;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import net.automatalib.alphabet.Alphabets;
import net.automatalib.automaton.fsa.CompactNFA;
import net.automatalib.util.automaton.builder.AutomatonBuilders;
import tlc2.tool.Action;
import tlc2.tool.TLCState;

public class LTSBuilder {
	private Set<LTSBState> initStates = new HashSet<>();
	private Set<LTSBState> allStates = new HashSet<>();
	private Set<LTSBTransition> goodTransitions = new HashSet<>();
	private Set<LTSBTransition> badTransitions = new HashSet<>();
	private Set<String> allActions = new HashSet<>();
	private boolean initialError = false;
    private boolean ignoreErrors;
    
    public LTSBuilder(boolean ignoreErrors) {
    	this.ignoreErrors = ignoreErrors;
    }
	
	public boolean ignoreErrors() {
		return this.ignoreErrors;
	}

	public int size() {
		return this.allStates.size();
	}

    public void addInitState(final TLCState s) {
		final LTSBState lbs = new LTSBState(s);
    	this.initStates.add(lbs);
    	this.allStates.add(lbs);
    }

    public void addBadInitState(final TLCState s) {
		addInitState(s);
		initialError = true;
    }

    public void addState(final TLCState s) {
		final LTSBState lbs = new LTSBState(s);
    	this.allStates.add(lbs);
    }

    public void addTransition(final TLCState src, final Action act, final TLCState dst) {
    	final LTSBState lbsSrc = new LTSBState(src);
    	final String strAct = act.actionNameWithParams();
    	final LTSBState lbsDst = new LTSBState(dst);
    	final LTSBTransition transition = new LTSBTransition(lbsSrc, strAct, lbsDst);
    	this.allActions.add(strAct);
    	this.goodTransitions.add(transition);
    }

    public void addTransitionToErr(final TLCState src, final Action act) {
    	final LTSBState lbsSrc = new LTSBState(src);
    	final String strAct = act.actionNameWithParams();
    	final LTSBTransition transition = new LTSBTransition(lbsSrc, strAct);
    	this.allActions.add(strAct);
    	this.badTransitions.add(transition);
    }

    public CompactNFA<String> toNFA() {
    	CompactNFA<String> compactNFA = AutomatonBuilders.newNFA(Alphabets.fromCollection(this.allActions)).create();
    	final Integer ltsErrState = this.initialError ? compactNFA.addInitialState(false) : compactNFA.addState(false);

    	Map<LTSBState, Integer> lbsToLtsStates = new HashMap<>();
    	for (final LTSBState lbsState : this.allStates) {
    		final boolean isInitState = this.initStates.contains(lbsState);
			final int ltsState = isInitState ? compactNFA.addInitialState(true) : compactNFA.addState(true);
			lbsToLtsStates.put(lbsState, ltsState);
    	}

    	for (final LTSBTransition tr : this.goodTransitions) {
    		final Integer src = lbsToLtsStates.get(tr.src);
    		final String act = tr.act;
    		final Integer dest = lbsToLtsStates.get(tr.dest);
    		compactNFA.addTransition(src, act, dest);
    	}

    	for (final LTSBTransition tr : this.badTransitions) {
    		final Integer src = lbsToLtsStates.get(tr.src);
    		final String act = tr.act;
    		compactNFA.addTransition(src, act, ltsErrState);
    	}

    	return compactNFA;
    }
    
    
    private static class LTSBTransition {
    	public final LTSBState src;
    	public final String act;
    	public final LTSBState dest;
    	
    	public LTSBTransition(LTSBState s, String a, LTSBState d) {
    		src = s;
    		act = a;
    		dest = d;
    	}
    	
    	public LTSBTransition(LTSBState s, String a) {
    		src = s;
    		act = a;
    		dest = null;
    	}
    	
    	@Override
    	public boolean equals(Object o) {
    		if (o instanceof LTSBTransition) {
    			final LTSBTransition other = (LTSBTransition) o;
    			return this.src.equals(other.src) && 
    					this.act.equals(other.act) &&
    					this.dest.equals(other.dest);
    		}
    		return false;
    	}
    	
    	@Override
    	public int hashCode() {
    		return this.src.hashCode() * 11 + this.act.hashCode() * 7 + this.dest.hashCode();
    	}
    }
    
    private static class LTSBState {
    	private final long sid;
    	
    	public LTSBState(final TLCState s) {
    		sid = s.fingerPrint();
    	}
    	
    	@Override
    	public boolean equals(Object o) {
    		if (o instanceof LTSBState) {
    			final LTSBState other = (LTSBState) o;
    			return this.sid == other.sid;
    		}
    		return false;
    	}
    	
    	@Override
    	public int hashCode() {
    		return Long.hashCode(this.sid);
    	}
    }
}
