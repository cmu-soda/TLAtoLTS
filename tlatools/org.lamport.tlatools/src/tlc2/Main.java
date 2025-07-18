package tlc2;

import net.automatalib.automaton.fsa.CompactNFA;

public class Main {

    public static void main(String[] args) {
        if (args.length == 2 || args.length == 3) {
        	final String tla = args[0];
        	final String cfg = args[1];
        	final boolean ignoreErrors = args.length == 3 && args[2].equals("--ignore-errs");
        	CompactNFA<String> lts = new TLC().createLTS(tla, cfg, ignoreErrors);
        	System.out.println("Num states: " + lts.getStates().size());
        }
        else {
        	System.out.println("usage: TLAtoLTS <tla> <cfg> [--ignore-errs]");
        }
        System.exit(0);
    }
}