package tla2sany.semantic;

import tla2sany.st.TreeNode;

public class RawTlaNode extends ExprNode {
	private String rawTLA;

	RawTlaNode(String tla, TreeNode stn) {
		super(RawTlaKind, stn);
		rawTLA = tla;
	}

	@Override
	  protected String toTLA(boolean pretty) {
		  return rawTLA;
	  }
}
