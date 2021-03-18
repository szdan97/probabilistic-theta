package hu.bme.mit.theta.xcfa.ir.passes;

import hu.bme.mit.theta.xcfa.XCFA;

/*
 * This class provides a variable elimination pass.
 * It gets rid of two types of redundant variables:
 *  -   Variables that are assigned exactly once and then exclusively used (read) without a branch in-between
 *      - Exception: procedure calls, due to potential side effects
 *  -   Variables that are assigned exactly once and then never used (read).
 *      - Exception: return variable
 */
public class VariableEliminationPass implements ProcedurePass {
    @Override
    public XCFA.Process.Procedure.Builder run(XCFA.Process.Procedure.Builder builder) {
        return null;
    }
}
