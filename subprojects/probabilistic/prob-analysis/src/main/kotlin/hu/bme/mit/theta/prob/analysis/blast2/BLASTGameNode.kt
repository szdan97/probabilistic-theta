package hu.bme.mit.theta.prob.analysis.blast2

import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType

interface BLASTGameNode<
        Self: BLASTGameNode<Self, U, D, A, P, GA>,
        U: PARTUnit<U, D, A, P>, D : ExprState, A : StmtAction, P : Prec,
        GA
        > {
    /**
     * Returns the unit which this node corresponds to, if it originates from a unit
     * (generally, this is true exactly for the state nodes), or null otherwise.
     */
    fun getOriginUnit(): U? = null

    /**
     * Must be true only for nodes directly corresponding to a PART Unit (i.e. getOriginUnit() != null)
     * If true, then an expression can be computed using computeNumericRefinement, whose knowledge would make
     * the numerical bounds tighter.
     */
    fun isRefinable(
        L: Map<Self, Double>,
        LStrategy: Map<Self, GA>,
        U: Map<Self, Double>,
        UStrategy: Map<Self, GA>,
        tolerance: Double
    ): Boolean = false

    /**
     * Returns an expression whose knowledge would make the value bounds tighter.
     * Only computes the relevant expression, does not change the node or the related unit.
     * Might throw an exception if isRefinable() is false.
     */
    fun computeNumericRefinement(
        L: Map<Self, Double>,
        LStrategy: Map<Self, GA>,
        U: Map<Self, Double>,
        UStrategy: Map<Self, GA>,
        tolerance: Double,
    ): Expr<BoolType> = throw UnsupportedOperationException("Non-refinable node")
}