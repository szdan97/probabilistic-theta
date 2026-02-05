package hu.bme.mit.theta.prob.analysis.uniflazy

import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType

interface PARTBuildingConfiguration<
        S: ExprState, A: StmtAction, P: Prec, R, L,
        GN: UnitGameNode<GA>, GA
        > {
    fun close(u: PARTUnit<S, A, P, R, L, GN, GA>, reachedSet: Set<PARTUnit<S, A, P, R, L, GN, GA>>)
    fun concretizeOrRefine(
        trace: PARTTrace<S, A, P, R, L, GN, GA>,
        initialAssertion: Expr<BoolType>,
        finalAssertion: Expr<BoolType>
    ): RefinementResult<S, A, P, GN, GA>
}

sealed class RefinementResult<
        S: ExprState, A: Action, P: Prec,
        GN: UnitGameNode<GA>, GA
        > {
    class Concretizable<S: ExprState, A: Action, P: Prec, GN: UnitGameNode<GA>, GA>: RefinementResult<S, A, P, GN, GA>()
    class Spurious<S: ExprState, A: StmtAction, P: Prec, R, L, GN: UnitGameNode<GA>, GA>(val pivotUnit: PARTUnit<S, A, P, R, L, GN, GA>): RefinementResult<S, A, P, GN, GA>()
}