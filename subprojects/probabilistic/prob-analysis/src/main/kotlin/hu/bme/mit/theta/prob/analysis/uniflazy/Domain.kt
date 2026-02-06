package hu.bme.mit.theta.prob.analysis.uniflazy

import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.analysis.PartialOrd
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.TransFunc
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.prob.analysis.ProbabilisticCommand
import hu.bme.mit.theta.prob.analysis.linkedtransfuncs.LinkedTransFunc

open class Domain<S: ExprState, A: Action, P: Prec, R, L>(
    val stateOrd: PartialOrd<S>, // Pre-order to be precise
    val extendPrec: (P, Expr<BoolType>) -> P, // TODO: decide between OOP and functional
    val refineState: (S, R) -> S,
    val abstractFromValuation: (Valuation, L, P) -> S,
    val abstractFromExpr: (Expr<BoolType>, L, P) -> S,
    val extractStructure: (S) -> L, // Not part of the theoretical description as it is necessary only for structural info
    val transFunc: TransFunc<S, in A, in P>,
    val linkedTransFunc: LinkedTransFunc<S, A, P>,
    val maySats: (S, Expr<BoolType>) -> Boolean,
    val mustSats: (S, Expr<BoolType>) -> Boolean,
    val getGuardSatisfactionConfigs: (S, List<ProbabilisticCommand<A>>) -> List<List<ProbabilisticCommand<A>>>
) {
    // Precision preorder is only used in the theory, not needed in the implementation
    // Bot and Top are not used explicitly in the implementation
    // Gamma is not used explicitly in the implementation
    // toExpr is already present in ExprState
}