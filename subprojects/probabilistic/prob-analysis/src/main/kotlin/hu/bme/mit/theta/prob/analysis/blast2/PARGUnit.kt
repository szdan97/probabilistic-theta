package hu.bme.mit.theta.prob.analysis.blast2

import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType

interface PARGUnit<Self : PARGUnit<Self, D, A, P>, D : ExprState, A : StmtAction, P : Prec> {
    fun getSupportPrecision(): P
    fun getState(): D
    fun expand(prec: P): Collection<Self>
    fun isExpanded(): Boolean
    fun isComplete() = isExpanded() || isCovered()

    /**
     * Returns the successor units that have already been created. If called before any expansion, the result will be empty.
     * Might be partial, if called during expansion or after removing only some successors.
     */
    fun getSuccessorUnits(): Collection<Pair<Pair<Expr<BoolType>, A>, Self>>

    fun canCover(unitToCover: Self): Boolean

    /**
     * Refinement might make formerly covered nodes non-covered, so there might be new unlabeled nodes.
     * Depending on the exact implementation, some nodes might be removed by state refinement
     * (e.g. when some command becomes universally disabled with the finer state).
     * These are collected in the result.
     */
    fun refineState(newState: D): RemovedAndUnlabeledNodes<Self>
    fun refineSupportPrecision(newPrecision: P)
    fun getCoverer(): Self?
    fun getCoveredUnits(): List<Self>
    fun isCovered() = getCoverer() != null
    fun ifCovered(then: (Self) -> Unit) = getCoverer()?.let(then)
    fun coverWith(coveringNode: Self)
    fun removeCover()

    fun markAsTarget()
    fun isTarget(): Boolean

    // fun remove()
    fun removeSubtree(): RemovedAndUnlabeledNodes<Self>

    fun stateNodeProjection(): ProjectedStateNode<D, A, P> = ProjectedStateNode(this)
}

