package hu.bme.mit.theta.prob.analysis.blast2

import hu.bme.mit.theta.analysis.PartialOrd
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.StmtAction

abstract class BasicUnit<Self : BasicUnit<Self, D, A, P>, D : ExprState, A : StmtAction, P : Prec>(
    var stateLabel: D,
    var supportPrec: P,
    val partialOrder: PartialOrd<D>
) : PARGUnit<Self, D, A, P> {
    protected var fullyExpanded = false
    protected var coveringUnit: Self? = null
    protected val coveredUnits = arrayListOf<Self>()
    protected var target = false

    override fun toString(): String {
        return "Unit(${getState()} | ${getSupportPrecision()})"
    }

    override fun getState(): D = stateLabel

    override fun isExpanded() = fullyExpanded

    override fun canCover(unitToCover: Self) =
        unitToCover != this && !this.isCovered() && partialOrder.isLeq(unitToCover.getState(), this.getState())

    override fun refineSupportPrecision(newPrecision: P) {
        supportPrec = newPrecision
    }

    override fun getCoverer() = coveringUnit

    override fun getCoveredUnits(): List<Self> = coveredUnits

    override fun coverWith(coveringNode: Self) {
        coveringUnit = coveringNode
    }

    override fun removeCover() {
        coveringUnit = null
    }

    override fun markAsTarget() {
        target = true
    }

    override fun isTarget(): Boolean = target

    override fun getSupportPrecision() = supportPrec

    override fun removeSubtree(): RemovedAndUnlabeledNodes<Self> {
        val unmarkedUnits = hashSetOf<Self>()
        val removedUnits = hashSetOf<Self>()
        removeSubtreeHelper(removedUnits = removedUnits, unmarkedUnits =  unmarkedUnits)
        return RemovedAndUnlabeledNodes(removedNodes = removedUnits, unmarkedNodes = unmarkedUnits)
    }

    protected fun removeSubtreeHelper(
        removedUnits: MutableCollection<Self>,
        unmarkedUnits: MutableCollection<Self>
    ) {
        for ((_, successor) in getSuccessorUnits()) {
            successor.removeSubtreeHelper(removedUnits = removedUnits, unmarkedUnits = unmarkedUnits)
            removedUnits.add(successor)
            unmarkedUnits.remove(successor)
            successor.coveringUnit?.coveredUnits?.remove(successor)
            successor.coveredUnits.forEach {
                it.removeCover()
                unmarkedUnits.add(it)
            }
        }
        clearIntermediateNodes()
        fullyExpanded = false
        unmarkedUnits.add(this as Self)
    }

    protected abstract fun clearIntermediateNodes()

    override fun refineState(newState: D): RemovedAndUnlabeledNodes<Self> {
        stateLabel = newState
        val removedUnits = hashSetOf<Self>()
        val unlabeledUnits = hashSetOf<Self>()
        for (coveredUnit in coveredUnits) {
            if (!canCover(coveredUnit)) {
                coveredUnit.removeCover()
                unlabeledUnits.add(coveredUnit)
            }
        }
        return RemovedAndUnlabeledNodes(removedUnits, unlabeledUnits)
        // TODO: for now, we do not directly reexpand or relabel here. The current BLAST implementation is compatible with this
        //  decision, especially as it never uses refineState().
    }
}