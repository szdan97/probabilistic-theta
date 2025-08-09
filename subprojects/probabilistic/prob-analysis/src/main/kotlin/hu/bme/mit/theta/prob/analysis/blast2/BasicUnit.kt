package hu.bme.mit.theta.prob.analysis.blast2

import hu.bme.mit.theta.analysis.PartialOrd
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.probabilistic.Goal

abstract class BasicUnit<Self : BasicUnit<Self, D, A, P>, D : ExprState, A : StmtAction, P : Prec>(
    var stateLabel: D,
    var supportPrec: P,
    val partialOrder: PartialOrd<D>
) : PARTUnit<Self, D, A, P> {
    protected var fullyExpanded = false
    protected var coveringUnit: Self? = null
    protected val coveredUnits = arrayListOf<Self>()
    protected var mayTarget = false
    protected var mustTarget = false
    companion object { var nextId = 0}
    private val _id = nextId++

    override fun getId() = _id

    override fun toString(): String {
        return "Unit[$_id](${getState()} | ${getSupportPrecision()})"
    }

    override fun getState(): D = stateLabel

    override fun isExpanded() = fullyExpanded

    override fun canCover(unitToCover: Self) =
        unitToCover != this && !this.isCovered() &&
//                unitToCover.getState() == this.getState() && // TODO: remove
                partialOrder.isLeq(unitToCover.getState(), this.getState())

    override fun refineSupportPrecision(newPrecision: P) {
        supportPrec = newPrecision
    }

    override fun getCoverer() = coveringUnit

    override fun getCoveredUnits(): List<Self> = coveredUnits

    override fun coverWith(coveringUnit: Self) {
        this.coveringUnit = coveringUnit
        //TODO: the cast is ugly, but even self-bounded types seem to not be enough here
        coveringUnit.coveredUnits.add(this as Self)
    }

    override fun removeCover() {
        coveringUnit?.coveredUnits?.remove(this)
        coveringUnit = null
    }

    override fun markAsMayBeTarget() {
        mayTarget = true
    }

    override fun mayBeTarget() = mayTarget

    override fun markAsMustBeTarget() {
        mustTarget = true
    }

    override fun mustBeTarget() = mustTarget

    override fun getSupportPrecision() = supportPrec

    override fun removeSubtree(): RemovedAndUnmarkedNodes<Self> {
        val unmarkedUnits = hashSetOf<Self>()
        val removedUnits = hashSetOf<Self>()
        removeSubtreeHelper(removedUnits = removedUnits, unmarkedUnits =  unmarkedUnits)
        return RemovedAndUnmarkedNodes(removedNodes = removedUnits, unmarkedNodes = unmarkedUnits)
    }

    protected fun removeSubtreeHelper(
        removedUnits: MutableCollection<Self>,
        unmarkedUnits: MutableCollection<Self>
    ) {
        for ((_, successor) in getSuccessorUnits()) {
            successor.removeSubtreeHelper(removedUnits = removedUnits, unmarkedUnits = unmarkedUnits)
            removedUnits.add(successor)
            unmarkedUnits.remove(successor)
            successor.removeCover()
            successor.coveredUnits.toList().forEach {
                it.removeCover()
                if(it !in removedUnits) unmarkedUnits.add(it)
            }
        }
        clearIntermediateNodes()
        fullyExpanded = false
        unmarkedUnits.add(this as Self)
    }

    protected abstract fun clearIntermediateNodes()

    override fun refineState(newState: D): RemovedAndUnmarkedNodes<Self> {
        stateLabel = newState
        val removedUnits = hashSetOf<Self>()
        val unmarkedNodes = hashSetOf<Self>()
        for (coveredUnit in coveredUnits) {
            if (!canCover(coveredUnit)) {
                coveredUnit.removeCover()
                unmarkedNodes.add(coveredUnit)
            }
        }
        val cleanUpResult = cleanUpSuccessors()
        removedUnits.addAll(cleanUpResult.removedNodes)
        unmarkedNodes.addAll(cleanUpResult.unmarkedNodes)
        return RemovedAndUnmarkedNodes(removedUnits, unmarkedNodes)
        // TODO: for now, we do not directly reexpand or relabel here. The current BLAST implementation is compatible with this
        //  decision, especially as it never uses refineState().
    }

    abstract fun cleanUpSuccessors(): RemovedAndUnmarkedNodes<Self>

    fun isTarget(originalGoal: Goal, abstractionGoal: Goal) =
        (mustBeTarget()
                || (mayBeTarget() && abstractionGoal == Goal.MAX))
}