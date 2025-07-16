package hu.bme.mit.theta.prob.analysis.blast2

import hu.bme.mit.theta.analysis.InitFunc
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.stmt.Stmts
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.WpState
import hu.bme.mit.theta.probabilistic.Goal
import java.util.*

class BLASTChecker<U : PARGUnit<U, D, A, P>, D : ExprState, A : StmtAction, P : Prec>(
    //val concreteInitExpr: Expr<BoolType>,
    val concreteInit: Valuation,
    val initFunc: InitFunc<D, P>,
    val createUnit: (state: D, supportPrec: P) -> U,
    val targetExpr: Expr<BoolType>,
    val maySatisfy: (D, Expr<BoolType>) -> Boolean,
 //   val createTraceChecker: (init: Expr<BoolType>, target: Expr<BoolType>) -> ExprTraceChecker<ItpRefutation>,
    val refute: (D, Expr<BoolType>) -> Expr<BoolType>,
    val refuteConcrete: (Valuation, Expr<BoolType>) -> Expr<BoolType>,
    val refinePrec: (currentPrec: P, refutation: Expr<BoolType>) -> P
) {
    fun isTarget(s: D) = maySatisfy(s, targetExpr)

    private fun close(unit: U, reachedUnits: Collection<U>) {
        if (unit.isCovered()) return //TODO: should this be a throw instead?
        for (potentialCoverer in reachedUnits) {
            if (potentialCoverer.canCover(unit)) {
                unit.coverWith(potentialCoverer)
                return
            }
        }
    }

    private fun processNonTargetUnit(unit: U, reachedUnits: Collection<U>) {
        if (unit.isComplete()) return //TODO: should this be a throw instead?
        close(unit, reachedUnits)
        if (unit.isCovered()) return
        unit.expand(unit.getSupportPrecision())
    }

    data class UnitProcessingResult<U>(
        val unmarkedUnits: List<U>,
        val removedUnits: List<U>
    )
    private fun processTargetUnit(targetUnit: U, rootUnit: U): UnitProcessingResult<U> {
        val stateNodeProjection = createFullStateNodeProjection(rootUnit)
        val targetTrace = stateNodeProjection[targetUnit]!!.getTraceFromRoot()
        if (targetTrace.isEmpty()) {
            TODO("corner case: target==root")
        } else {
            val res = concretizeOrRefine(targetTrace)
            return UnitProcessingResult(
                res.unmarkedNodes.map { it.origin as U }, //TODO: add U as a type param of the projected node
                res.removedNodes.map {it.origin as U}
            )
        }
        // TODO: should we constantly maintain a state node projection instead of building it from scratch here?
    }


    private fun concretizeOrRefine(trace: List<StateNodeProjectionEdge<D, A, P>>) = concretizeOrRefineOriginal(trace)

    private fun keepSubtree(pivotNode: ProjectedStateNode<D, A, P>): Boolean = false

    data class RefinementResult<D: ExprState, A: StmtAction, P: Prec>(
        val concretizable: Boolean,
        val unmarkedNodes: List<ProjectedStateNode<D,A,P>>,
        val removedNodes: List<ProjectedStateNode<D,A,P>>
    )
    private fun concretizeOrRefineOriginal(trace: List<StateNodeProjectionEdge<D, A, P>>): RefinementResult<D,A,P> {
        // Direct implementation based on the algorithm of Henzinger et. al.: Lazy abstraction
        var badRegion = targetExpr
        for (i in trace.indices.reversed()) {
            val currStateNode = trace[i].end
            val state = currStateNode.state
            if (maySatisfy(state, badRegion)) {
                badRegion = WpState.of(badRegion).wep(Stmts.SequenceStmt(trace[i].action.stmts)).expr
            } else {
                val pivotNode = trace[i].source
                val unmarkedNodes = arrayListOf<ProjectedStateNode<D,A,P>>()
                val removedNodes = arrayListOf<ProjectedStateNode<D,A,P>>()
                if (keepSubtree(pivotNode)) {
                    TODO("relabel subtree?")
                } else {
                    val res = pivotNode.removeSubtree()
                    unmarkedNodes.addAll(res.unmarkedNodes)
                    removedNodes.addAll(res.removedNodes)
                    val refutation = refute(state, badRegion)
                    val newPrec = refinePrec(pivotNode.origin.getSupportPrecision(), refutation)
                    pivotNode.origin.refineSupportPrecision(newPrec)
                }
                return RefinementResult(false, unmarkedNodes, removedNodes)
            }
        }
        val eval = badRegion.eval(concreteInit)
        if(!(eval as BoolLitExpr).value) {
            val pivotNode = trace.first().source // the root
            val unmarkedNodes = arrayListOf<ProjectedStateNode<D,A,P>>()
            val removedNodes = arrayListOf<ProjectedStateNode<D,A,P>>()
            if (keepSubtree(pivotNode)) {
                TODO("relabel subtree?")
            } else {
                val res = pivotNode.removeSubtree()
                unmarkedNodes.addAll(res.unmarkedNodes)
                removedNodes.addAll(res.removedNodes)
                val refutation = refuteConcrete(concreteInit, badRegion)
                val newPrec = refinePrec(pivotNode.origin.getSupportPrecision(), refutation)
                pivotNode.origin.refineSupportPrecision(newPrec)
                pivotNode.origin.refineState(getInitState(newPrec))
            }
            // maybe a reinit function would make more sense later
            return RefinementResult(false, unmarkedNodes, removedNodes)
        }
        return RefinementResult(true, listOf(), listOf())
        // If the loop did not break, then the trace is concretizable, we just leave the target node there
    }

    /*
    private val logicalTraceChecker = createTraceChecker(concreteInitExpr, targetExpr)
    private fun concretizeOrRefineDelegated(
        trace: List<StateNodeProjectionEdge<D,A,P>>
    ) {
        val states = listOf(trace.first().source.state) + trace.map { it.end.state }
        val transformedTrace = Trace.of(
            states, trace.map { it.action }
        )
        val traceStatus = logicalTraceChecker.check(transformedTrace)
        if(traceStatus.isFeasible) {
            // TODO: should we do anything here?
        } else {
            val itpRef = traceStatus.asInfeasible().refutation
            refToPrec.toPrec(itpRef)
            TODO("refine")
        }
    }
     */

    private fun explore(rootUnit: U, reachedSet: MutableCollection<U>, q: ArrayDeque<U>) {
        while (q.isNotEmpty()) {
            val currUnit = q.pop()
            if (isTarget(currUnit.getState())) {
                currUnit.markAsTarget()
                val processResult = processTargetUnit(currUnit, rootUnit)
                val removedUnits = processResult.removedUnits.toSet()
                reachedSet.removeAll(removedUnits)
                q.removeAll(removedUnits)
                q.addAll(processResult.unmarkedUnits.toSet())
                // TODO: should target checking and logical refinement be performed when processing a node or when it is found?
            } else {
                processNonTargetUnit(currUnit, reachedSet)
                q.addAll(currUnit.getSuccessorUnits().map { it.second })
                reachedSet.addAll(currUnit.getSuccessorUnits().map { it.second })
            }
        }
    }

    fun getInitState(prec: P): D {
        val initStates = initFunc.getInitStates(prec)
        require(initStates.size == 1) { "Only a single abstract init state is supported for now"}
        val initState = initStates.first()
        return initState
    }

    fun doInitialExploration(
        initPrec: P
    ): U {
        val initState = getInitState(initPrec)
        val root = createUnit(initState, initPrec)
        val q = ArrayDeque<U>()
        q.add(root)
        explore(root,  hashSetOf(root), q)
        return root
    }

    fun check(
        initPrec: P, goal: Goal, threshold: Double
    ) {
        val initState = getInitState(initPrec)
        val root = createUnit(initState, initPrec)
        val q = ArrayDeque<U>()
        q.add(root)
        explore(root,  hashSetOf(root), q)
        TODO("numeric analysis")
        TODO("numeric refinement")
    }
}

