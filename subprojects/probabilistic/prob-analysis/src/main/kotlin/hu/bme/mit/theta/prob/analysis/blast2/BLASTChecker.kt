package hu.bme.mit.theta.prob.analysis.blast2

import hu.bme.mit.theta.analysis.InitFunc
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceBwBinItpChecker
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not
import hu.bme.mit.theta.prob.analysis.P_ABSTRACTION
import hu.bme.mit.theta.prob.analysis.P_CONCRETE
import hu.bme.mit.theta.probabilistic.*
import hu.bme.mit.theta.probabilistic.gamesolvers.SGSolutionInitializer
import hu.bme.mit.theta.probabilistic.gamesolvers.VISolver
import hu.bme.mit.theta.solver.ItpSolver
import java.util.*

class BLASTChecker<U : PARTUnit<U, D, A, P>, D : ExprState, A : StmtAction, P : Prec,
        GameNode: BLASTGameNode<GameNode, U, D, A, P, GameAction>, GameAction>(
    val concreteInit: Valuation,
    val initFunc: InitFunc<D, P>,
    val createUnit: (state: D, supportPrec: P) -> U,
    val targetExpr: Expr<BoolType>,
    val maySatisfy: (D, Expr<BoolType>) -> Boolean,
    //val refute: (D, Expr<BoolType>) -> Expr<BoolType>,
    val itpSolver: ItpSolver,
    val refuteConcrete: (Valuation, Expr<BoolType>) -> Expr<BoolType>,
    val refinePrec: (currentPrec: P, refutation: Expr<BoolType>) -> P,
    val rootUnitToGame: (U) -> StochasticGame<GameNode, GameAction>,
    val gameSolver: StochasticGameSolver<GameNode, GameAction> = VISolver(1e-6),
    val lowerRewardFunction: GameRewardFunction<GameNode, GameAction>,
    val upperRewardFunction: GameRewardFunction<GameNode, GameAction>,
    /**
     * Initializer used when P_A wants to minimize
     */
    val lowerGameInitilizer: SGSolutionInitializer<GameNode, GameAction>,
    /**
     * Initialize used when P_A wants to maximize
     */
    val upperGameInitilizer: SGSolutionInitializer<GameNode, GameAction>
) {
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
        val res = concretizeOrRefine(targetTrace, targetExpr, stateNodeProjection[rootUnit]!!)
        require(res.concretizable || res.removedNodes.isNotEmpty())
        //if(!res.concretizable) println("Logical pivot: ${res.logicalPivotNode!!.origin.getId()}")
        return UnitProcessingResult(
            res.unmarkedNodes.map { it.origin as U }, //TODO: add U as a type param of the projected node
            res.removedNodes.map { it.origin as U }
            )
        // TODO: should we constantly maintain a state node projection instead of building it from scratch here?
    }


    private fun concretizeOrRefine(
        trace: List<StateNodeProjectionEdge<D, A, P>>,
        toBlockAtLast: Expr<BoolType>,
        root: ProjectedStateNode<D, A, P>
    ) = concretizeOrRefineBwBinITP(trace, toBlockAtLast, root)

    private fun keepSubtree(pivotNode: ProjectedStateNode<D, A, P>): Boolean = false

    data class RefinementResult<D : ExprState, A : StmtAction, P : Prec>(
        val concretizable: Boolean,
        val unmarkedNodes: List<ProjectedStateNode<D, A, P>>,
        val removedNodes: List<ProjectedStateNode<D, A, P>>,
        val logicalPivotNode: ProjectedStateNode<D,A,P>?
    ) {
        companion object {
            fun <D : ExprState, A : StmtAction, P : Prec> Feasible() =
                RefinementResult<D, A, P>(true, listOf(), listOf(), null)
        }
    }
    private fun concretizeOrRefineBwBinITP(trace: List<StateNodeProjectionEdge<D, A, P>>, toBlockAtLast: Expr<BoolType>, root: ProjectedStateNode<D,A,P>): RefinementResult<D, A, P> {
        val traceRefiner = ExprTraceBwBinItpChecker.create(concreteInit.toExpr(), toBlockAtLast, itpSolver)
        val nodes = arrayListOf(root)
        for (edge in trace) {
            nodes.add(edge.end)
        }
        val states = nodes.map { it.state }
        val transformedTrace = Trace.of(states, trace.map { it.action })
        val refRes = traceRefiner.check(transformedTrace)
        if(refRes.isFeasible) {
            return RefinementResult.Feasible()
        }
        val refutation = refRes.asInfeasible().refutation.toList()
        val refutationIndex = refutation.indexOfFirst { !it.equals(BoolExprs.True()) }
        val refutationExpr = refutation[refutationIndex]
        val pivotIndex = refutationIndex - 1
        if(pivotIndex >= 0) { // No reinit needed, pruning + support prec change is enough
            val pivotNode = nodes[pivotIndex]
            val newPrec = refinePrec(pivotNode.supportPrecision, refutationExpr)
            pivotNode.origin.refineSupportPrecision(newPrec)
            val (removedNodes, unmarkedNodes) = pivotNode.removeSubtree()

            return RefinementResult(false, unmarkedNodes.toList(), removedNodes.toList(), pivotNode)
        }
        // Reinit needed: The init node must be a more precise abstraction of the concrete init state
        val pivotNode = root
        val (removedNodes, unmarkedNodes) = root.removeSubtree()
        val newPrec = refinePrec(pivotNode.supportPrecision, refutationExpr)
        root.origin.refineSupportPrecision(newPrec)
        root.origin.refineState(getInitState(newPrec))
        return RefinementResult(false, unmarkedNodes.toList(), removedNodes.toList(), pivotNode)
    }

    private fun explore(rootUnit: U, reachedSet: MutableCollection<U>, q: ArrayDeque<U>) {
        while (q.isNotEmpty()) {
            val currUnit = q.pop()
            if (maySatisfy(currUnit.getState(), targetExpr)) {
                currUnit.markAsMayBeTarget()
                if(!maySatisfy(currUnit.getState(), Not(targetExpr)))
                    currUnit.markAsMustBeTarget()
                val processResult = processTargetUnit(currUnit, rootUnit)
                val removedUnits = processResult.removedUnits.toSet()
                reachedSet.removeAll(removedUnits)
                q.removeAll(removedUnits)
                q.addAll(processResult.unmarkedUnits.toSet())
                //println("Logical Removed: ${removedUnits.map { it.getId() }}")
                //println("Added to q: ${processResult.unmarkedUnits.toSet().map { it.getId() }}")
                require(rootUnitToGame(rootUnit).getAllNodes().mapNotNull { it.getOriginUnit() }.toSet() == reachedSet.toSet())
                // TODO: should target checking and logical refinement be performed when processing a node or when it is found?
            } else {
                processNonTargetUnit(currUnit, reachedSet)
                val toAdd = currUnit.getSuccessorUnits().map { it.second }
                q.addAll(toAdd)
                reachedSet.addAll(toAdd)
                //println("Added to reached and q: ${toAdd.map { it.getId() }}")
                require(rootUnitToGame(rootUnit).getAllNodes().mapNotNull { it.getOriginUnit() }.toSet() == reachedSet.toSet())

            }
        }
        require(rootUnitToGame(rootUnit).getAllNodes().all { it.getOriginUnit()?.let { it.isComplete() || it.mustBeTarget() } ?: true })
    }

    fun getInitState(prec: P): D {
        val initStates = initFunc.getInitStates(prec)
        require(initStates.size == 1) { "Only a single abstract init state is supported for now" }
        val initState = initStates.first()
        return initState
    }

    fun check(
        initPrec: P, goal: Goal, threshold: Double,
        logAnalysis: (currGame: StochasticGame<GameNode, GameAction>,
                      L: Map<GameNode, Double>, U: Map<GameNode, Double>) -> Unit = { _,_,_ -> },
        logNumericRefinement: (currGame: StochasticGame<GameNode, GameAction>,
                               L: Map<GameNode, Double>, U: Map<GameNode, Double>,
                               numericPivot: GameNode, refinementExpression: Expr<BoolType>,
                               //logicalPivotUnit: U
                ) -> Unit = { _,_,_,_,_ -> }
    ): Pair<Double, StochasticGame<GameNode, GameAction>> {
        val initState = getInitState(initPrec)
        val root = createUnit(initState, initPrec)
        val q = ArrayDeque<U>()
        q.add(root)
        val reachedSet = hashSetOf(root)
        while (true) {
            // Exploration + Logical refinement
            explore(root, reachedSet, q)

            // Numeric Analysis
            val game = rootUnitToGame(root)
            val lowerAnalysisTask = AnalysisTask(
                game,
                setGoal(P_CONCRETE to goal, P_ABSTRACTION to Goal.MIN),
                lowerRewardFunction
            )
            val upperAnalysisTask = AnalysisTask(
                game,
                setGoal(P_CONCRETE to goal, P_ABSTRACTION to Goal.MAX),
                upperRewardFunction
            )
            val (L, LStrat) = gameSolver.solveWithStrategy(lowerAnalysisTask, lowerGameInitilizer)
            val (U, UStrat) = gameSolver.solveWithStrategy(upperAnalysisTask, upperGameInitilizer)
            logAnalysis(game, L, U)
            if (U[game.initialNode]!! - L[game.initialNode]!! < threshold)
                return (L[game.initialNode]!! + U[game.initialNode]!!) / 2 to game

            // Numeric refinement with propagation
            val projection = createFullStateNodeProjection(root)
            val pivotNode: GameNode = selectNumericPivotNode(game, L, LStrat, U, UStrat, threshold)
            val pivotUnit: U = pivotNode.getOriginUnit()
                ?: throw RuntimeException("Numeric pivot node must directly correspond to a unit")
            val trace = projection[pivotUnit]!!.getTraceFromRoot()
            val refinementExpr = pivotNode.computeNumericRefinement(L, LStrat, U, UStrat, threshold)
            logNumericRefinement(
                game, L, U, pivotNode, refinementExpr, //refinementResult.logicalPivotNode!!.origin as U
            )
            var refinementResult = concretizeOrRefine(trace, refinementExpr, projection[root]!!)
            if(refinementResult.concretizable) // Propagating both of them simultaneously might be a bit cheaper
                refinementResult = concretizeOrRefine(trace, Not(refinementExpr),  projection[root]!!)
            val removedUnits = refinementResult.removedNodes.map { it.origin }.toSet()

            val toAdd = refinementResult.unmarkedNodes.map { it.origin as U }
            q.addAll(toAdd)
            q.removeAll(removedUnits)
            reachedSet.removeAll(removedUnits)
            //println("Numeric pivot: ${pivotUnit.getId()}")
            //println("Logical pivot: ${refinementResult.logicalPivotNode!!.origin.getId()}")
            //println("Added to q: ${toAdd.map { it.getId() }}")
            //println("Numeric Removed: ${removedUnits.map { it.getId() }}")
        }
    }

    fun selectNumericPivotNode(
        game: StochasticGame<GameNode, GameAction>,
        L: Map<GameNode, Double>,
        LStrategy: Map<GameNode, GameAction>,
        U: Map<GameNode, Double>,
        UStrategy: Map<GameNode, GameAction>,
        tolerance: Double
    ): GameNode {
        val nodeToRefine = game.getAllNodes()
            .filter { it.isRefinable(L, LStrategy, U, UStrategy, tolerance) }
            .maxByOrNull { U[it]!!-L[it]!! } ?: throw IllegalArgumentException("No refinable node found")
        return nodeToRefine
    }
}

