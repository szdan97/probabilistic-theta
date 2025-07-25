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
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not
import hu.bme.mit.theta.core.utils.WpState
import hu.bme.mit.theta.prob.analysis.P_ABSTRACTION
import hu.bme.mit.theta.prob.analysis.P_CONCRETE
import hu.bme.mit.theta.probabilistic.*
import hu.bme.mit.theta.probabilistic.gamesolvers.SGSolutionInitializer
import hu.bme.mit.theta.probabilistic.gamesolvers.VISolver
import java.util.*

interface BLASTGameNode<
        Self: BLASTGameNode<Self,U,D,A,P,GA>,
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

class BLASTChecker<U : PARTUnit<U, D, A, P>, D : ExprState, A : StmtAction, P : Prec,
        GameNode: BLASTGameNode<GameNode, U, D, A, P, GameAction>, GameAction>(
    val concreteInit: Valuation,
    val initFunc: InitFunc<D, P>,
    val createUnit: (state: D, supportPrec: P) -> U,
    val targetExpr: Expr<BoolType>,
    val maySatisfy: (D, Expr<BoolType>) -> Boolean,
    val refute: (D, Expr<BoolType>) -> Expr<BoolType>,
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
    ) = concretizeOrRefineOriginal(trace, toBlockAtLast, root)

    private fun keepSubtree(pivotNode: ProjectedStateNode<D, A, P>): Boolean = false

    data class RefinementResult<D : ExprState, A : StmtAction, P : Prec>(
        val concretizable: Boolean,
        val unmarkedNodes: List<ProjectedStateNode<D, A, P>>,
        val removedNodes: List<ProjectedStateNode<D, A, P>>,
        val logicalPivotNode: ProjectedStateNode<D,A,P>?
    )

    private fun concretizeOrRefineOriginal(trace: List<StateNodeProjectionEdge<D, A, P>>, toBlockAtLast: Expr<BoolType>, root: ProjectedStateNode<D,A,P>): RefinementResult<D, A, P> {
        // Direct implementation based on the algorithm of Henzinger et. al.: Lazy abstraction
        var badRegion = toBlockAtLast
        for (i in trace.indices.reversed()) {
            val currStateNode = trace[i].end
            val state = currStateNode.state
            if (maySatisfy(state, badRegion)) {
                badRegion = WpState.of(badRegion).wep(Stmts.SequenceStmt(trace[i].action.stmts)).expr
            } else {
                val pivotNode = trace[i].source
                val unmarkedNodes = arrayListOf<ProjectedStateNode<D, A, P>>()
                val removedNodes = arrayListOf<ProjectedStateNode<D, A, P>>()
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
                return RefinementResult(false, unmarkedNodes, removedNodes, pivotNode)
            }
        }
        val eval = badRegion.eval(concreteInit)
        if (!(eval as BoolLitExpr).value) {
            val pivotNode = root
            val unmarkedNodes = arrayListOf<ProjectedStateNode<D, A, P>>()
            val removedNodes = arrayListOf<ProjectedStateNode<D, A, P>>()
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
            return RefinementResult(false, unmarkedNodes, removedNodes, pivotNode)
        }
        // The trace is concretizable
        return RefinementResult(true, listOf(), listOf(), null)
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
        require(initStates.size == 1) { "Only a single abstract init state is supported for now" }
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
        explore(root, hashSetOf(root), q)
        return root
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
        while (true) {
            // Exploration + Logical refinement
            val reachedSet = hashSetOf(root)
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

            q.addAll(refinementResult.unmarkedNodes.map { it.origin as U })
            q.removeAll(removedUnits)
            reachedSet.removeAll(removedUnits)
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

