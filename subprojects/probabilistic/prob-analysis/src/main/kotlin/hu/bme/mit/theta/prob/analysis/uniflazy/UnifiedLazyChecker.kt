package hu.bme.mit.theta.prob.analysis.uniflazy

import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.prob.analysis.P_ABSTRACTION
import hu.bme.mit.theta.prob.analysis.P_CONCRETE
import hu.bme.mit.theta.prob.analysis.ProbabilisticCommandLTS
import hu.bme.mit.theta.probabilistic.*
import hu.bme.mit.theta.probabilistic.gamesolvers.initializers.TargetSetLowerInitializer

class UnifiedLazyChecker<S : ExprState, A : StmtAction, P : Prec, R, L,
        GN : UnitGameNode<GA> /* Game Node type */, GA /* Game Action type */
        >(
    val domain: Domain<S, A, P, R, L>,
    val createUnit: (state: S, supportPrec: P, PART: PART<S,A,P,R,L, GN, GA>) -> PARTUnit<S, A, P, R, L, GN, GA>,
    val buildingConfiguration: PARTBuildingConfiguration<S, A, P, R, L, GN, GA>,
    val gameSolver: StochasticGameSolver<GN, GA>,

    /**
     * Select the numerical pivot unit based on value and strategy information.
     * The selected unit must be numerically refinable
     * (i.e., result.isNumericRefinable() == true)
     */
    val pivotSelectionStrategy: (
        units: Set<PARTUnit<S, A, P, R, L, GN, GA>>,
        unitToNodeMap: Map<PARTUnit<S, A, P, R, L, GN, GA>, GN>,
        L: Map<GN, Double>,
        LStrategy: Map<GN, GA>,
        U: Map<GN, Double>,
        UStrategy: Map<GN, GA>
            ) -> PARTUnit<S, A, P, R, L, GN, GA>
) {
    fun check(
        lts: ProbabilisticCommandLTS<S, A>,
        initExpr: Expr<BoolType>,
        initStructure: L,
        initPrec: P,
        targetExpr: Expr<BoolType>,
        goal: Goal,
        threshold: Double = 1e-6
    ): Pair<Double, Double> {
        val part = PART(
            createUnit,
            targetExpr,
            initStructure,
            initExpr,
            initPrec,
            lts,
            domain,
            buildingConfiguration
        )
        val root = part.root
        while (true) {
            part.explorePART()
            val (game, unitToNodeMap) = part.toGame()

            val isUpperTarget = { n: GN -> false }
            val upperRewardFunc = TargetRewardFunction<GN, GA>(isUpperTarget)
            val upperAnalysisTask = AnalysisTask(
                game, setGoal(P_CONCRETE to goal, P_ABSTRACTION to Goal.MAX), upperRewardFunc
            )
            val upperInitializer = TargetSetLowerInitializer<GN, GA>(isUpperTarget)
            val (upperValues, upperStrat) = gameSolver.solveWithStrategy(upperAnalysisTask, upperInitializer)

            val isLowerTarget = {n: GN -> false}
            val lowerRewardFunc = TargetRewardFunction<GN, GA>(isLowerTarget)
            val lowerInitializer = TargetSetLowerInitializer<GN, GA>(isLowerTarget)
            val lowerAnalysisTask = AnalysisTask(
                game, setGoal(P_CONCRETE to goal, P_ABSTRACTION to Goal.MAX), lowerRewardFunc
            )
            val (lowerValues, lowerStrat) = gameSolver.solveWithStrategy(lowerAnalysisTask, lowerInitializer)

            val diff = upperValues[game.initialNode]!! - lowerValues[game.initialNode]!!
            if (diff < threshold) {
                return Pair(lowerValues[game.initialNode]!!, upperValues[game.initialNode]!!)
            }

            // Making sure that the unit is numRefinable is currently the
            // responsibility of the pivotSelectionStrategy (no pre-filtering).
            // This is more error-prone, but can be more efficient than pre-filtering.
            val numericalPivot = pivotSelectionStrategy(
                part.reached,
                unitToNodeMap,
                lowerValues,
                lowerStrat,
                upperValues,
                upperStrat
            )
            val refinementExpr = numericalPivot.computeNumericRefinement(
                lowerValues,
                lowerStrat,
                upperValues,
                upperStrat,
                threshold
            )
            val trace = numericalPivot.getTraceFromRoot()
            var refinementResult = buildingConfiguration.concretizeOrRefine(
                trace, initExpr, refinementExpr
            )
            if(refinementResult is RefinementResult.Concretizable)
                refinementResult = buildingConfiguration.concretizeOrRefine(
                    trace, initExpr, Not(refinementExpr)
                )
        }
    }
}