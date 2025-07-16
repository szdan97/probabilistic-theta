package hu.bme.mit.theta.prob.analysis.menuabstraction

import hu.bme.mit.theta.analysis.InitFunc
import hu.bme.mit.theta.analysis.PartialOrd
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.prob.analysis.P_CONCRETE
import hu.bme.mit.theta.prob.analysis.ProbabilisticCommandLTS
import hu.bme.mit.theta.probabilistic.AnalysisTask
import hu.bme.mit.theta.probabilistic.Goal
import hu.bme.mit.theta.probabilistic.StochasticGameSolver
import hu.bme.mit.theta.probabilistic.gamesolvers.initializers.TargetSetLowerInitializer

class MenuGameBLASTChecker<S : ExprState, A : StmtAction, P : Prec>(
    val lts: ProbabilisticCommandLTS<S, A>,
    val init: InitFunc<S, P>,
    val transFunc: MenuGameTransFunc<S, A, P>,
    val targetExpr: Expr<BoolType>,
    val maySatisfy: (S, Expr<BoolType>) -> Boolean,
    val mustSatisfy: (S, Expr<BoolType>) -> Boolean,
    val ord: PartialOrd<S>,
    val refiner: MenuGameRefiner<S, A, P, *>,
    val extendPrec: P.(P) -> P,
    val gameSolver: StochasticGameSolver<
            MenuGameNode<S, A>,
            MenuGameAction<S, A>
            >
) {
    data class BLASTMenuGameCheckerResult<S : ExprState, A : StmtAction, P : Prec>(
        val finalLowerInitValue: Double,
        val finalUpperInitValue: Double,
        val finalSupportPrecs: Map<BLASTMenuGame<S, A, P>.BLASTMenuGameNode, P>
    )

    fun check(initPrec: P, goal: Goal, threshold: Double): BLASTMenuGameCheckerResult<S, A, P> {
        val game = BLASTMenuGame(
            lts,
            init,
            transFunc,
            targetExpr,
            maySatisfy,
            mustSatisfy,
            initPrec,
            ord,
            extendPrec
        )
        while (true) {
            game.fullyExplore()
            val rewardFunction = MenuGameLowerRewardFunc<S, A>()

            val lowerGoal: (Int) -> Goal = { if (it == P_CONCRETE) goal else Goal.MIN }
            //val lowerInitializer = GameAlmostSureTargetInitializer(game, lowerGoal, {rewardFunction(it) == 1.0} )
            val lowerAnalysisTask = AnalysisTask(game, lowerGoal, rewardFunction)

            val upperGoal: (Int) -> Goal = { if (it == P_CONCRETE) goal else Goal.MAX }
            //val upperInitializer = GameAlmostSureTargetInitializer(game, upperGoal, {rewardFunction(it) == 1.0} )
            val upperAnalysisTask = AnalysisTask(game, upperGoal, MenuGameUpperRewardFunc())

            val lowerInitializer = TargetSetLowerInitializer<MenuGameNode<S, A>, MenuGameAction<S, A>> {
                it is MenuGameNode.StateNode && it.minReward == 1
            }
            val upperInitializer = TargetSetLowerInitializer<MenuGameNode<S, A>, MenuGameAction<S, A>> {
                it is MenuGameNode.StateNode && it.minReward == 1
            }

            val lowerValues = gameSolver.solveWithStrategy(lowerAnalysisTask, lowerInitializer)
            val upperValues = gameSolver.solveWithStrategy(upperAnalysisTask, upperInitializer)
            println("[${lowerValues.first[game.initialNode]}, ${upperValues.first[game.initialNode]}]")
            if (upperValues.first[game.initialNode]!! - lowerValues.first[game.initialNode]!! < threshold) {
                return BLASTMenuGameCheckerResult(
                    lowerValues.first[game.initialNode]!!,
                    upperValues.first[game.initialNode]!!,
                    game.nodes.associateWith { it.supportPrecision }
                )
            }
            // As the support precision for a given state might be ambiguous, and the
            val refinementResult = refiner.refine(
                game,
                upperValues.first,
                lowerValues.first,
                upperValues.second,
                lowerValues.second,
                initPrec
            )
            game.refine(refinementResult)
        }
    }

}