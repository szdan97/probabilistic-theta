package hu.bme.mit.theta.prob.analysis.menuabstraction

import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.prob.analysis.P_CONCRETE
import hu.bme.mit.theta.probabilistic.AnalysisTask
import hu.bme.mit.theta.probabilistic.Goal
import hu.bme.mit.theta.probabilistic.StochasticGameSolver
import hu.bme.mit.theta.probabilistic.gamesolvers.initializers.TargetSetLowerInitializer

class MenuGameCegarChecker<S : ExprState, A : StmtAction, P : Prec>(
    val abstractor: MenuGameAbstractor<S, A, P>,
    val refiner: MenuGameRefiner<S, A, P, *>,
    val gameSolver: StochasticGameSolver<
            MenuGameNode<S, A>,
            MenuGameAction<S, A>
            >
) {
    data class MenuGameCheckerResult<S : ExprState, A : StmtAction, P : Prec>(
        val finalPrec: P,
        val finalLowerInitValue: Double,
        val finalUpperInitValue: Double
    )

    fun check(initPrec: P, goal: Goal, threshold: Double): MenuGameCheckerResult<S, A ,P> {
        var currPrec = initPrec
        val lowerInitializer = TargetSetLowerInitializer<MenuGameNode<S, A>, MenuGameAction<S, A>> {
            it is MenuGameNode.StateNode && it.minReward == 1
        }
        val upperInitializer = TargetSetLowerInitializer<MenuGameNode<S, A>, MenuGameAction<S, A>> {
            it is MenuGameNode.StateNode && it.minReward == 1
        }
        while (true) {
            val abstraction = abstractor.computeAbstraction(currPrec)
            val game = abstraction.game
            println("All nodes: ${game.getAllNodes().size}")
            println("State nodes: ${game.getAllNodes().filterIsInstance<MenuGameNode.StateNode<*,*>>().size}")
            println("Result nodes: ${game.getAllNodes().filterIsInstance<MenuGameNode.ResultNode<*,*>>().size}")
            val lowerAnalysisTask = AnalysisTask(game, { if (it == P_CONCRETE) goal else Goal.MIN }, abstraction.rewardMax)
            val upperAnalysisTask = AnalysisTask(game, { if (it == P_CONCRETE) goal else Goal.MAX }, abstraction.rewardMin)
            val upperValues = gameSolver.solveWithStrategy(upperAnalysisTask, lowerInitializer)
            val lowerValues = gameSolver.solveWithStrategy(lowerAnalysisTask, upperInitializer)
            println("[${lowerValues.first[game.initialNode]}, ${upperValues.first[game.initialNode]}]")
            if (upperValues.first[game.initialNode]!! - lowerValues.first[game.initialNode]!! < threshold) {
                return MenuGameCheckerResult(
                    currPrec,
                    lowerValues.first[game.initialNode]!!,
                    upperValues.first[game.initialNode]!!
                )
            }
            val nextPrec = refiner.refine(
                game,
                upperValues.first,
                lowerValues.first,
                upperValues.second,
                lowerValues.second,
                currPrec
            ).newPrec
            require(nextPrec != currPrec)
            currPrec = nextPrec
            println("New Precision: $currPrec")
        }
    }

}