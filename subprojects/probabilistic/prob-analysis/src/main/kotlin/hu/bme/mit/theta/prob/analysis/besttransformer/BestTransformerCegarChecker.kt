package hu.bme.mit.theta.prob.analysis.besttransformer

import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.prob.analysis.P_CONCRETE
import hu.bme.mit.theta.prob.analysis.besttransformer.BestTransformerAbstractor.BestTransformerGameAction
import hu.bme.mit.theta.prob.analysis.besttransformer.BestTransformerAbstractor.BestTransformerGameNode
import hu.bme.mit.theta.probabilistic.AnalysisTask
import hu.bme.mit.theta.probabilistic.Goal
import hu.bme.mit.theta.probabilistic.StochasticGameSolver
import hu.bme.mit.theta.probabilistic.gamesolvers.initializers.TargetSetLowerInitializer

class BestTransformerCegarChecker<S : ExprState, A : StmtAction, P : Prec>(
    val abstractor: BestTransformerAbstractor<S, A, P>,
    val refiner: BestTransformerRefiner<S, A, P, *>,
    val gameSolver: StochasticGameSolver<
            BestTransformerGameNode<S, A>,
            BestTransformerGameAction<S, A>
            >
) {
    data class BestTransformerCheckerResult<S : ExprState, A : StmtAction, P : Prec>(
        val finalPrec: P,
        val finalLowerInitValue: Double,
        val finalUpperInitValue: Double
    )

    fun check(initPrec: P, goal: Goal, threshold: Double): BestTransformerCheckerResult<S, A ,P> {
        var currPrec = initPrec
        val lowerInitializer = TargetSetLowerInitializer<BestTransformerGameNode<S, A>, BestTransformerGameAction<S, A>> {
            it is BestTransformerGameNode.AbstractionChoiceNode && it.minReward == 1
        }
        val upperInitializer = TargetSetLowerInitializer<BestTransformerGameNode<S, A>, BestTransformerGameAction<S, A>> {
            it is BestTransformerGameNode.AbstractionChoiceNode && it.maxReward == 1
        }
        while (true) {
            val abstraction = abstractor.computeAbstraction(currPrec)
            val game = abstraction.game
            println("All nodes: ${game.getAllNodes().size}")
            println("A-nodes: ${game.getAllNodes().filterIsInstance<BestTransformerGameNode.AbstractionChoiceNode<*,*>>().size}")
            println("C-nodes: ${game.getAllNodes().filterIsInstance<BestTransformerGameNode.ConcreteChoiceNode<*,*>>().size}")
            val lowerAnalysisTask = AnalysisTask(game, { if (it == P_CONCRETE) goal else Goal.MIN }, abstraction.rewardMin)
            val upperAnalysisTask = AnalysisTask(game, { if (it == P_CONCRETE) goal else Goal.MAX }, abstraction.rewardMax)
            val (lowerValues, lowerStrat) = gameSolver.solveWithStrategy(lowerAnalysisTask, lowerInitializer)
            val (upperValues, upperStrat) = gameSolver.solveWithStrategy(upperAnalysisTask, upperInitializer)
            println("[${lowerValues[game.initialNode]}, ${upperValues[game.initialNode]}]")
            if (upperValues[game.initialNode]!! - lowerValues[game.initialNode]!! < threshold) {
                return BestTransformerCheckerResult(
                    currPrec,
                    lowerValues[game.initialNode]!!,
                    upperValues[game.initialNode]!!
                )
            }
            val nextPrec = refiner.refine(game, upperValues, lowerValues, upperStrat, lowerStrat, currPrec).newPrec
            require(nextPrec != currPrec)
            currPrec = nextPrec
            println("New Precision: $currPrec")
        }
    }

}