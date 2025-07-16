package hu.bme.mit.theta.prob.analysis.besttransformer

import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.analysis.InitFunc
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.prob.analysis.P_ABSTRACTION
import hu.bme.mit.theta.prob.analysis.P_CONCRETE
import hu.bme.mit.theta.prob.analysis.ProbabilisticCommand
import hu.bme.mit.theta.prob.analysis.ProbabilisticCommandLTS
import hu.bme.mit.theta.prob.analysis.besttransformer.BestTransformerAbstractor.BestTransformerGameAction.AbstractionChoice
import hu.bme.mit.theta.prob.analysis.besttransformer.BestTransformerAbstractor.BestTransformerGameAction.ConcreteChoice
import hu.bme.mit.theta.prob.analysis.besttransformer.BestTransformerAbstractor.BestTransformerGameNode.AbstractionChoiceNode
import hu.bme.mit.theta.prob.analysis.besttransformer.BestTransformerAbstractor.BestTransformerGameNode.ConcreteChoiceNode
import hu.bme.mit.theta.prob.analysis.linkedtransfuncs.LinkedTransFunc
import hu.bme.mit.theta.probabilistic.BacktrackableGame
import hu.bme.mit.theta.probabilistic.FiniteDistribution
import hu.bme.mit.theta.probabilistic.FiniteDistribution.Companion.dirac
import hu.bme.mit.theta.probabilistic.GameRewardFunction
import hu.bme.mit.theta.probabilistic.ImplicitStochasticGame

interface BestTransformerTransFunc<S : State, A : Action, P : Prec> {
    fun getNextStates(
        currState: S, commands: List<ProbabilisticCommand<A>>, prec: P
    ): List<List<Pair<ProbabilisticCommand<A>, FiniteDistribution<Pair<A, S>>>>>
}

class BasicBestTransformerTransFunc<S : State, A : Action, P : Prec>(
    val baseTransFunc: LinkedTransFunc<S, A, P>,
    val getGuardSatisfactionConfigs:
        (S, List<ProbabilisticCommand<A>>) ->
    List<List<ProbabilisticCommand<A>>>
) : BestTransformerTransFunc<S, A, P> {
    override fun getNextStates(
        currState: S,
        commands: List<ProbabilisticCommand<A>>,
        prec: P
    ): List<List<Pair<ProbabilisticCommand<A>, FiniteDistribution<Pair<A, S>>>>> {
        val results = arrayListOf<List<Pair<ProbabilisticCommand<A>, FiniteDistribution<Pair<A, S>>>>>()
        for (config in getGuardSatisfactionConfigs(currState, commands)) {
            val fullPrecond = config.fold(True() as Expr<BoolType>) { acc, command ->
                SmartBoolExprs.And(acc, command.guard)
            }
            val actions: List<A> = config.flatMap { it.result.support }
            val nexts = baseTransFunc.getSuccStates(currState, fullPrecond, actions, prec)
            for (next in nexts) {
                val possibleFullResult = arrayListOf<Pair<ProbabilisticCommand<A>, FiniteDistribution<Pair<A, S>>>>()
                val actionToResult = actions.zip(next).toMap()
                for (command in config) {
                    possibleFullResult.add(
                        command to command.result.transform { it to actionToResult[it]!! }
                    )
                }
                results.add(possibleFullResult)
            }
        }
        return results
    }
}

class BestTransformerAbstractor<S : State, A : Action, P : Prec>(
    val lts: ProbabilisticCommandLTS<S, A>,
    val init: InitFunc<S, P>,
    val transFunc: BestTransformerTransFunc<S, A, P>,
    val targetExpr: Expr<BoolType>,
    val maySatisfy: (S, Expr<BoolType>) -> Boolean,
    val mustSatisfy: (S, Expr<BoolType>) -> Boolean,
    val trackPredecessors: Boolean = false
) {
    sealed class BestTransformerGameNode<S : State, A : Action>(val player: Int) {
        data class AbstractionChoiceNode<S : State, A : Action>(
            val s: S,
            val maxReward: Int = 0,
            val minReward: Int = 0,

            // If the reward split expression evaluates to true in a concrete state,
            // then that provides maxReward; if not, it provides minReward
            val rewardSplitExpr: Expr<BoolType>? = null,

            // Expression specifying the reward given by a concrete state
            val rewardExpr: Expr<IntType>? = null,

            // Whether the node should be made absorbing regardless of whether any action is enabled originally
            // Used for making the target states absorbing for reachability queries
            val absorbing: Boolean = false
        ) : BestTransformerGameNode<S, A>(P_ABSTRACTION) {
            init {
                require(maxReward == minReward || rewardSplitExpr != null || rewardExpr != null) {
                    "If maximal and minimal rewards are not the same, then either a reward split expression or a reward expression is needed"
                }
            }
        }

        data class ConcreteChoiceNode<S : State, A : Action>(
            val commandResults: Map<ProbabilisticCommand<A>, FiniteDistribution<Pair<A, S>>>
        ) : BestTransformerGameNode<S, A>(P_CONCRETE)
    }

    sealed class BestTransformerGameAction<S : State, A : Action> {
        data class AbstractionChoice<S : State, A : Action>(
            val commandResults: Map<ProbabilisticCommand<A>, FiniteDistribution<Pair<A, S>>>
        ) : BestTransformerGameAction<S, A>()

        data class ConcreteChoice<S : State, A : Action>(
            val command: ProbabilisticCommand<A>
        ) : BestTransformerGameAction<S, A>()
    }

    data class AbstractionResult<S : State, A : Action>(
        val game: BestTransformerGame<S, A, *>,
        val rewardMin: GameRewardFunction<BestTransformerGameNode<S, A>, BestTransformerGameAction<S, A>>,
        val rewardMax: GameRewardFunction<BestTransformerGameNode<S, A>, BestTransformerGameAction<S, A>>
    )

    class BestTransformerGame<S : State, A : Action, P : Prec>(
        val prec: P,
        val trackPredecessors: Boolean = false,
        val lts: ProbabilisticCommandLTS<S, A>,
        val init: InitFunc<S, P>,
        val transFunc: BestTransformerTransFunc<S, A, P>,
        val targetExpr: Expr<BoolType>,
        val maySatisfy: (S, Expr<BoolType>) -> Boolean,
        val mustSatisfy: (S, Expr<BoolType>) -> Boolean,
    ) : ImplicitStochasticGame<BestTransformerGameNode<S, A>, BestTransformerGameAction<S, A>>(),
        BacktrackableGame<BestTransformerGameNode<S, A>> {
        private val _initialNode: BestTransformerGameNode<S, A>
        private val predecessors = hashMapOf<BestTransformerGameNode<S, A>, MutableSet<BestTransformerGameNode<S, A>>>()

        init {
            val initState = init.getInitStates(prec).first() // TODO: cannot handle multiple abstract inits yet
            val mayBeTarget = maySatisfy(initState, targetExpr)
            val mustBeTarget = mustSatisfy(initState, targetExpr)
            _initialNode = AbstractionChoiceNode(
                initState,
                if (mayBeTarget) 1 else 0,
                if (mustBeTarget) 1 else 0,
                targetExpr,
                null,
                mustBeTarget
            )
            predecessors[initialNode] = hashSetOf()
        }

        override val initialNode: BestTransformerGameNode<S, A>
            get() = _initialNode

        val transFuncCache = hashMapOf<BestTransformerGameNode<S, A>, Collection<BestTransformerGameAction<S, A>>>()
        override fun getAvailableActions(node: BestTransformerGameNode<S, A>): Collection<BestTransformerGameAction<S, A>> {
            when (node) {
                is AbstractionChoiceNode -> {
                    if (node.absorbing) return listOf()
                    return transFuncCache.getOrPut(node) {
                        val commands = lts.getAvailableCommands(node.s).toList()
                        val choices = transFunc.getNextStates(node.s, commands, prec)
                        return@getOrPut choices.map { AbstractionChoice(it.toMap()) }
                    }
                }

                is ConcreteChoiceNode -> return node.commandResults.keys.map { ConcreteChoice(it) }
            }
        }

        private val resultCache = hashMapOf<
                Pair<BestTransformerGameNode<S, A>,BestTransformerGameAction<S, A>>,
            FiniteDistribution<BestTransformerGameNode<S, A>>>()
        override fun getResult(
            node: BestTransformerGameNode<S, A>,
            action: BestTransformerGameAction<S, A>
        ): FiniteDistribution<BestTransformerGameNode<S, A>> {
            val result: FiniteDistribution<BestTransformerGameNode<S, A>> =
                resultCache.getOrPut(node to action) {
                    when (node) {
                        is AbstractionChoiceNode -> {
                            when (action) {
                                is AbstractionChoice -> dirac(ConcreteChoiceNode(action.commandResults))
                                is ConcreteChoice -> throw IllegalArgumentException()
                            }
                        }

                        is ConcreteChoiceNode -> {
                            when (action) {
                                is AbstractionChoice -> throw IllegalArgumentException()
                                is ConcreteChoice -> node.commandResults[action.command]!!.transform {
                                    val mayBeTarget = maySatisfy(it.second, targetExpr)
                                    val mustBeTarget = mustSatisfy(it.second, targetExpr)
                                    require(mustBeTarget == mayBeTarget) {
                                        "The abstraction must be exact with respect to the target labels/rewards for now"
                                    }
                                    AbstractionChoiceNode(
                                        it.second,
                                        if (mayBeTarget) 1 else 0,
                                        if (mustBeTarget) 1 else 0,
                                        targetExpr,
                                        null,
                                        mustBeTarget
                                    )
                                }
                            }
                        }
                    }
                }
            if (trackPredecessors) {
                for (resultNode in result.support) {
                    predecessors.getOrPut(resultNode) { hashSetOf() }.add(node)
                }
            }
            return result
        }

        override fun getPlayer(node: BestTransformerGameNode<S, A>) = node.player

        override fun getPreviousNodes(node: BestTransformerGameNode<S, A>) =
            if (trackPredecessors) predecessors[node]!!
            else throw UnsupportedOperationException("Predecessors are not tracked for this instance")
    }


    fun computeAbstraction(prec: P): AbstractionResult<S, A> {

        val rewardFunMax = object : GameRewardFunction<BestTransformerGameNode<S, A>, BestTransformerGameAction<S, A>> {
            override fun getStateReward(n: BestTransformerGameNode<S, A>): Double {
                return when (n) {
                    is AbstractionChoiceNode -> n.maxReward.toDouble()
                    is ConcreteChoiceNode -> 0.0
                }
            }

            override fun getEdgeReward(
                source: BestTransformerGameNode<S, A>,
                action: BestTransformerGameAction<S, A>,
                target: BestTransformerGameNode<S, A>
            ): Double {
                return 0.0 // for now
            }
        }

        val rewardFunMin = object : GameRewardFunction<BestTransformerGameNode<S, A>, BestTransformerGameAction<S, A>> {
            override fun getStateReward(n: BestTransformerGameNode<S, A>): Double {
                return when (n) {
                    is AbstractionChoiceNode -> n.minReward.toDouble()
                    is ConcreteChoiceNode -> 0.0
                }
            }

            override fun getEdgeReward(
                source: BestTransformerGameNode<S, A>,
                action: BestTransformerGameAction<S, A>,
                target: BestTransformerGameNode<S, A>
            ): Double {
                return 0.0 // for now
            }
        }


        val game = BestTransformerGame(
            prec,
            trackPredecessors,
            lts,
            init,
            transFunc,
            targetExpr,
            maySatisfy,
            mustSatisfy,
        )

        return AbstractionResult(game, rewardFunMin, rewardFunMax)
    }

}