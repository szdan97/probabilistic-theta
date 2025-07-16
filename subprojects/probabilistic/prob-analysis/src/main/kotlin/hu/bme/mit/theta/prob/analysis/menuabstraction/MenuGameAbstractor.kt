package hu.bme.mit.theta.prob.analysis.menuabstraction

import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.analysis.InitFunc
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.prob.analysis.ProbabilisticCommandLTS
import hu.bme.mit.theta.probabilistic.*
import hu.bme.mit.theta.probabilistic.FiniteDistribution.Companion.dirac

class MenuGameAbstractor<S : State, A : Action, P : Prec>(
    val lts: ProbabilisticCommandLTS<S, A>,
    val init: InitFunc<S, P>,
    val transFunc: MenuGameTransFunc<S, A, P>,
    val targetExpr: Expr<BoolType>,
    val maySatisfy: (S, Expr<BoolType>) -> Boolean,
    val mustSatisfy: (S, Expr<BoolType>) -> Boolean,
    val trackPredecessors: Boolean=false
) {

    data class AbstractionResult<S : State, A : Action>(
        val game: StochasticGame<MenuGameNode<S, A>, MenuGameAction<S, A>>,
        val rewardMin: GameRewardFunction<MenuGameNode<S, A>, MenuGameAction<S, A>>,
        val rewardMax: GameRewardFunction<MenuGameNode<S, A>, MenuGameAction<S, A>>
    )

    fun computeAbstraction(prec: P): AbstractionResult<S, A> {

        val rewardFunMax = MenuGameUpperRewardFunc<S, A>()

        val rewardFunMin = MenuGameLowerRewardFunc<S, A>()

        val game = StandardMenuGame(
            prec,
            lts,
            init,
            transFunc,
            targetExpr,
            maySatisfy,
            mustSatisfy,
            trackPredecessors
        )

        return AbstractionResult(game, rewardFunMin, rewardFunMax)
    }

    class StandardMenuGame<S : State, A : Action, P : Prec>(
        val prec: P,
        val lts: ProbabilisticCommandLTS<S, A>,
        val init: InitFunc<S, P>,
        val transFunc: MenuGameTransFunc<S, A, P>,
        val targetExpr: Expr<BoolType>,
        val maySatisfy: (S, Expr<BoolType>) -> Boolean,
        val mustSatisfy: (S, Expr<BoolType>) -> Boolean,
        val trackPredecessors: Boolean = false
    ) : ImplicitStochasticGame<MenuGameNode<S, A>, MenuGameAction<S, A>>(),
        BacktrackableGame<MenuGameNode<S, A>> {

        private val _initialNode: MenuGameNode<S, A>
        private val predecessors = hashMapOf<MenuGameNode<S, A>, MutableSet<MenuGameNode<S, A>>>()


        init {
            val initState = init.getInitStates(prec).first() // TODO: cannot handle multiple abstract inits yet
            val mayBeTarget = maySatisfy(initState, targetExpr)
            val mustBeTarget = mustSatisfy(initState, targetExpr)
            _initialNode = MenuGameNode.StateNode(
                initState,
                if (mayBeTarget) 1 else 0,
                if (mustBeTarget) 1 else 0,
                targetExpr,
                null,
                mustBeTarget
            )
            predecessors[_initialNode] = hashSetOf()
        }

        override val initialNode: MenuGameNode<S, A>
            get() = _initialNode

        val trapNode = MenuGameNode.TrapNode<S, A>()
        val trapDecision = MenuGameAction.EnterTrap<S, A>()
        val trapDirac = dirac(trapNode as MenuGameNode<S, A>)

        // TODO: is there a better way to do this without data classes (so that BLASTMenuGame can still work)?
        //      although this still does not enforce full exploration, so it's not a materialization,
        //      but the game interface was meant to be used in a more mathematical way
        private val stateToNodeMap = hashMapOf(
            (_initialNode as MenuGameNode.StateNode).s to _initialNode
        )

        override fun getPlayer(node: MenuGameNode<S, A>): Int = node.player

        private  fun getOrCreateNode(
            s: S, minReward: Int = 0, maxReward: Int = 0,
            rewardSplitExpr: Expr<BoolType>? = null,
            rewardExpr: Expr<IntType>? = null,
            absorbing: Boolean = false
        ): MenuGameNode.StateNode<S, A> = stateToNodeMap.getOrPut(s) {
            MenuGameNode.StateNode(s, minReward, maxReward, rewardSplitExpr, rewardExpr, absorbing)
        }

        private val resultCache = hashMapOf<Pair<MenuGameNode<S, A>, MenuGameAction<S, A>>, FiniteDistribution<MenuGameNode<S, A>>>()
        override fun getResult(
            node: MenuGameNode<S, A>,
            action: MenuGameAction<S, A>
        ): FiniteDistribution<MenuGameNode<S, A>> {
            val result: FiniteDistribution<MenuGameNode<S, A>> =
                resultCache.getOrPut(node to action) {
                    when (node) {
                        is MenuGameNode.StateNode -> when (action) {
                            is MenuGameAction.AbstractionDecision -> throw IllegalArgumentException("Result called for unavailable action $action on node $node")
                            is MenuGameAction.ChosenCommand -> dirac(
                                MenuGameNode.ResultNode(node.s, action.command)
                            )

                            is MenuGameAction.EnterTrap -> throw IllegalArgumentException("Result called for unavailable action $action on node $node")
                        }

                        is MenuGameNode.ResultNode -> when (action) {
                            is MenuGameAction.AbstractionDecision ->
                                action.result.transform {
                                    val mayBeTarget = maySatisfy(it.second, targetExpr)
                                    val mustBeTarget = mustSatisfy(it.second, targetExpr)
                                    require(mustBeTarget == mayBeTarget) {
                                        "The abstraction must be exact with respect to the target labels/rewards for now"
                                    }
                                    getOrCreateNode(
                                        it.second,
                                        if (mayBeTarget) 1 else 0,
                                        if (mustBeTarget) 1 else 0,
                                        targetExpr,
                                        null,
                                        mustBeTarget
                                    )
                                }

                            is MenuGameAction.ChosenCommand -> throw IllegalArgumentException("Result called for unavailable action $action on node $node")
                            is MenuGameAction.EnterTrap -> trapDirac
                        }

                        is MenuGameNode.TrapNode -> throw IllegalArgumentException("Result called for unavailable action $action on node $node")
                    }
                }
            if (trackPredecessors) {
                for (resultNode in result.support) {
                    predecessors.getOrPut(resultNode) { hashSetOf() }.add(node)
                }
            }
            return result
        }

        val transFuncCache = hashMapOf<MenuGameNode<S, A>, Collection<MenuGameAction<S, A>>>()
        override fun getAvailableActions(node: MenuGameNode<S, A>): Collection<MenuGameAction<S, A>> {
            return when (node) {
                is MenuGameNode.StateNode -> transFuncCache.getOrPut(node) {
                    if (node.absorbing || node.s.isBottom) listOf()
                    else lts.getAvailableCommands(node.s).filter {
                        maySatisfy(node.s, it.guard)
                    }.map { MenuGameAction.ChosenCommand(it) }
                }

                is MenuGameNode.ResultNode -> transFuncCache.getOrPut(node) {
                    val transFuncResult = transFunc.getNextStates(node.s, node.a, prec)
                    val res = transFuncResult.succStates.map {
                        MenuGameAction.AbstractionDecision<S, A>(it)
                    }
                    if (transFuncResult.canBeDisabled) res + trapDecision
                    else res
                }

                is MenuGameNode.TrapNode -> listOf()
            }
        }

        override fun getPreviousNodes(n: MenuGameNode<S, A>): Collection<MenuGameNode<S, A>> {
            return if (trackPredecessors) predecessors[n]!!
            else throw UnsupportedOperationException("Predecessors are not tracked for this instance")
        }

    }

}