package hu.bme.mit.theta.prob.analysis.direct

import com.google.common.base.Stopwatch
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.analysis.TransFunc
import hu.bme.mit.theta.analysis.expl.ExplPrec
import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.prob.analysis.ProbabilisticCommand
import hu.bme.mit.theta.prob.analysis.jani.*
import hu.bme.mit.theta.prob.analysis.lazy.SMDPLazyChecker.Algorithm.*
import hu.bme.mit.theta.prob.analysis.lazy.SMDPLazyChecker.BRTDPStrategy.*
import hu.bme.mit.theta.probabilistic.*
import hu.bme.mit.theta.probabilistic.gamesolvers.ExpandableNode
import hu.bme.mit.theta.probabilistic.gamesolvers.ExpansionResult
import hu.bme.mit.theta.probabilistic.gamesolvers.initializers.ExplicitInitializer
import hu.bme.mit.theta.probabilistic.gamesolvers.initializers.MDPAlmostSureTargetInitializer
import hu.bme.mit.theta.probabilistic.gamesolvers.initializers.TargetSetLowerInitializer
import java.util.*
import java.util.concurrent.TimeUnit

typealias DirectCheckerNode<S, A> = DirectChecker<S, A>.DirectCheckerMDP.NodeClass
class DirectChecker<S: State, A: StmtAction>(
    val getStdCommands: (S) -> Collection<ProbabilisticCommand<A>>,
    val isEnabled: (S, ProbabilisticCommand<A>) -> Boolean,
    _isTarget: ((S) -> Boolean)? = null,
    _reward: ((S)-> Double)? = null,
    val accumulateRewardOnExit: Boolean = false,
    val accumulateRewardAfterStep: Boolean = false,
    val initState: S,

    val transFunc: TransFunc<S, in A, ExplPrec>,
    val fullPrec: ExplPrec,
    val mdpSolver: StochasticGameSolver<DirectCheckerNode<S, A>, FiniteDistribution<DirectCheckerNode<S, A>>>,
    val useQualitativePreprocessing: Boolean = false,
    val verboseLogging: Boolean = false
) {
    init {
        require(_isTarget != null || _reward != null)
        require(_isTarget == null || _reward == null)
        require(_reward == null || accumulateRewardOnExit || accumulateRewardAfterStep)
    }
    val isTarget = _isTarget ?: {false}
    val reward = _reward ?: {0.0}
    val checkReward = _reward != null

    fun check(
        goal: Goal,
        measureExplorationTime: Boolean = false
    ): Double {

        val game = getMDP()
        val rewardFunction = getRewardFun()

        val timer = Stopwatch.createStarted()
        if(measureExplorationTime) {
            game.getAllNodes() // this forces full exploration of the game
            timer.stop()
            val explorationTime = timer.elapsed(TimeUnit.MILLISECONDS)
            println("Exploration time (ms): $explorationTime")
            timer.reset()
            timer.start()
        }

        val initializer = getInitializer(game, goal)

        if(initializer.isKnown(game.initNode)) {
            timer.stop()
            val probTime = timer.elapsed(TimeUnit.MILLISECONDS)
            println("Precomputation sufficient, result: ${initializer.initialLowerBound(game.initNode)}")
            println("Probability computation time (ms): $probTime")
            println("All nodes: ${game.reachedSet.size}")
            return initializer.initialLowerBound(game.initNode)
        }
        val quantSolver = mdpSolver

        val analysisTask = AnalysisTask(game, {goal}, rewardFunction)
        val values = quantSolver.solve(analysisTask, initializer)

        timer.stop()
        val probTime = timer.elapsed(TimeUnit.MILLISECONDS)
        println("Probability computation time (ms): $probTime")
        println("All nodes: ${game.reachedSet.size}")

        return values[game.initNode]!!
    }

    fun checkWithDebugInfo(
        goal: Goal,
        measureExplorationTime: Boolean = false
    ) {

    }

    companion object {
        private var nextId = 0
    }

    fun getMDP() = this.DirectCheckerMDP()
    fun getRewardFun() =
        if(checkReward) object : GameRewardFunction<DirectCheckerNode<S, A>, FiniteDistribution<DirectCheckerNode<S, A>>> {
        override fun getStateReward(n: DirectCheckerNode<S, A>): Double {
            return 0.0
        }

        override fun getEdgeReward(
            source: DirectCheckerNode<S, A>,
            action: FiniteDistribution<DirectCheckerNode<S, A>>,
            target: DirectCheckerNode<S, A>
        ): Double {
            val onExit = if(accumulateRewardOnExit) source.rewardOnExit else 0.0
            val afterStep = if(accumulateRewardAfterStep) target.rewardOnExit else 0.0
            return onExit + afterStep
        }

    }
    else TargetRewardFunction {
        it.isTargetNode
    }
    fun getInitializer(game: DirectCheckerMDP, goal: Goal) =
        if(checkReward) {
            ExplicitInitializer(
                mapOf(), mapOf(), 0.0, Double.POSITIVE_INFINITY, 1e-7, mapOf()
            )
        }
        else if(useQualitativePreprocessing)
            MDPAlmostSureTargetInitializer(game, goal, DirectCheckerNode<S, A>::isTargetNode)
        else TargetSetLowerInitializer {
            it.isTargetNode
        }


    inner class DirectCheckerMDP : StochasticGame<DirectCheckerMDP.NodeClass, FiniteDistribution<DirectCheckerNode<S, A>>> {
        val initNode = NodeClass(initState)
        init {
            initNode.isTargetNode = isTarget(initState)
            initNode.rewardOnExit = reward(initState)
        }
        val waitlist: Queue<NodeClass> = ArrayDeque<NodeClass>().apply { add(initNode) }
        val reachedSet = hashMapOf(initState to initNode)

        override fun materialize(): StochasticGame.MaterializationResult<NodeClass> {
            getAllNodes() //forces full exploration to make sure all nodes have been expanded
            return super.materialize()
        }

        override val initialNode: NodeClass
            get() = initNode

        override fun getAllNodes(): Collection<NodeClass> {

            while (!waitlist.isEmpty()) {
                val node = waitlist.remove()
                if(!node.isTargetNode) {
                    node.expand()
                }
            }
            return reachedSet.values
        }

        override fun getPlayer(node: NodeClass): Int = 0

        override fun getResult(node: NodeClass, action: FiniteDistribution<NodeClass>): FiniteDistribution<NodeClass> {
            require(node.expanded)
            return action
        }

        override fun getAvailableActions(node: NodeClass): List<FiniteDistribution<NodeClass>> {
            require(node.expanded)
            return node.getOutgoingEdges()
        }

        inner class NodeClass(val state: S): ExpandableNode<NodeClass> {

            private val id = nextId++
            private val outEdges = arrayListOf<FiniteDistribution<NodeClass>>()
            var expanded: Boolean = false
            var isTargetNode: Boolean = false
            var rewardOnExit: Double = 0.0
            fun getOutgoingEdges(): List<FiniteDistribution<NodeClass>> = outEdges
            fun createEdge(target: FiniteDistribution<NodeClass>) {
                outEdges.add(target)
            }

            override fun hashCode(): Int {
                return Objects.hashCode(this.id)
            }

            override fun isExpanded(): Boolean {
                return expanded
            }

            override fun expand(
            ): ExpansionResult<NodeClass> {
                val stdCommands = getStdCommands(this.state)
                this.expanded = true
                if (this.isTargetNode) return ExpansionResult(listOf(), listOf())

                val currState = this.state
                val newChildren = arrayListOf<DirectCheckerNode<S, A>>()
                val revisited = arrayListOf<DirectCheckerNode<S, A>>()
                for (cmd in stdCommands) {
                    if (isEnabled(currState, cmd)) {
                        val target = cmd.result.transform { a ->
                            val nextState =
                                transFunc
                                    .getSuccStates(currState, a, fullPrec)
                                    // TODO: this works only with deterministic actions now
                                    .first()
                            val newNode = if (reachedSet.containsKey(nextState)) {
                                val n = reachedSet.getValue(nextState)
                                revisited.add(n)
                                n
                            } else {
                                val n = NodeClass(nextState)
                                newChildren.add(n)
                                reachedSet[nextState] = n
                                if (isTarget(n.state)) {
                                    n.isTargetNode = true
                                    n.expanded = true
                                }
                                n.rewardOnExit = reward(n.state)
                                n
                            }
                            newNode
                        }
                        this.createEdge(target)
                    }
                }
                waitlist?.addAll(newChildren)
                return ExpansionResult(newChildren, revisited)
            }

            override fun equals(other: Any?): Boolean {
                if (this === other) return true
                if (javaClass != other?.javaClass) return false

                other as DirectCheckerNode<S, A>

                return id == other.id
            }

        }

    }
}