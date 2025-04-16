package hu.bme.mit.theta.prob.analysis.lazy

import com.google.common.base.Stopwatch
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.common.logging.ConsoleLogger
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.prob.analysis.ProbabilisticCommand
import hu.bme.mit.theta.probabilistic.*
import hu.bme.mit.theta.probabilistic.FiniteDistribution.Companion.dirac
import hu.bme.mit.theta.probabilistic.gamesolvers.*
import hu.bme.mit.theta.probabilistic.gamesolvers.initializers.FallbackInitializer
import hu.bme.mit.theta.probabilistic.gamesolvers.initializers.MDPAlmostSureTargetInitializer
import hu.bme.mit.theta.probabilistic.gamesolvers.initializers.TargetSetLowerInitializer
import java.util.*
import java.util.concurrent.TimeUnit
import kotlin.collections.set
import kotlin.math.min

class ProbLazyChecker<SC : ExprState, SA : ExprState, A : StmtAction>(
    // Model properties
    val getStdCommands: (SC) -> Collection<ProbabilisticCommand<A>>,
    val getErrorCommands: (SC) -> Collection<ProbabilisticCommand<A>>,
    val initState: SC,
    val topInit: SA,

    val domain: LazyDomain<SC, SA, A>,

    val goal: Goal,

    // Checker Configuration

    // Approximation settings
    private val useMayStandard: Boolean = true,
    private val useMustStandard: Boolean = false,
    private val useMayTarget: Boolean = true,
    private val useMustTarget: Boolean = false,

    // Logging
    private val verboseLogging: Boolean = false,
    private val logger: Logger = ConsoleLogger(Logger.Level.VERBOSE),


    private val resetOnUncover: Boolean = true,
    private val useMonotonicBellman: Boolean = false,
    private val useSeq: Boolean = false,
    private val useGameRefinement: Boolean = false,
    private val useQualitativePreprocessing: Boolean = false,
    private val mergeSameSCNodes: Boolean = false,
    private val refinementStrategy: EdgeRefinementStrategy = EdgeRefinementStrategy.ALL_EDGES,
) {
    /**
     * Controls which edges of the selected node to make surely enabled
     * when performing refinement in the game-based version.
     */
    enum class EdgeRefinementStrategy {
        ALL_EDGES,
        OPTIMAL_EDGES,
        SINGLE_EDGE
    }

    private var numCoveredNodes = 0
    private var numRealCovers = 0

    private fun reset() {
        waitlist.clear()
        numCoveredNodes = 0
        numRealCovers = 0
    }

    init {
        if (!(useMayStandard || useMustStandard)) throw RuntimeException("No approximation type (must/may/both) specified for standard commands!")
        if (!(useMayTarget || useMustTarget)) throw RuntimeException("No approximation type (must/may/both) specified for target commands!")
        if (goal == Goal.MIN && !useMayStandard)
            // the simulation theorem only holds for non-absorbing MDPs, and adding theoretical self-loops is non-trivial for this case
            // a possible solution would be to do the same as in the lower approx of the game-based version:
            // a node should be considered a target if it is absorbing, but there are non-absorbing s \in L_a(n)
            TODO("MIN with lower-cover is unsound for now")
    }

    val waitlist = ArrayDeque<Node>()

    private var nextNodeId = 0

    var currReachedSet: TrieReachedSet<Node, *>? = null
    val globalScToNode: HashMap<SC, List<Node>>? =
        if (mergeSameSCNodes) hashMapOf() else null

    inner class Node(
        val sc: SC, sa: SA
    ) : ExpandableNode<Node> {
        val maySatErrors = arrayListOf<ProbabilisticCommand<A>>()
        var mayBeError: Boolean = false
        val mustSatErrors = arrayListOf<ProbabilisticCommand<A>>()
        var mustBeError: Boolean = false

        var sa: SA = sa
            private set(v) {
                val tracked = currReachedSet?.delete(this) ?: false
                field = v
                if (tracked) currReachedSet?.add(this)
            }

        var onUncover: ((Node) -> Unit)? = null

        val id: Int = nextNodeId++

        var _isExpanded = false

        fun isComplete() = _isExpanded || isCovered || isErrorNode
        override fun isExpanded(): Boolean {
            return _isExpanded
        }

        override fun expand(): ExpansionResult<Node> {
            return this@ProbLazyChecker.expand(
                this,
                getStdCommands(this.sc),
                getErrorCommands(this.sc),
                if (mergeSameSCNodes) globalScToNode else null
            )
        }

        override fun hashCode(): Int {
            // as SA and the outgoing edges change throughout building the ARG,
            // and hash maps/sets are often used during this, the hashcode must not depend on them
            return Objects.hash(id)
        }

        private val outEdges = arrayListOf<Edge>()
        var backEdges = arrayListOf<Edge>()
        var coveringNode: Node? = null
            private set
        private val coveredNodes = arrayListOf<Node>()
        val isCovered: Boolean
            get() = coveringNode != null

        val isCovering: Boolean
            get() = coveredNodes.isNotEmpty()
        var isErrorNode = false
            private set

        fun getOutgoingEdges(): List<Edge> = outEdges
        fun createEdge(
            target: FiniteDistribution<Pair<A, Node>>,
            guard: Expr<BoolType>,
            surelyEnabled: Boolean,
            relatedCommand: ProbabilisticCommand<A>
        ): Edge {
            val newEdge = Edge(this, target, guard, surelyEnabled, relatedCommand)
            outEdges.add(newEdge)
            target.support.forEach { (a, n) ->
                n.backEdges.add(newEdge)
            }
            return newEdge
        }

        private var realCovered = false
        fun coverWith(coverer: Node) {
            require(!isCovered)
            numCoveredNodes++
            // equality checking of sc-s can be expensive if done often,
            // so we do this only if the number of real covers is logged
            if (verboseLogging && coverer.sc != this.sc) {
                realCovered = true
                numRealCovers++
            }
            coveringNode = coverer
            coverer.coveredNodes.add(this)
        }

        fun removeCover() {
            require(isCovered)
            numCoveredNodes--
            if (verboseLogging && realCovered) {
                realCovered = false
                numRealCovers--
            }
            coveringNode!!.coveredNodes.remove(this)
            coveringNode = null
            onUncover?.invoke(this)
        }

        fun strengthenWithSeq(toblock: Expr<BoolType>, forEdge: Edge? = null) {
            var currNode = this
            val nodes = arrayListOf(currNode)
            val guards = arrayListOf<Expr<BoolType>>()
            val actions = arrayListOf<A>()

            if(forEdge != null) {
                guards.add(0, forEdge.guard)
                actions.add(0, forEdge.getActionFor(currNode))
                currNode = forEdge.source
                require(!nodes.contains(currNode))
                nodes.add(0, currNode)
            }

            // TODO: better handling of the init node
            while (currNode.backEdges.isNotEmpty() && currNode.id != 0) {
                val backEdge = currNode.backEdges.first()
                guards.add(0, backEdge.guard)
                actions.add(0, backEdge.getActionFor(currNode))
                currNode = backEdge.source
                require(!nodes.contains(currNode))
                nodes.add(0, currNode)
            }

            val newLabels = domain.blockSeq(nodes, guards, actions, toblock)
            val forceCovers = arrayListOf<Node>()

            // As only a single path to the root can be strengthened at once, we need to deal with the other parents later
            val secondaryParentStrengthenings = arrayListOf<Pair<Node, List<Edge>>>()

            for ((i, node) in nodes.withIndex()) {
                if (newLabels[i] == node.sa) continue
                node.sa = newLabels[i]
                secondaryParentStrengthenings.add(node to node.backEdges.drop(1))

                val cpy = ArrayList(node.coveredNodes) // copy because removeCover() modifies it inside the loop
                for (coveredNode in cpy) {
                    if (!domain.checkContainment(coveredNode.sc, node.sa)) {
                        coveredNode.removeCover()
                        require(coveredNode !in waitlist)
                        waitlist.add(coveredNode)
                    } else {
                        forceCovers.add(coveredNode)
                    }
                }
                forceCovers.forEach {
                    if (it.isCovered) // the previous strengthenForCovering calls might have removed the cover of the current node
                        it.strengthenForCovering()
                }
            }

            for ((node, inEdges) in secondaryParentStrengthenings) {
                // TODO: check if taking only 1 edge really makes sense
                //  the idea is that the recursive call will account for all the other parents
                for (inEdge in inEdges.take(1)) {
//                    val action = inEdge.getActionFor(node)
//                    val preImage = ExprUtils.simplify(domain.preImage(node.sa, action), ImmutableValuation.empty())
//                    val toBlock = SmartBoolExprs.And(inEdge.guard, Not(preImage))
//                    if(preImage != True())
//                        inEdge.source.strengthenWithSeq(toBlock)

                    node.strengthenWithSeq(Not(node.sa.toExpr()), inEdge)
                }
            }
        }

        fun changeAbstractLabel(
            newLabel: SA
        ) {
            if (newLabel == sa) return
            sa = newLabel
            val cpy = ArrayList(coveredNodes)
            for (coveredNode in cpy) { // copy because removeCover() modifies it inside the loop
                if (!coveredNode.isCovered) continue // strengthening of other covered nodes might have removed the cover
                if (!domain.checkContainment(coveredNode.sc, this.sa)) {
                    coveredNode.removeCover()
                    waitlist.add(coveredNode)
                } else {
                    coveredNode.strengthenForCovering()
                }
            }

            // strengthening the parent
            strengthenParents()
        }

        fun strengthenParents() {
            for (backEdge in backEdges) {
                val parent = backEdge.source
                val action = backEdge.getActionFor(this)
                // TODO: what if preImage is equivalent to True?
                val preImage = ExprUtils.simplify(domain.preImage(this.sa, action), ImmutableValuation.empty())
                val toBlock = SmartBoolExprs.And(backEdge.guard, Not(preImage))

                if (preImage == True()) continue

                if (useSeq) {
                    parent.strengthenWithSeq(toBlock)
                } else {
                    val constrainedToPreImage = domain.block(
                        parent.sa,
                        toBlock,
                        parent.sc
                    )
                    parent.changeAbstractLabel(constrainedToPreImage)
                }
            }
        }

        fun markAsErrorNode() {
            isErrorNode = true
        }

        fun strengthenForCovering() {
            require(isCovered)
            val coverer = coveringNode!!
            if (!domain.isLeq(sa, coverer.sa)) {
                if (useSeq) strengthenWithSeq(Not(coverer.sa.toExpr()))
                else {
                    val newExpr =
                        if (sa.toExpr() == True()) coverer.sa
                        else domain.block(sa, Not(coverer.sa.toExpr()), sc)
                    changeAbstractLabel(newExpr)
                }
            }
        }

        fun strengthenAgainstCommand(
            c: ProbabilisticCommand<A>,
            negate: Boolean = false
        ) {
            val toblock =
                if (negate) Not(c.guard)
                else c.guard

            if (useSeq) strengthenWithSeq(toblock)
            else {
                val modifiedAbstract = domain.block(sa, toblock, sc)
                changeAbstractLabel(modifiedAbstract)
            }
        }

        fun strengthenAgainstCommands(
            negatedCommands: List<ProbabilisticCommand<A>>,
            nonNegatedCommands: List<ProbabilisticCommand<A>>
        ) {
            val toblock =
                SmartBoolExprs.Or(
                    negatedCommands.map { Not(it.guard) } + nonNegatedCommands.map { it.guard })

            if (useSeq) strengthenWithSeq(toblock)
            else {
                val modifiedAbstract = domain.block(sa, toblock, sc)
                changeAbstractLabel(modifiedAbstract)
            }
        }

        override fun toString(): String {
            return "Node[$id](c: $sc, a: $sa)"
        }

        fun getChildren(): List<Node> = this.getOutgoingEdges().flatMap { it.targetList.map { it.second } }

        /**
         * Recursively get all action-edge descendants. Does not traverse cover edges.
         */
        fun getDescendants(): List<Node> {
            val children = getChildren()
            return children + children.flatMap(ProbLazyChecker<SC, SA, A>.Node::getDescendants)
        }
    }

    inner class Edge(
        val source: Node, val target: FiniteDistribution<Pair<A, Node>>, val guard: Expr<BoolType>,
        surelyEnabled: Boolean, val relatedCommand: ProbabilisticCommand<A>
    ) {
        var targetList = target.support.toList()

        var surelyEnabled = surelyEnabled
            private set

        // used for round-robin strategy
        private var nextChoice = 0
        fun chooseNextRR(): Pair<A, Node> {
            val res = targetList[nextChoice]
            nextChoice = (nextChoice + 1) % targetList.size
            return res
        }

        fun getActionFor(result: Node): A {
            for ((a, n) in target.support) {
                if (n == result) return a
            }
            throw IllegalArgumentException("$result not found in the targets of edge $this")
        }

        fun makeSurelyEnabled() {
            surelyEnabled = true
        }

        override fun toString(): String {
            return target.transform { it.first }.toString()
        }
    }

    fun findMEC(
        root: Node,
        initAvailableEdges: (Node) -> List<Edge> = ProbLazyChecker<SC, SA, A>.Node::getOutgoingEdges
    ): Set<Node> {
        fun findSCC(root: Node, availableEdges: (Node) -> List<Edge>): Set<Node> {
            val stack = Stack<Node>()
            val lowlink = hashMapOf<Node, Int>()
            val index = hashMapOf<Node, Int>()
            var currIndex = 0

            fun strongConnect(n: Node): Set<Node> {
                index[n] = currIndex
                lowlink[n] = currIndex++
                stack.push(n)

                val successors =
                    if (n.isCovered) setOf(n.coveringNode!!)
                    else availableEdges(n).flatMap { it.targetList.map { it.second } }.toSet()
                for (m in successors) {
                    if (m !in index) {
                        strongConnect(m)
                        lowlink[n] = min(lowlink[n]!!, lowlink[m]!!)
                    } else if (stack.contains(m)) {
                        lowlink[n] = min(lowlink[n]!!, index[m]!!)
                    }
                }

                val scc = hashSetOf<Node>()
                if (lowlink[n] == index[n]) {
                    do {
                        val m = stack.pop()
                        scc.add(m)
                    } while (m != n)
                }
                return scc
            }

            return strongConnect(root)
        }

        var scc: Set<Node> = hashSetOf()
        var availableEdges: (Node) -> List<Edge> = initAvailableEdges
        do {
            val prevSCC = scc
            scc = findSCC(root, availableEdges)
            availableEdges = { n: ProbLazyChecker<SC, SA, A>.Node ->
                initAvailableEdges(n).filter { it.targetList.all { it.second in scc } }
            }
        } while (scc.size != prevSCC.size)
        return scc
    }

    private inner class VirtuallyMergedMDP(
        val _initialNode: Node,
        val merged: MutableMap<Node, Pair<Set<Node>, List<Edge>>>,
    ): ImplicitStochasticGame<Node, Edge>() {
        override val initialNode: Node
            get() = _initialNode

        override fun getAvailableActions(node: Node) =
            merged[node]!!.second

        override fun getResult(node: Node, action: Edge) =
            action.target.transform { it.second }

        override fun getPlayer(node: Node) = 0 // Only one player
    }

    fun brtdp(
        successorSelection:
        StochasticGame<Node, Edge>.(
            currNode: Node,
            L: Map<Node, Double>,
            U: Map<Node, Double>,
            goal: Goal
        ) -> Node,
        threshold: Double = 1e-7
    ) = if (useGameRefinement) brtdpWithGameRefinement(successorSelection, threshold)
    else simpleBrtdp(successorSelection, threshold)

    fun simpleBrtdp(
        successorSelection:
            StochasticGame<Node, Edge>.(
            currNode: Node,
            L: Map<Node, Double>,
            U: Map<Node, Double>,
            goal: Goal
        ) -> Node,
        threshold: Double = 1e-7
    ): Double {
        reset()
        val timer = Stopwatch.createStarted()
        val initNode = Node(initState, topInit)

        waitlist.add(initNode)

        val reachedSet = hashSetOf(initNode)
        val scToNode = hashMapOf(initNode.sc to arrayListOf(initNode))
        var U = hashMapOf(initNode to 1.0)
        var L = hashMapOf(initNode to 0.0)


        // virtually merged end components, also maintaining a set of edges that leave the EC for each of them
        val merged = hashMapOf(initNode to (setOf(initNode) to initNode.getOutgoingEdges()))
        var checkForMEC = arrayListOf<Node>()

        val game = VirtuallyMergedMDP(initNode, merged)

        fun onUncover(n: Node) {
            if (resetOnUncover) {
                U[n] = 1.0
                L[n] = 0.0
            }
            for (node in merged[n]!!.first) {
                merged[node] = setOf(node) to node.getOutgoingEdges()
                if (node != n)
                    checkForMEC.add(n)
            }
        }

        var i = 0

        while (U[initNode]!! - L[initNode]!! > threshold) {
            // logging for experiments
            i++
            if (i % 1000 == 0)
                if (verboseLogging) {
                    println(
                        "$i: " +
                                "nodes: ${reachedSet.size}, non-covered: ${reachedSet.size - numCoveredNodes}, " +
                                " real covers: $numRealCovers " +
                                "[${L[initNode]}, ${U[initNode]}], d=${U[initNode]!! - L[initNode]!!}, " +
                                "time (ms): ${timer.elapsed(TimeUnit.MILLISECONDS)}"
                    )
                }

            //----------------------------------------------------------------------------------------------------------

            // simulate a single trace
            val trace = arrayListOf(initNode)
            checkForMEC.clear()

            // TODO: probability-based bound for trace length (see learning algorithms paper)
            while (
                !((trace.last()._isExpanded && trace.last().getOutgoingEdges()
                    .isEmpty()) || (trace.size > reachedSet.size * 3))
            ) {
                val lastNode = trace.last()
                if (!lastNode._isExpanded) {
                    val (newlyDiscovered, revisited) = expand(
                        lastNode,
                        getStdCommands(lastNode.sc),
                        getErrorCommands(lastNode.sc),
                        if (mergeSameSCNodes) scToNode else null
                    )
                    if (mergeSameSCNodes) {
                        checkForMEC.addAll(revisited)
                    }
                    // as the node has just been expanded, its outgoing edges have been changed,
                    // so the merged map needs to be updated as well
                    if (merged[lastNode]!!.first.size == 1)
                        merged[lastNode] = setOf(lastNode) to lastNode.getOutgoingEdges()

                    for (newNode in newlyDiscovered) {
                        newNode.onUncover = ::onUncover

                        // treating each node as its own EC at first so that value computations can be done
                        // solely based on the _merged_ map
                        merged[newNode] = setOf(newNode) to newNode.getOutgoingEdges()
                        close(newNode, reachedSet, scToNode)
                        reachedSet.add(newNode)
                        if (newNode.sc in scToNode) {
                            scToNode[newNode.sc]!!.add(newNode)
                        } else {
                            scToNode[newNode.sc] = arrayListOf(newNode)
                        }
                        if (newNode.isCovered) {
                            checkForMEC.add(newNode)
                            U[newNode] = U.getOrDefault(newNode.coveringNode!!, 1.0)
                            L[newNode] = L.getOrDefault(newNode.coveringNode!!, 0.0)
                        } else {
                            U[newNode] = 1.0
                            L[newNode] = 0.0
                        }
                    }

                    if (newlyDiscovered.isEmpty() && revisited.isEmpty()) {
                        // marking as error node is done during expanding the node,
                        // so the node might have become an error node since starting the core
                        if (lastNode.isErrorNode)
                            L[lastNode] = 1.0
                        // absorbing nodes can never lead to an error node
                        else
                            U[lastNode] = 0.0
                        break
                    }
                }

                // stop if a non-exitable MEC is reached
                if (merged[lastNode]!!.second.isEmpty())
                    break

                val nextNode = game.successorSelection(lastNode, L, U, goal)


                trace.add(nextNode)
                // this would lead to infinite traces in MECs, but the trace length bound will stop the loop
                while (trace.last().isCovered)
                    trace.add(nextNode.coveringNode!!)
            }

            // for each new covered node added there is a chance that a new EC has been created
            while (checkForMEC.isNotEmpty()) {
                // the covered node then must be part of the EC, so it is enough to perform EC search on the subgraph
                // reachable from this node
                // this also means that at most one new EC can exist (which might be a superset of an existing one)
                val node = checkForMEC.first()

                val mec = findMEC(node)
                val edgesLeavingMEC = mec.flatMap {
                    it.getOutgoingEdges().filter {
                        it.targetList.any { it.second !in mec }
                    }
                }
                if (mergeSameSCNodes && mec.size == 1) {
                    val zero =
                        (goal == Goal.MIN && mec.first().getOutgoingEdges().any { it !in edgesLeavingMEC })
                                || (mec.first()._isExpanded && edgesLeavingMEC.isEmpty())
                    if (zero)
                        U[mec.first()] = 0.0
                    merged[node] = mec to edgesLeavingMEC
                }
                if (mec.size > 1) {
                    val zero =
                        goal == Goal.MIN || (edgesLeavingMEC.isEmpty() && mec.all { it._isExpanded || it.isCovered })
                    for (n in mec) {
                        merged[n] = mec to edgesLeavingMEC
                        if (zero) U[n] = 0.0
                    }
                }
                checkForMEC.removeAll(mec)
            }

            val Unew = HashMap(U)
            val Lnew = HashMap(L)
            // value propagation using the merged map
            for (node in trace.reversed().distinct()) {
                if (node.isCovered) {
                    Unew[node] = U.getValue(node.coveringNode!!)
                    Lnew[node] = L.getValue(node.coveringNode!!)
                } else {
                    // TODO: based on rewards
                    var unew = if (Unew[node] == 0.0) 0.0 else (goal.select(
                        merged[node]!!.second.map {
                            it.target.expectedValue { U.getValue(it.second) }
                        }
                    ) ?: 1.0)
                    var lnew = if (Lnew[node] == 1.0) 1.0 else (goal.select(
                        merged[node]!!.second.map { it.target.expectedValue { L.getValue(it.second) } }
                    ) ?: 0.0)
                    require(unew >= lnew)

                    if (useMonotonicBellman) {
                        unew = minOf(unew, Unew[node]!!)
                        lnew = maxOf(lnew, Lnew[node]!!)
                    }

                    for (siblingNode in merged[node]!!.first) {
                        Unew[siblingNode] = unew
                        Lnew[siblingNode] = lnew
                    }
                }
            }
            U = Unew
            L = Lnew
        }
        println(
            "All nodes: ${reachedSet.size}\n" +
                    "Non-covered nodes: ${reachedSet.filterNot { it.isCovered }.size}\n" +
                    "Real covers: ${reachedSet.filter { it.isCovered && it.coveringNode!!.sc != it.sc }.size}\n" +
                    "Result range: [${L[initNode]}, ${U[initNode]}], d=${U[initNode]!! - L[initNode]!!}"
        )
        timer.stop()
        println("Total time (ms): ${timer.elapsed(TimeUnit.MILLISECONDS)}")

        return U[initNode]!!
    }

    fun brtdpWithGameRefinement(
        successorSelection:
        StochasticGame<Node, Edge>.(
            currNode: Node,
            L: Map<Node, Double>,
            U: Map<Node, Double>,
            goal: Goal
        ) -> Node,
        threshold: Double = 1e-7
    ): Double {
        require(useMayStandard)
        require(!useMustStandard) { "Not implemented for lower-cover yet" }

        reset()
        val timer = Stopwatch.createStarted()
        val initNode = Node(initState, topInit)

        waitlist.add(initNode)

        val reachedSet = arrayListOf(initNode)
        val scToNode = hashMapOf(initNode.sc to arrayListOf(initNode))
        var UFull = hashMapOf(initNode to 1.0)
        var LFull = hashMapOf(initNode to 0.0)
        var UTrapped = hashMapOf(initNode to 1.0)
        var LTrapped = hashMapOf(initNode to 0.0)


        // virtually merged end components, also maintaining a set of edges that leave the EC for each of them
        val mergedFull = hashMapOf(initNode to (setOf(initNode) to initNode.getOutgoingEdges()))
        val mergedTrapped = hashMapOf(initNode to (setOf(initNode) to initNode.getOutgoingEdges()))
        val checkForMEC = hashSetOf<Node>()

        fun resetMerging(nodes: Collection<Node>) {
            for (node in nodes) {
                mergedFull[node] = setOf(node) to node.getOutgoingEdges()
                checkForMEC.add(node)
            }
            for (node in nodes) {
                mergedTrapped[node] = setOf(node) to node.getOutgoingEdges()
                    .filter { it.surelyEnabled }
            }
        }

        fun onUncover(n: Node) {
            if (resetOnUncover) {
                UFull[n] = 1.0
                UTrapped[n] = 1.0
                LFull[n] = 0.0
                LTrapped[n] = 0.0
            }
            resetMerging(mergedFull[n]!!.first)
        }

        var i = 0
        var refinable = true

        val gameFull = VirtuallyMergedMDP(initNode, mergedFull)
        val gameTrapped = VirtuallyMergedMDP(initNode, mergedTrapped)

        // Use the largest difference of the 4 approximations for stopping
        while (
            (goal == Goal.MAX && UFull[initNode]!! - LTrapped[initNode]!! > threshold) ||
            (goal == Goal.MIN && UTrapped[initNode]!! - LFull[initNode]!! > threshold)
        ) {
            // logging for experiments
            i++
            if (i % 1000 == 0)
                if (verboseLogging) {
                    println(
                        "$i: " +
                                "nodes: ${reachedSet.size}, non-covered: ${reachedSet.size - numCoveredNodes}, " +
                                " real covers: $numRealCovers " +
                                "[${LTrapped[initNode]}, ${UTrapped[initNode]}], d=${UTrapped[initNode]!! - LTrapped[initNode]!!}, " +
                                "[${LFull[initNode]}, ${UFull[initNode]}], d=${UFull[initNode]!! - LFull[initNode]!!}, " +
                                "time (ms): ${timer.elapsed(TimeUnit.MILLISECONDS)}"
                    )
                }

            //----------------------------------------------------------------------------------------------------------

            // simulate a single trace
            val trace = arrayListOf(initNode)
            checkForMEC.clear()

            // TODO: probability-based bound for trace length (see learning algorithms paper)
            GenerateTrace@ while (
                !((trace.last()._isExpanded && trace.last().getOutgoingEdges()
                    .isEmpty()) || (trace.size > reachedSet.size * 3))
            ) {
                val lastNode = trace.last()
                if (!lastNode._isExpanded) {
                    require(!lastNode.isCovered)
                    val (newlyDiscovered, revisited) = expand(
                        lastNode,
                        getStdCommands(lastNode.sc),
                        getErrorCommands(lastNode.sc),
                        if (mergeSameSCNodes) scToNode else null
                    )
                    if (mergeSameSCNodes) {
                        checkForMEC.addAll(revisited)
                    }

                    require(mergedFull[lastNode]!!.first.size == 1)
                    require(mergedTrapped[lastNode]!!.first.size == 1)
                    // as the node has just been expanded, its outgoing edges have been changed,
                    // so the merged map needs to be updated as well
                    if (mergedFull[lastNode]!!.first.size == 1)
                        mergedFull[lastNode] = setOf(lastNode) to lastNode.getOutgoingEdges()
                    if (mergedTrapped[lastNode]!!.first.size == 1)
                        mergedTrapped[lastNode] = setOf(lastNode) to lastNode.getOutgoingEdges()
                            .filter { it.surelyEnabled }

                    for (newNode in newlyDiscovered) {
                        newNode.onUncover = ::onUncover

                        // treating each node as its own EC at first so that value computations can be done
                        // solely based on the _merged_ map
                        mergedFull[newNode] = setOf(newNode) to newNode.getOutgoingEdges() //this should always be empty
                        mergedTrapped[newNode] = setOf(newNode) to newNode.getOutgoingEdges()
                            .filter { it.surelyEnabled } //this will be "even more empty" should always be empty
                        close(newNode, reachedSet, scToNode)
                        reachedSet.add(newNode)
                        scToNode.getOrPut(newNode.sc) { arrayListOf() }.add(newNode)
                        if (newNode.isCovered) {
                            checkForMEC.add(newNode)
                            UFull[newNode] = UFull[newNode.coveringNode]!!
                            LFull[newNode] = LFull[newNode.coveringNode]!!
                            UTrapped[newNode] = UTrapped[newNode.coveringNode]!!
                            LTrapped[newNode] = LTrapped[newNode.coveringNode]!!
                        } else {
                            UFull[newNode] = 1.0
                            UTrapped[newNode] = 1.0
                            LFull[newNode] = 0.0
                            LTrapped[newNode] = 0.0
                        }
                    }

                    if(goal == Goal.MIN && lastNode.mayBeError) {
                        UTrapped[lastNode] = 1.0
                        LTrapped[lastNode] = 1.0
                    } else if (goal == Goal.MAX && !lastNode.mustBeError) {
                        UTrapped[lastNode] = 0.0
                        LTrapped[lastNode] = 0.0
                    }

                    if (newlyDiscovered.isEmpty() && revisited.isEmpty()) {
                        // marking as error node is done during expanding the node,
                        // so the node might have become an error node since starting the core
                        if (lastNode.isErrorNode) {
                            LFull[lastNode] = 1.0
                            LTrapped[lastNode] = 1.0
                        }
                        // absorbing nodes can never lead to an error node
                        else {
                            UFull[lastNode] = 0.0
                            UTrapped[lastNode] = 0.0
                        }
                        break@GenerateTrace
                    }
                    if (!lastNode.isErrorNode &&
                        goal == Goal.MAX &&
                        lastNode.getOutgoingEdges().none { it.surelyEnabled }
                    ) {
                        // The node is absorbing in the trapped MDP
                        UTrapped[lastNode] = 0.0
                    }
                }

                // stop if a non-exitable MEC is reached
                if (mergedFull[lastNode]!!.second.isEmpty())
                    break@GenerateTrace

                val nextNode =
                    if (UFull[initNode]!! - LFull[initNode]!! > UTrapped[initNode]!! - LTrapped[initNode]!!
                        || mergedTrapped[lastNode]!!.second.isEmpty()
                    )
                        gameFull.successorSelection(lastNode, LFull, UFull, goal)
                    else
                        gameTrapped.successorSelection(lastNode, LTrapped, UTrapped, goal)


                trace.add(nextNode)
                // this would lead to infinite traces in MECs, but the trace length bound will stop the loop
                while (trace.last().isCovered)
                    trace.add(trace.last().coveringNode!!)
            }


            val UFullnew = HashMap(UFull)
            val UTrappednew = HashMap(UTrapped)
            val LFullnew = HashMap(LFull)
            val LTrappednew = HashMap(LTrapped)

            // for each new covered node added there is a chance that a new EC has been created
            updateMECs(checkForMEC, mergedFull, mergedTrapped, UFullnew, UTrappednew)

            // value propagation using the merged map
            for (node in trace.reversed().distinct()) {
                if (node.isCovered) {
                    UFullnew[node] = UFull.getValue(node.coveringNode!!)
                    UTrappednew[node] = UTrapped.getValue(node.coveringNode!!)
                    LFullnew[node] = LFull.getValue(node.coveringNode!!)
                    LTrappednew[node] = LTrapped.getValue(node.coveringNode!!)
                } else {
                    // TODO: based on rewards
                    var ufullnew =
                        if (UFullnew[node] == 0.0) 0.0
                        else if (mergedFull[node]!!.let { (mecFull, edgesLeavingMEC) ->
                                (mergeSameSCNodes && mecFull.size == 1
                                    && ((goal == Goal.MIN && node.getOutgoingEdges().any { it !in edgesLeavingMEC })
                                    || (node._isExpanded && edgesLeavingMEC.isEmpty())))
                                        || (mecFull.size > 1 && (goal == Goal.MIN || (edgesLeavingMEC.isEmpty() && mecFull.all { it._isExpanded || it.isCovered })))
                        }) 0.0 //TODO: this is ugly, and it is written at least 3 times in this file
                        else (goal.select(
                        mergedFull[node]!!.second.map {
                            it.target.expectedValue { UFull.getValue(it.second) }
                        }
                    ) ?: 1.0)
                    var utrappednew =
                        if (UTrappednew[node] == 0.0) 0.0
                        else if (node.isErrorNode || (!node._isExpanded && !node.isCovered)) 1.0
                        else if (goal == Goal.MIN && node.mayBeError) 1.0
                        else if (
                            node._isExpanded &&
                            goal == Goal.MIN && mergedTrapped[node]!!.first.size == 1
                            && mergedTrapped[node]!!.second.isEmpty()
                            && mergedFull[node]!!.second.isNotEmpty()
                        ) 1.0 // Only trappable actions possible, and the trap is a target when MIN-ing
                        else (goal.select(
                            mergedTrapped[node]!!.second.map {
                                it.target.expectedValue { UTrapped.getValue(it.second) }
                            }
                        ) ?: 0.0)
                    var lfullnew =
                        if (LFullnew[node] == 1.0) 1.0
                        else if (
                            goal == Goal.MIN && (mergedFull[node]!!.first.size > 1
                                    || node.getOutgoingEdges().any { it !in mergedFull[node]!!.second })
                        ) 0.0
                        else (goal.select(
                            mergedFull[node]!!.second.map { it.target.expectedValue { LFull.getValue(it.second) } }
                        ) ?: 0.0)
                    var ltrappednew =
                        if (LTrappednew[node] == 1.0) 1.0
                        else if(goal == Goal.MIN && node.mayBeError) 1.0
                        else if (
                            goal == Goal.MIN && (mergedTrapped[node]!!.first.size > 1
                                    || node.getOutgoingEdges()
                                .any { it.surelyEnabled && it !in mergedTrapped[node]!!.second })
                        ) 0.0
                        else if (
                            node._isExpanded &&
                            goal == Goal.MIN && mergedTrapped[node]!!.first.size == 1
                            && mergedTrapped[node]!!.second.isEmpty()
                            && mergedFull[node]!!.second.isNotEmpty()
                        ) 1.0 // Only trappable actions possible, and the trap is a target when MIN-ing
                        else (goal.select(
                            mergedTrapped[node]!!.second.map { it.target.expectedValue { LTrapped.getValue(it.second) } }
                        ) ?: 0.0)

                    require(ufullnew >= lfullnew) {"Node ${node.id} Full : $lfullnew - $ufullnew "}
                    require(utrappednew >= ltrappednew) {"Node ${node.id} Trapped : $ltrappednew - $utrappednew "}
                    require((goal == Goal.MIN && ltrappednew >= lfullnew)||(goal == Goal.MAX && utrappednew <= ufullnew))

                    if (useMonotonicBellman) {
                        ufullnew = minOf(ufullnew, UFullnew[node]!!)
                        utrappednew = minOf(utrappednew, UTrappednew[node]!!)
                        lfullnew = maxOf(lfullnew, LFullnew[node]!!)
                        ltrappednew = maxOf(ltrappednew, LTrappednew[node]!!)
                    }

                    for (siblingNode in mergedFull[node]!!.first) {
                        UFullnew[siblingNode] = ufullnew
                        LFullnew[siblingNode] = lfullnew
                    }
                    for (siblingNode in mergedTrapped[node]!!.first) {
                        UTrappednew[siblingNode] = utrappednew
                        LTrappednew[siblingNode] = ltrappednew
                    }
                }
            }
            UFull = UFullnew
            UTrapped = UTrappednew
            LFull = LFullnew
            LTrapped = LTrappednew

            val abstractionDiff =
                Math.abs((UFull[initNode]!! + LFull[initNode]!!) / 2 - (UTrapped[initNode]!! + LTrapped[initNode]!!)) / 2
            val abstractionGapLarger =
                refinable &&
                (abstractionDiff > (UFull[initNode]!! - LFull[initNode]!!)
                        && abstractionDiff > (UTrapped[initNode]!! - LTrapped[initNode]!!))
            val boundsConverged =
                (UFull[initNode]!!-LFull[initNode]!!) < threshold/2
                        && (UTrapped[initNode]!!-LTrapped[initNode]!!) < threshold/2
            val shouldRefineGame = abstractionGapLarger
            //val shouldRefineGame = boundsConverged
            if (shouldRefineGame) {
                val selectFrom = trappedReachable(initNode) // TODO: UPDATE THIS DURING EXPLO/REFINEMENT, DO NOT RECOMPUTE
                val maxDiffNode = selectFrom.filter {
                    it.getOutgoingEdges().any { !it.surelyEnabled }
                            || (it.mustBeError != it.mayBeError)
                }.maxByOrNull {
                    // Both terms would be halved for averaging, but argmax is preserved
                    (UFull[it]!! + LFull[it]!!) - (UTrapped[it]!! - LTrapped[it]!!)
                }
                if(maxDiffNode == null) {
                    refinable = false
                    continue
                }
                println("Refined node: ${maxDiffNode.id}")
                refineGameNode(maxDiffNode, UFull)
                /*
                TODO("handle the consequences of error refinement - the rewards changed in trapped," +
                        "the LFull for MAX / UFull for MIN is no longer a valid approx (even without error refinement, only" +
                        "standard game ref), but without proper reward handling, copying trapped to full will never converge, " +
                        "even if it is still a valid approx")
                 */
                if (goal == Goal.MAX) {
                    // reset the upper approximations in the trapped MDP as it is no longer an upper approx
                    // the upper approx of the full MDP is still valid, so we set it to that instead of a trivial approx
                    // similar goes for the lower approximation and the trapped lower approximation
                    UTrapped.putAll(UFull)
                    LFull.putAll(LTrapped)
                } else {
                    // same but flipped for MIN
                    LTrapped.putAll(LFull)
                    //TODO("resetting UFull might be needed, but they have different rewards, so this makes it inconsistent (e.g. it easily becomes all 1)")
                    UFull.putAll(UTrapped)
                }

                // recompute MECs:
                // covers have been removed -> less MECs
                // new edges have appeared in the trapped MDP -> more MECs

                val mec = mergedTrapped[maxDiffNode]!!.first
                resetMerging(mec)

                // strengthenings might have removed covers, and the new surelyEnabled edges can create new MECs in the trapped MDP
                updateMECs(checkForMEC, mergedFull, mergedTrapped, UFull, UTrapped)

                // No need to reset U and L here, as the game-based refinement is done through a regular strengthening operation,
                // which resets them for the appropriate nodes

            }
        }
        println(
            "final stats: " +
                    "nodes: ${reachedSet.size}, non-covered: ${reachedSet.filterNot { it.isCovered }.size}, " +
                    " real covers: ${reachedSet.filter { it.isCovered && it.coveringNode!!.sc != it.sc }.size} " +
                    "[${LTrapped[initNode]}, ${UTrapped[initNode]}], d=${UTrapped[initNode]!! - LTrapped[initNode]!!}" +
                    "[${LFull[initNode]}, ${UFull[initNode]}], d=${UFull[initNode]!! - LFull[initNode]!!}"
        )
        timer.stop()
        println("Total time (ms): ${timer.elapsed(TimeUnit.MILLISECONDS)}")

        // Midpoint of the midpoints
        return (UFull[initNode]!! + LFull[initNode]!! + UTrapped[initNode]!! + LTrapped[initNode]!!) / 4
    }

    private fun updateMECs(
        newCovered: HashSet<Node>,
        mergedFull: HashMap<Node, Pair<Set<Node>, List<Edge>>>,
        mergedTrapped: HashMap<Node, Pair<Set<Node>, List<Edge>>>,
        UFull: HashMap<Node, Double>,
        UTrapped: HashMap<Node, Double>
    ) {
        while (newCovered.isNotEmpty()) {
            // the covered node then must be part of the EC, so it is enough to perform EC search on the subgraph
            // reachable from this node
            // this also means that at most one new EC can exist (which might be a superset of an existing one)
            val node = newCovered.first()

            val mecFull = findMEC(node)
            val edgesLeavingMEC = mecFull.flatMap {
                it.getOutgoingEdges().filter { it.targetList.any { it.second !in mecFull } }
            }
            if (mergeSameSCNodes && mecFull.size == 1) {
                // mecFull == { node }
                val zero =
                    (goal == Goal.MIN && node.getOutgoingEdges().any { it !in edgesLeavingMEC })
                            || (node._isExpanded && edgesLeavingMEC.isEmpty())
                if (zero)
                    UFull[node] = 0.0
                mergedFull[node] = mecFull to edgesLeavingMEC
            }
            if (mecFull.size > 1) {
                val zero =
                    goal == Goal.MIN || (edgesLeavingMEC.isEmpty() && mecFull.all { it._isExpanded || it.isCovered })
                for (n in mecFull) {
                    mergedFull[n] = mecFull to edgesLeavingMEC
                    if (zero) UFull[n] = 0.0
                }
            }
            newCovered.removeAll(mecFull)

            val checkForTrappedMec = mecFull.toMutableSet()
            while (checkForTrappedMec.isNotEmpty()) {
                val node = checkForTrappedMec.first()
                val mecTrapped = findMEC(node) {
                    if(goal == Goal.MIN && it.mayBeError) listOf()
                    else it.getOutgoingEdges().filter { it.surelyEnabled }
                }
                val edgesLeavingMECTrapped = mecTrapped.flatMap {
                    it.getOutgoingEdges().filter { it.surelyEnabled && it.targetList.any { it.second !in mecTrapped } }
                }
                if (mergeSameSCNodes && mecTrapped.size == 1) {
                    val zero =
                        (goal == Goal.MIN && mecTrapped.first().getOutgoingEdges()
                            .any { it.surelyEnabled && it !in edgesLeavingMECTrapped })
                                || (
                                goal == Goal.MAX &&
                                        mecTrapped.first()._isExpanded &&
                                        edgesLeavingMECTrapped.isEmpty() &&
                                        edgesLeavingMEC.isEmpty()
                                )
                    if (zero)
                        UTrapped[mecTrapped.first()] = 0.0
                    mergedTrapped[node] = mecTrapped to edgesLeavingMECTrapped
                }
                if (mecTrapped.size > 1) {
                    val zero =
                        goal == Goal.MIN || (edgesLeavingMECTrapped.isEmpty() && mecTrapped.all { it._isExpanded || it.isCovered })
                    for (n in mecTrapped) {
                        mergedTrapped[n] = mecTrapped to edgesLeavingMECTrapped
                        if (zero) UTrapped[n] = 0.0
                    }
                }
                checkForTrappedMec.removeAll(mecTrapped)
            }
        }
    }


    fun fullyExpanded(
        useBVI: Boolean = false,
        threshold: Double,
        extractKeys: (SA) -> List<*> = { _ -> listOf(null) },
        timeout: Int = 0,
    ): Double {
        reset()
        val timer = Stopwatch.createStarted()

        //val reachedSet = hashSetOf(initNode)
        val (reachedSet, scToNode, initNode) = explore(extractKeys, timeout, timer, mergeSameSCNodes)

        timer.stop()
        val explorationTime = timer.elapsed(TimeUnit.MILLISECONDS)
        println("Exploration time (ms): $explorationTime")
        val nodes = reachedSet.getAll()

        println("All nodes: ${nodes.size}")
        println("Non-covered nodes: ${nodes.count { !it.isCovered }}")
        println("Strict covers: $numRealCovers")
        timer.reset()
        timer.start()
        val errorProb =
            if (useGameRefinement) computeErrorProbWithRefinement(
                initNode, reachedSet, scToNode, useBVI, threshold, threshold
            )
            else computeErrorProb(initNode, nodes, useBVI, threshold).first
        timer.stop()
        val probTime = timer.elapsed(TimeUnit.MILLISECONDS)
        println("Probability computation time (ms): $probTime")
        println("Total time (ms): ${explorationTime + probTime}")
        return errorProb
    }

    fun fullyExpandedWithDebugInfo(
        useBVI: Boolean = false,
        threshold: Double,
        extractKeys: (SA) -> List<*> = { _ -> listOf(null) },
    ): Pair<Double, Pair<PARG, Map<Node, Double>>> {
        val (reachedSet, scToNode, initNode) = explore(extractKeys, 0, Stopwatch.createStarted(), mergeSameSCNodes)
        val nodes = reachedSet.getAll()

        return if (useGameRefinement) TODO()
        else computeErrorProb(initNode, nodes, useBVI, threshold)
    }

    private inner class ExplorationResult(
        val reachedSet: TrieReachedSet<Node, Any>,
        val scToNode: MutableMap<SC, ArrayList<Node>>,
        val initNode: Node
    ) {
        operator fun component1() = reachedSet
        operator fun component2() = scToNode
        operator fun component3() = initNode
    }

    private fun explore(
        extractKeys: (SA) -> List<*>,
        timeout: Int,
        timer: Stopwatch,
        mergeSameSCNodes: Boolean
    ): ExplorationResult {
        reset()
        val initNode = Node(initState, topInit)
        waitlist.add(initNode)
        val reachedSet = TrieReachedSet<Node, Any> {
            extractKeys(it.sa)
        }
        reachedSet.add(initNode)
        currReachedSet = reachedSet
        val scToNode = hashMapOf(initNode.sc to arrayListOf(initNode))

        while (!waitlist.isEmpty()) {
            if (timeout != 0 && timer.elapsed(TimeUnit.MILLISECONDS) > timeout)
                throw RuntimeException("Timeout")
            val n = waitlist.removeFirst()
            require(!n.isCovered)
            close(n, reachedSet, scToNode)
            if (n.isCovered) continue
            val (newlyDiscovered, revisited) = expand(
                n,
                getStdCommands(n.sc),
                getErrorCommands(n.sc),
                if (mergeSameSCNodes) scToNode else hashMapOf()
            )
            for (newNode in newlyDiscovered) {
                if (newNode.isCovered)
                    continue
                close(newNode, reachedSet, scToNode)
                if (newNode.sc in scToNode) {
                    scToNode[newNode.sc]!!.add(newNode)
                } else {
                    scToNode[newNode.sc] = arrayListOf(newNode)
                }
                if (!newNode.isCovered) {
                    if (newNode !in waitlist) waitlist.addFirst(newNode)
                } else {
                    waitlist.remove(newNode)
                }
                reachedSet.add(newNode)
            }
        }
        return ExplorationResult(reachedSet, scToNode, initNode)
    }

    private fun expand(
        n: Node,
        stdCommands: Collection<ProbabilisticCommand<A>>,
        errorCommands: Collection<ProbabilisticCommand<A>>,
        scToNode: Map<SC, List<Node>>? = null
    ): ExpansionResult<Node> {

        val negatedCommands = arrayListOf<ProbabilisticCommand<A>>()
        val nonNegatedCommands = arrayListOf<ProbabilisticCommand<A>>()
        for (cmd in errorCommands) {
            if (domain.isEnabled(n.sc, cmd)) {
                n.markAsErrorNode()
                n.mayBeError = true
                if (useMustTarget && !domain.mustBeEnabled(n.sa, cmd)) {
                    n.strengthenAgainstCommand(cmd, true)
                }
                if(useGameRefinement && domain.mustBeEnabled(n.sa, cmd)) {
                    n.mustBeError = true
                    n.mustSatErrors.add(cmd)
                }

                return ExpansionResult(emptyList(), emptyList()) // keep error nodes absorbing
            } else if (useMayTarget && domain.mayBeEnabled(n.sa, cmd)) {
                nonNegatedCommands.add(cmd)
            } else if (useGameRefinement && useMustTarget && domain.mayBeEnabled(n.sa, cmd)) {
                n.mayBeError = true
                n.maySatErrors.add(cmd)
            }
        }
        val newlyDiscovered = arrayListOf<Node>()
        val revisited = hashSetOf<Node>()
        for (cmd in stdCommands) {
            if (domain.isEnabled(n.sc, cmd)) {
                val target = cmd.result.transform { a ->
                    val nextState = domain.concreteTransFunc(n.sc, a)
                    if (scToNode != null
                        && nextState in scToNode
                        && scToNode[nextState]!!.isNotEmpty()
                    ) {
                        val revisNode = scToNode[nextState]!!.first()
                        revisited.add(revisNode)
                        a to revisNode
                    } else {
                        val newNode =
                            Node(nextState, domain.topAfter(n.sa, a))
                        newlyDiscovered.add(newNode)
                        // TODO: move scToNode updates here
                        a to newNode
                    }
                }
                if (useMustStandard && !domain.mustBeEnabled(n.sa, cmd)) {
                    negatedCommands.add(cmd)
                }

                val surelyEnabled =
                    !useGameRefinement || ( // don't care about it if we don't use game refinement
                            (useMayStandard && useMustStandard) || // if an Exact-PARG is built, then the standard refinement takes care of it
                                    (useMayStandard && domain.mustBeEnabled(n.sa, cmd)) ||
                                    (useMustStandard && domain.mayBeEnabled(n.sa, cmd)))

                n.createEdge(target, cmd.guard, surelyEnabled, cmd)
            } else if (useMayStandard && domain.mayBeEnabled(n.sa, cmd)) {
                nonNegatedCommands.add(cmd)
            }
        }
        if (negatedCommands.isNotEmpty() || nonNegatedCommands.isNotEmpty())
            n.strengthenAgainstCommands(negatedCommands, nonNegatedCommands)

        n._isExpanded = true

        for (node in revisited) {
            if (node._isExpanded) {
                node.strengthenParents()
            }
        }

        return ExpansionResult(newlyDiscovered, revisited.toList())
    }

    private fun close(node: Node, reachedSet: Collection<Node>, scToNode: Map<SC, List<Node>>) {
        scToNode[node.sc]?.find { it != node && !it.isCovered }?.let {
            node.coverWith(it)
            node.strengthenForCovering()
            return
        }
        for (otherNode in reachedSet) {
            if (otherNode != node && !otherNode.isCovered && domain.checkContainment(node.sc, otherNode.sa)) {
                node.coverWith(otherNode)
                node.strengthenForCovering()
                break
            }
        }
    }

    private fun close(node: Node, reachedSet: TrieReachedSet<Node, *>, scToNode: Map<SC, List<Node>>) {
        require(!node.isCovered)
        scToNode[node.sc]?.find { it != node && !it.isCovered }?.let {
        //scToNode[node.sc]?.find { it != node && it.isExpanded() }?.let {
            node.coverWith(it)
            node.strengthenForCovering()
            return
        }
        for (otherNode in reachedSet.get(node)) {
            if (otherNode != node && !otherNode.isCovered && domain.checkContainment(node.sc, otherNode.sa)) {
            //if (otherNode != node && otherNode.isExpanded() && domain.checkContainment(node.sc, otherNode.sa)) {
                node.coverWith(otherNode)
                node.strengthenForCovering()
                break
            }
        }
    }


    abstract inner class PARGAction
    inner class EdgeAction(val e: Edge) : PARGAction() {
        override fun toString(): String {
            return e.toString()
        }
    }

    private inner class CoverAction : PARGAction() {

        override fun toString() = "<<cover>>"
    }


    inner class PARG(
        val init: Node,
        val reachedSet: Collection<Node>
    ) : ImplicitStochasticGame<Node, PARGAction>() {
        override val initialNode: Node
            get() = init

        override fun getAvailableActions(node: Node) =
            if (node.isCovered) listOf(CoverAction()) else node.getOutgoingEdges().map(::EdgeAction)

        override fun getResult(node: Node, action: PARGAction) =
            if (action is EdgeAction) action.e.target.transform { it.second }
            else dirac(node.coveringNode!!)

        override fun getPlayer(node: Node): Int = 0 // This is an MDP
    }

    private fun computeErrorProb(
        initNode: Node,
        reachedSet: Collection<Node>,
        useBVI: Boolean,
        threshold: Double
    ): Pair<Double, Pair<PARG, Map<Node, Double>>> {

        val parg = PARG(initNode, reachedSet)
        val rewardFunction = TargetRewardFunction<Node, PARGAction> { it.isErrorNode && !it.isCovered }
        val timer = Stopwatch.createStarted()
        val initializer =
            if (useQualitativePreprocessing)
                MDPAlmostSureTargetInitializer(parg, goal) { it.isErrorNode && !it.isCovered }
            else TargetSetLowerInitializer { it.isErrorNode && !it.isCovered }
        val quantSolver: StochasticGameSolver<Node, PARGAction> =
            if (useBVI) MDPBVISolver(threshold)
            else VISolver(threshold, useGS = false)

        val analysisTask = AnalysisTask(parg, { goal }, rewardFunction)
        val nodes = parg.getAllNodes()
        println("All nodes: ${nodes.size}")
        println("Non-covered nodes: ${nodes.filter { !it.isCovered }.size}")

        if (initializer.isKnown(parg.initialNode)) {
            timer.stop()
            val probTime = timer.elapsed(TimeUnit.MILLISECONDS)
            println("Precomputation sufficient, result: ${initializer.initialLowerBound(parg.initialNode)}")
            println("Probability computation time (ms): $probTime")
            return initializer.initialLowerBound(parg.initialNode) to (parg to parg.getAllNodes().associateWith { initializer.initialLowerBound(it) })
        }

        val values = quantSolver.solve(analysisTask, initializer)
        timer.stop()
        val probTime = timer.elapsed(TimeUnit.MILLISECONDS)
        println("Probability computation time (ms): $probTime")

        return (values[initNode]!! to (parg to values))
    }

    inner class TrappedPARG(
        val init: Node,
        val reachedSet: Collection<Node>
    ) : ImplicitStochasticGame<Node, PARGAction>() {
        override val initialNode: Node
            get() = init

        override fun getAvailableActions(node: Node) =
            if (node.isCovered) listOf(CoverAction())
            else if(goal == Goal.MIN && node.mayBeError)
                listOf() // made virtually absorbing
            else node.getOutgoingEdges().filter {
                it.surelyEnabled
            }.map(::EdgeAction)

        override fun getResult(node: Node, action: PARGAction) =
            if (action is EdgeAction) action.e.target.transform { it.second }
            else dirac(node.coveringNode!!)

        override fun getPlayer(node: Node): Int = 0 // This is an MDP

        override fun getAllNodes(): Collection<Node> {
            return reachedSet
        }
    }

    private fun computeErrorProbWithRefinement(
        initNode: Node,
        reachedSet: TrieReachedSet<Node, Any>,
        scToNode: MutableMap<SC, ArrayList<Node>>,
        useBVI: Boolean,
        innerThreshold: Double,
        outerThreshold: Double
    ): Double {
        val reachedNodes = reachedSet.getAll()
        var parg = PARG(initNode, reachedNodes)
        var trappedParg = TrappedPARG(initNode, reachedNodes)

        fun isFullTarget(it: Node) =
            (it.isErrorNode && !it.isCovered)

        fun isTrappedTarget(it: Node) =
            (it.isErrorNode && !it.isCovered && (goal != Goal.MAX || it.mustBeError))
                    // When the original goal is minimization, the trap node is also a target;
                    // this means that the concrete player will still never want to choose an action which might be trapped,
                    // but unlike in the maximization case, we need to deal with this when it has no other choice
                    || (goal == Goal.MIN &&
                        it.getOutgoingEdges().none { it.surelyEnabled } &&
                        !it.getOutgoingEdges().all { e -> e.targetList.size == 1 && e.targetList.first().second == it })
                    || (goal == Goal.MIN && it.mayBeError)

        val fullRewardFunction = TargetRewardFunction<Node, PARGAction> { isFullTarget(it) }
        val trappedRewardFunction = TargetRewardFunction<Node, PARGAction> { isTrappedTarget(it) }
        lateinit var fullInitializer: SGSolutionInitializer<Node, PARGAction>
        lateinit var trappedInitializer: SGSolutionInitializer<Node, PARGAction>

        var baseFullInitializer =
            if (useQualitativePreprocessing)
                MDPAlmostSureTargetInitializer(parg, goal) { isFullTarget(it) }
            else TargetSetLowerInitializer { isFullTarget(it) }
        var baseTrappedInitializer =
            if (useQualitativePreprocessing)
                MDPAlmostSureTargetInitializer(trappedParg, goal) { isTrappedTarget(it) }
            else TargetSetLowerInitializer { isTrappedTarget(it) }
        fullInitializer = baseFullInitializer
        trappedInitializer = baseTrappedInitializer

        while (true) {
            val fullAnalysisTask = AnalysisTask(parg, { goal }, fullRewardFunction)
            val trappedAnalysisTask = AnalysisTask(trappedParg, { goal }, trappedRewardFunction)

            lateinit var trappedValues: Map<Node, Double>
            lateinit var fullValues: Map<Node, Double>

            if (useBVI) {
                val fullSolver = MDPBVISolver<Node, PARGAction>(innerThreshold)
                val trappedSolver = MDPBVISolver<Node, PARGAction>(innerThreshold)

                val (Lfull, Ufull) = fullSolver.solveWithRange(fullAnalysisTask, fullInitializer)
                val (Ltrapped, Utrapped) = trappedSolver.solveWithRange(trappedAnalysisTask, trappedInitializer)

                // TODO: strategies
                val lowerApprox =
                    if (goal == Goal.MAX) Ltrapped
                    else Lfull
                val upperApprox =
                    if (goal == Goal.MAX) Ufull
                    else Utrapped
                trappedInitializer =
                    FallbackInitializer(
                        lowerApprox, upperApprox, baseTrappedInitializer, innerThreshold, mapOf()
                    )
                fullInitializer =
                    FallbackInitializer(
                        lowerApprox, upperApprox, baseFullInitializer, innerThreshold, mapOf()
                    )
                // TODO: MIN should use [Lfull, Utrapped]?
                trappedValues = Ltrapped
                fullValues = Ufull
            } else {
                val fullSolver = VISolver<Node, PARGAction>(innerThreshold)
                val trappedSolver = VISolver<Node, PARGAction>(innerThreshold)

                val Lfull = fullSolver.solve(fullAnalysisTask, fullInitializer)
                val Ltrapped = trappedSolver.solve(trappedAnalysisTask, trappedInitializer)

                val lowerApprox =
                    if (goal == Goal.MIN) Lfull
                    else Ltrapped

                trappedInitializer =
                    FallbackInitializer(
                        lowerApprox, hashMapOf(), baseTrappedInitializer, innerThreshold, mapOf()
                    )
                fullInitializer =
                    FallbackInitializer(
                        lowerApprox, hashMapOf(), baseFullInitializer, innerThreshold, mapOf()
                    )
                trappedValues = Ltrapped
                fullValues = Lfull
            }

            println("Init node val: [${trappedValues[initNode]}, ${fullValues[initNode]}] ")

            if (Math.abs(fullValues[initNode]!! - trappedValues[initNode]!!) < outerThreshold)
                return (fullValues[initNode]!! + trappedValues[initNode]!!) / 2

            // TODO: try other refinement strategies
            // - closest or weightedMaxDiff instead of maxDiff
            // - constrain to strategy-reachable or optimal-reachable nodes
            refineMenuGame(reachedSet, scToNode, trappedValues, fullValues, trappedReachable(initNode))
            val reachedNodes = reachedSet.getAll()
            parg = PARG(initNode, reachedNodes)
            trappedParg = TrappedPARG(initNode, reachedNodes)
            baseFullInitializer =
                if (useQualitativePreprocessing)
                    MDPAlmostSureTargetInitializer(parg, goal, ::isFullTarget)
                else TargetSetLowerInitializer(::isFullTarget)
            baseTrappedInitializer =
                if (useQualitativePreprocessing)
                    MDPAlmostSureTargetInitializer(trappedParg, goal, ::isTrappedTarget)
                else TargetSetLowerInitializer(::isTrappedTarget)
        }
    }

    private fun trappedReachable(initNode: Node): Collection<Node> {
        // TODO: cache/compute iteratively
        val res = hashSetOf(initNode)
        val waitlist: Queue<Node> = ArrayDeque()
        waitlist.add(initNode)
        while (!waitlist.isEmpty()) {
            val node = waitlist.remove()
            if (node.isCovered) {
                if (node.coveringNode !in res) {
                    res.add(node.coveringNode!!)
                    waitlist.add(node.coveringNode)
                }
            } else {
                for (edge in node.getOutgoingEdges()) {
                    if (!edge.surelyEnabled) continue
                    for ((_, child) in edge.targetList) {
                        if (child !in res) {
                            res.add(child)
                            waitlist.add(child)
                        }
                    }
                }
            }
        }
        return res
    }

    fun refineMenuGame(
        reachedSet: TrieReachedSet<Node, Any>,
        scToNode: MutableMap<SC, ArrayList<Node>>,
        lowerValues: Map<Node, Double>,
        upperValues: Map<Node, Double>,
        allowedNodes: Collection<Node>
    ) {
        require(allowedNodes.isNotEmpty())
        val maxDiffNode = allowedNodes.filter {
            it.getOutgoingEdges().any { !it.surelyEnabled }
                    || (it.mustBeError != it.mayBeError)
        }.maxByOrNull {
            upperValues[it]!! - lowerValues[it]!!
        }!!
        println("Refined node: ${maxDiffNode.id}")

        refineGameNode(maxDiffNode, upperValues)
        while (!waitlist.isEmpty()) {
            val n = waitlist.removeFirst()
            val (newlyDiscovered, revisited) = expand(
                n,
                getStdCommands(n.sc),
                getErrorCommands(n.sc),
            )
            for (newNode in newlyDiscovered) {
                close(newNode, reachedSet, scToNode)
                if (newNode.sc in scToNode) {
                    scToNode[newNode.sc]!!.add(newNode)
                } else {
                    scToNode[newNode.sc] = arrayListOf(newNode)
                }
                if (!newNode.isCovered) {
                    waitlist.addFirst(newNode)
                }
                reachedSet.add(newNode)
            }
        }
    }

    private fun refineGameNode(
        nodeToRefine: Node,
        fullValues: Map<Node, Double>
    ) {
        if(nodeToRefine.mustBeError != nodeToRefine.mayBeError) {
            // Error refinement
            if(nodeToRefine.isErrorNode) {
                for (maySatError in nodeToRefine.maySatErrors.toList()) {
                    nodeToRefine.strengthenAgainstCommand(maySatError, negate = true)
                }
                // TODO: conv to set or remove duplicates?
                nodeToRefine.mustSatErrors.addAll(nodeToRefine.maySatErrors)
                nodeToRefine.mayBeError = true
            } else {
                for (maySatError in nodeToRefine.maySatErrors.toList()) {
                    nodeToRefine.strengthenAgainstCommand(maySatError)
                }
                nodeToRefine.maySatErrors.clear()
                nodeToRefine.mayBeError = false
            }
            return
        }

        // Standard refinement
        fun selectOptimalEdges(): List<Edge> {
            val edgeValues =
                nodeToRefine.getOutgoingEdges().associateWith { it.target.expectedValue { fullValues[it.second]!! } }
            val opt = goal.select(edgeValues.values)
            return nodeToRefine.getOutgoingEdges().filter { edgeValues[it] == opt }
        }

        val edgesToRefine =
            when (refinementStrategy) {
                EdgeRefinementStrategy.ALL_EDGES -> nodeToRefine.getOutgoingEdges()
                EdgeRefinementStrategy.OPTIMAL_EDGES -> selectOptimalEdges()
                EdgeRefinementStrategy.SINGLE_EDGE -> selectOptimalEdges().subList(0, 1)
            }
        for (outgoingEdge in edgesToRefine) {
            if (!outgoingEdge.surelyEnabled) {
                nodeToRefine.strengthenAgainstCommand(outgoingEdge.relatedCommand, negate = true)
                outgoingEdge.makeSurelyEnabled()
            }
        }
    }

}