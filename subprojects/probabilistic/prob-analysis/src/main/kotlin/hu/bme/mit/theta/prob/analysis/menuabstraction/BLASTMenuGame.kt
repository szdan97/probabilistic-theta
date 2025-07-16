package hu.bme.mit.theta.prob.analysis.menuabstraction

import hu.bme.mit.theta.analysis.InitFunc
import hu.bme.mit.theta.analysis.PartialOrd
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.prob.analysis.ProbabilisticCommandLTS
import hu.bme.mit.theta.probabilistic.FiniteDistribution
import hu.bme.mit.theta.probabilistic.FiniteDistribution.Companion.dirac
import hu.bme.mit.theta.probabilistic.StochasticGame
import hu.bme.mit.theta.probabilistic.gamesolvers.ExpandableNode
import hu.bme.mit.theta.probabilistic.gamesolvers.ExpansionResult
import java.util.*

class BLASTMenuGame<S : ExprState, A : StmtAction, P : Prec>(
    val lts: ProbabilisticCommandLTS<S, A>,
    val init: InitFunc<S, P>,
    val transFunc: MenuGameTransFunc<S, A, P>,
    val targetExpr: Expr<BoolType>,
    val maySatisfy: (S, Expr<BoolType>) -> Boolean,
    val mustSatisfy: (S, Expr<BoolType>) -> Boolean,
    val initialPrec: P,
    val ord: PartialOrd<S>,
    val extendPrec: P.(P) -> P
) : StochasticGame<MenuGameNode<S, A>, MenuGameAction<S, A>> {

    inner class BLASTMenuGameNode(
        val wrappedNode: MenuGameNode<S, A>,
        /**
         * The precision used when computing the post operator from this node
         */
        var supportPrecision: P
    ) : ExpandableNode<BLASTMenuGameNode> {
        val outgoingEdges = hashMapOf<MenuGameAction<S, A>, BLASTMenuGameTransitionEdge>()
        val incomingEdges = arrayListOf<BLASTMenuGameTransitionEdge>()

        var coveringNode: BLASTMenuGameNode? = null
        var coveredNodes: MutableList<BLASTMenuGameNode> = arrayListOf()
        fun isCovered() = coveringNode != null
        fun isComplete() = isCovered() || isExpanded()

        private var expanded = wrappedNode is MenuGameNode.TrapNode

        fun getLastCoverer(): BLASTMenuGameNode {
            var res = this
            while (true) res = res.coveringNode ?: return res
        }

        override fun isExpanded(): Boolean {
            return expanded
        }

        fun makeUnexpanded() {
            expanded = false
        }

        override fun expand(): ExpansionResult<BLASTMenuGameNode> {
            val newlyCreated = hashSetOf<BLASTMenuGameNode>()
            val revisited = hashSetOf<BLASTMenuGameNode>()
            for (action in this@BLASTMenuGame.getAvailableActions(this)) {
                if (action !in outgoingEdges) {
                    val expansionResult = expand(this, action)
                    newlyCreated.addAll(expansionResult.newlyCreated)
                }
            }
            expanded = true
            return ExpansionResult(newlyCreated.toList(), revisited.toList())
        }

        fun coverWith(coverer: BLASTMenuGameNode) {
            require(coverer != this)
            require(coveringNode == null)
            coveringNode = coverer
            coverer.coveredNodes.add(this)
        }

        fun removeCover() {
            require(coveringNode != null)
            coveringNode!!.coveredNodes.remove(this)
            coveringNode = null
        }

        fun extendSupportPrecision(newPrec: P) {
            supportPrecision = supportPrecision.extendPrec(newPrec)
        }
    }

    sealed class BLASTMenuGameAction
    object CoverAction: BLASTMenuGameAction()

    inner class BLASTMenuGameTransitionEdge(
        val wrappedAction: MenuGameAction<S, A>,
        val start: BLASTMenuGameNode,
        val end: FiniteDistribution<BLASTMenuGameNode>
    ): BLASTMenuGameAction()

    private fun createEdge(
        wrappedAction: MenuGameAction<S, A>,
        start: BLASTMenuGameNode,
        end: FiniteDistribution<BLASTMenuGameNode>
    ): BLASTMenuGameTransitionEdge {
        val newEdge = BLASTMenuGameTransitionEdge(wrappedAction, start, end)
        start.outgoingEdges[wrappedAction] = newEdge
        end.support.forEach { it.incomingEdges.add(newEdge) }
        return newEdge
    }

    private lateinit var _initialNode: BLASTMenuGameNode

    init {
        initialize(initialPrec)
    }

    private fun initialize(initialNodePrec: P) {
        val initState = init.getInitStates(initialNodePrec).first() // TODO: cannot handle multiple abstract inits yet
        val mayBeTarget = maySatisfy(initState, targetExpr)
        val mustBeTarget = mustSatisfy(initState, targetExpr)
        _initialNode = BLASTMenuGameNode(
            MenuGameNode.StateNode(
                initState,
                if (mayBeTarget) 1 else 0,
                if (mustBeTarget) 1 else 0,
                targetExpr,
                null,
                mustBeTarget
            ),
            initialNodePrec
        )
    }

    private fun createNode(wrappedNode: MenuGameNode<S, A>, supportPrecision: P): BLASTMenuGameNode {
        require(wrappedNode !in wrappedNodeMap)
        val newNode = BLASTMenuGameNode(wrappedNode, supportPrecision)
        nodes.add(newNode)
        wrappedNodeMap[wrappedNode] = newNode
        return newNode
    }

    val trapNode = MenuGameNode.TrapNode<S, A>()
    val trapDecision = MenuGameAction.EnterTrap<S, A>()
    val trapDirac = dirac(trapNode as MenuGameNode<S, A>)
    val blastTrapNode = BLASTMenuGameNode(trapNode, initialPrec)

    val nodes = arrayListOf(_initialNode, blastTrapNode)
    private val wrappedNodeMap = hashMapOf(
        _initialNode.wrappedNode to _initialNode,
        trapNode to blastTrapNode
    )
    val waitlist: Deque<BLASTMenuGameNode> = ArrayDeque<BLASTMenuGameNode>().apply { add(_initialNode) }

    override val initialNode: MenuGameNode<S, A>
        get() = _initialNode.wrappedNode

    override fun getPlayer(node: MenuGameNode<S, A>): Int = node.player

    inner class BLASTExpansionResult(
        val newEdge: BLASTMenuGameTransitionEdge,
        val newlyCreated: List<BLASTMenuGameNode>,
    )

    fun expand(
        node: BLASTMenuGameNode,
        action: MenuGameAction<S, A>
    ): BLASTExpansionResult {
        if (action in node.outgoingEdges) throw IllegalStateException("Node-action pair already explored!")
        val result = when (node.wrappedNode) {
            is MenuGameNode.StateNode -> when (action) {
                is MenuGameAction.AbstractionDecision -> throw IllegalArgumentException("Result called for unavailable action $action on node $node")
                is MenuGameAction.ChosenCommand -> dirac(
                    MenuGameNode.ResultNode(node.wrappedNode.s, action.command)
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
                        MenuGameNode.StateNode(
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
        val newlyCreated = arrayListOf<BLASTMenuGameNode>()
        val newEdge = createEdge(action, node, result.transform { menuGameNode ->
            if (menuGameNode == trapNode) blastTrapNode.also(newlyCreated::add)
            else createNode(menuGameNode, node.supportPrecision).also(newlyCreated::add)
        })
        return BLASTExpansionResult(newEdge, newlyCreated)
    }

    fun getAvailableActions(node: BLASTMenuGameNode): Collection<MenuGameAction<S, A>> {
        return when (node.wrappedNode) {
            is MenuGameNode.StateNode -> transFuncCache.getOrPut(node.wrappedNode to null) {
                if (node.wrappedNode.absorbing || node.wrappedNode.s.isBottom) listOf()
                else lts.getAvailableCommands(node.wrappedNode.s).map { MenuGameAction.ChosenCommand(it) }
            }

            is MenuGameNode.ResultNode -> {
                val prec: P = node.supportPrecision
                transFuncCache.getOrPut(node.wrappedNode to prec) {
                    val transFuncResult = transFunc.getNextStates(node.wrappedNode.s, node.wrappedNode.a, prec)
                    val res = transFuncResult.succStates.map {
                        MenuGameAction.AbstractionDecision<S, A>(it)
                    }
                    if (transFuncResult.canBeDisabled) res + trapDecision
                    else res
                }
            }

            is MenuGameNode.TrapNode -> listOf()
        }

    }

    override fun getResult(
        node: MenuGameNode<S, A>,
        action: MenuGameAction<S, A>
    ): FiniteDistribution<MenuGameNode<S, A>> {
        return (wrappedNodeMap[node]?.outgoingEdges?.get(action)?.end?.transform { it.getLastCoverer().wrappedNode })
            ?: throw IllegalStateException("node-action pair not available")
    }

    val transFuncCache = hashMapOf<Pair<MenuGameNode<S, A>, P?>, Collection<MenuGameAction<S, A>>>()
    override fun getAvailableActions(node: MenuGameNode<S, A>): Collection<MenuGameAction<S, A>> {
        val blastNode = wrappedNodeMap[node]!!
        require(blastNode.isExpanded() || blastNode.coveringNode != null) { "getAvailableActions can only be called on expanded nodes" }
        return blastNode.outgoingEdges.keys
    }

    fun fullyExplore() {
        while (!waitlist.isEmpty()) {
            val currNode = waitlist.remove()
            if (currNode == blastTrapNode) continue
            require(!currNode.isComplete())
            require(currNode in nodes)
            close(currNode)
            if (currNode.coveringNode == null) {
                val expansionResult = currNode.expand()
                waitlist.addAll(expansionResult.newlyDiscovered)
            }
        }
    }

    fun close(node: BLASTMenuGameNode) {
        // This differs from the original BLAST algorithm, as there was no covering node there
        // instead, it only marked the node as "covered" (in general, by all the other nodes)
        // and used timestamps to determine which nodes need to be unmarked after refinement
        // Pro for the original: a node can be covered by the union of other nodes instead of only one specific node
        //      and only one cover check is needed (although with a potentially larger formula,
        //      which needs to be often recomputed)
        // Con for the original: unmarking is less precise, and it might be much harder to implement the one-shot cover
        //      check for domains other than PRED
        if (node.wrappedNode is MenuGameNode.StateNode) {
            val coverer = nodes.find { node canBeCoveredBy it }
            if (coverer != null) {
                node.coverWith(coverer)
            }
        }
    }

    infix fun BLASTMenuGameNode.canBeCoveredBy(potentialCoverer: BLASTMenuGameNode): Boolean {
        if (this.wrappedNode is MenuGameNode.StateNode && potentialCoverer.wrappedNode is MenuGameNode.StateNode)
            return this != potentialCoverer
                    && potentialCoverer.coveringNode == null
                    && ord.isLeq(this.wrappedNode.s, potentialCoverer.wrappedNode.s)
        return false
    }

    // ****************
    // Refinement stuff
    // ****************

    private fun removeEdge(edge: BLASTMenuGameTransitionEdge) {
        edge.start.outgoingEdges.remove(edge.wrappedAction)
        if(nodes.contains(edge.start) && !waitlist.contains(edge.start))
            waitlist.add(edge.start)
        edge.start.makeUnexpanded()
        edge.end.support.forEach {
            it.incomingEdges.remove(edge)
            if (it.incomingEdges.isEmpty() && it != _initialNode) {
                removeNode(it)
            }
        }
    }

    private fun removeNode(node: BLASTMenuGameNode) {
        if (nodes.contains(node)) {
            nodes.remove(node)
            waitlist.remove(node) // the node might have been added to the waitlist during pruning, or it has not been explored yet if refinement is called during exploration
            wrappedNodeMap.remove(node.wrappedNode)
            // .toList calls to create a copy
            for (outgoingEdge in node.outgoingEdges.values.toList()) {
                removeEdge(outgoingEdge)
            }
            for (incomingEdge in node.incomingEdges.toList()) {
                removeEdge(incomingEdge)
            }
            for (coveredNode in node.coveredNodes.toList()) {
                coveredNode.removeCover()
            }
        }
    }

    private fun prune(node: MenuGameNode<S, A>) {
        if (node == initialNode) throw IllegalArgumentException("Should have called reinitialize instead")
        removeNode(wrappedNodeMap[node] ?: throw IllegalStateException("Node to prune does not exist"))
    }

    private fun reinitialize(newInitPrec: P) {
        nodes.clear()
        initialize(newInitPrec)
    }


    fun refine(refinementResult: MenuGameRefiner.RefinementResult<S, A, P>) {
        if (refinementResult.pivotNode == initialNode) {
            reinitialize(refinementResult.newPrec)
        } else {
            val parents = wrappedNodeMap[refinementResult.pivotNode]!!.incomingEdges.map { it.start }
            parents.forEach { it.extendSupportPrecision(refinementResult.newPrec) }
            // The original Lazy Abstraction paper describes the algorithm with an option to configure when the subtree
            // of the pivot node is kept, but it does not describe any specific strategies for it, and the discussion of
            // termination assumes that it is never kept; for now, we never keep it
            prune(refinementResult.pivotNode)
            TODO("the lack of information in the parent node might be problematic, especially in EXPL, as the newly introduced variable won't be known here. Check what Henzinger originally did")
            TODO("maybe propagate the refinement similarly to Kat10's local precision propagation methods?")
            TODO("also, as the path to a given node is always unambiguous in the reachability tree, and we only care about deterministic assignments for now, " +
                    "we can always add the information based on the concrete state at the end (~ASG), and propagate it backwards to make it an overapproximation")
            TODO("the original changes the support prec of only 1 node (the pivot node, which is the first that does not intersect with a backwards bad region), but by how logical refinement is performed, this is enough there." +
                    "Maybe what we should do with numerical refinement is marking one of the abstraction choices as the bad state and do the same backwards traversal from there? This would give us a different pivot node," +
                    "and it would lead to a very different refinement method than the original GBAR." +
                    "More specifically, is the following enough? Perform the traversal backwards from the choice of both strategies in the GB-pivot node, and let the BLAST-pivot-node be the first where" +
                    "a) not both of them intersect with the node's label or b) their intersection does not intersect with the node [IDK yet which of these is the correct one, if any]." +
                    "Also, could this be the idea behind using (seq-)interpolation in GBAR?")
        }
    }

    override fun getAllNodes(): Collection<MenuGameNode<S, A>> {
        return nodes.map { it.wrappedNode }
    }
}