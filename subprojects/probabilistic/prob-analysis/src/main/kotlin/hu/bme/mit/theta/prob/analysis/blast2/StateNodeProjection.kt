package hu.bme.mit.theta.prob.analysis.blast2

import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.core.stmt.Stmts
import hu.bme.mit.theta.prob.analysis.BasicStmtAction
import java.util.*

class ProjectedStateNode<D : ExprState, A : StmtAction, P : Prec>(
    val origin: PARTUnit<*, D, A, P>,
) {
    val state get() = origin.getState()
    val supportPrecision get() = origin.getSupportPrecision()

    val outgoingEdges = arrayListOf<StateNodeProjectionEdge<D, A, P>>()
    var incomingEdge: StateNodeProjectionEdge<D, A, P>? = null
    var coveringNode: ProjectedStateNode<D, A, P>? = null
    val coveredNodes = arrayListOf<ProjectedStateNode<D, A, P>>()

    fun getTraceFromRoot(): List<StateNodeProjectionEdge<D, A, P>> {
        if (this.incomingEdge == null) return listOf()
        val reverseTrace = arrayListOf(incomingEdge!!)
        while (true) {
            val nextEdge = reverseTrace.last().source.incomingEdge ?: break
            reverseTrace.add(nextEdge)
        }
        return reverseTrace.reversed()
    }

    fun removeSubtree(): RemovedAndUnlabeledNodes<ProjectedStateNode<D, A, P>> {
        val unmarkedNodes = hashSetOf<ProjectedStateNode<D, A, P>>()
        val removedNodes = hashSetOf<ProjectedStateNode<D, A, P>>()
        removeSubtreeHelper(removedNodes = removedNodes, unmarkedNodes = unmarkedNodes)
        origin.removeSubtree()
        return RemovedAndUnlabeledNodes(removedNodes = removedNodes, unmarkedNodes = unmarkedNodes)
    }

    /**
     * @param unmarkedNodes: this collection will be modified by adding the subtree root and the uncovered nodes to it and removing the removed nodes if they happen to be in it
     * @param removedNodes: this collection will be modified by adding the removed nodes into it
     */
    fun removeSubtreeHelper(
        removedNodes: MutableCollection<ProjectedStateNode<D, A, P>>,
        unmarkedNodes: MutableCollection<ProjectedStateNode<D, A, P>>
    ) {
        for (successor in getSuccessors()) {
            successor.removeSubtreeHelper(removedNodes = removedNodes, unmarkedNodes = unmarkedNodes)
            removedNodes.add(successor)
            unmarkedNodes.remove(successor)
            successor.coveringNode?.coveredNodes?.remove(successor)
            successor.coveredNodes.forEach {
                it.removeCover()
                if(it !in removedNodes) unmarkedNodes.add(it)
            }
        }
        unmarkedNodes.add(this)
    }

    fun getSuccessors() = outgoingEdges.map {
        it.end
    }

    fun removeCover() {
        coveringNode = null
    }

}

fun <U : PARTUnit<U, D, A, P>, D : ExprState, A : StmtAction, P : Prec> createFullStateNodeProjection(rootUnit: U): Map<U, ProjectedStateNode<D, A, P>> {
    val map = hashMapOf<U, ProjectedStateNode<D, A, P>>()
    val q = ArrayDeque<U>()
    q.add(rootUnit)
    map[rootUnit] = rootUnit.stateNodeProjection()
    while (q.isNotEmpty()) {
        val currUnit = q.pop()
        val currStateNode = map[currUnit]!!
        currUnit.ifCovered { coverer ->
            val covererStateNode = map.getOrPut(coverer) { coverer.stateNodeProjection() }
            currStateNode.coveringNode = covererStateNode
            covererStateNode.coveredNodes.add(currStateNode)
        }
        for ((guardaction, successorUnit) in currUnit.getSuccessorUnits()) {
            val (guard, action) = guardaction
            val successorNode = map.getOrPut(successorUnit) { successorUnit.stateNodeProjection() }
            map[successorUnit] = successorNode
            val guardedAction = BasicStmtAction(listOf(Stmts.Assume(guard)) + action.stmts)
            val edge = StateNodeProjectionEdge(currStateNode, successorNode, guardedAction)// guard, action)
            currStateNode.outgoingEdges.add(edge)
            successorNode.incomingEdge = edge
            q.add(successorUnit)
        }
    }
    return map
}

class StateNodeProjectionEdge<D : ExprState, A : StmtAction, P : Prec>(
    val source: ProjectedStateNode<D, A, P>,
    val end: ProjectedStateNode<D, A, P>,
    val action: BasicStmtAction
    //val guard: Expr<BoolType>,
    //val action: A
)