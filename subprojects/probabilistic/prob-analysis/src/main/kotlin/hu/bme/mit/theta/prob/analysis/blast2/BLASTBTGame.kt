package hu.bme.mit.theta.prob.analysis.blast2

import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.prob.analysis.P_ABSTRACTION
import hu.bme.mit.theta.prob.analysis.P_CONCRETE
import hu.bme.mit.theta.prob.analysis.ProbabilisticCommand
import hu.bme.mit.theta.probabilistic.FiniteDistribution
import hu.bme.mit.theta.probabilistic.FiniteDistribution.Companion.dirac
import hu.bme.mit.theta.probabilistic.Goal
import hu.bme.mit.theta.probabilistic.ImplicitStochasticGame
import hu.bme.mit.theta.probabilistic.TargetRewardFunction


fun <D : ExprState, A : StmtAction, P : Prec> createBLASTBTGameRewardFunction(
    originalGoal: Goal, abstractionGoal: Goal
) = TargetRewardFunction<BLASTBTGameNode<D,A,P>, BLASTBTGameAction<D, A, P>> {
    it is BLASTBTGameNode.StateNode && it.origin.isTarget(originalGoal, abstractionGoal)
}

sealed class BLASTBTGameNode<D : ExprState, A : StmtAction, P : Prec>(val player: Int, open val origin: Any):
BLASTGameNode<BLASTBTGameNode<D,A,P>, BTUnit<D,A,P>, D, A, P, BLASTBTGameAction<D,A,P>>{
    data class StateNode<D : ExprState, A : StmtAction, P : Prec>(override val origin: BTUnit<D, A, P>) :
        BLASTBTGameNode<D, A, P>(P_ABSTRACTION, origin) {
        override fun getOriginUnit() = origin

        override fun isRefinable(
            L: Map<BLASTBTGameNode<D, A, P>, Double>,
            LStrategy: Map<BLASTBTGameNode<D, A, P>, BLASTBTGameAction<D, A, P>>,
            U: Map<BLASTBTGameNode<D, A, P>, Double>,
            UStrategy: Map<BLASTBTGameNode<D, A, P>, BLASTBTGameAction<D, A, P>>,
            tolerance: Double
        ): Boolean {
            TODO()
        }

        override fun computeNumericRefinement(
            L: Map<BLASTBTGameNode<D, A, P>, Double>,
            LStrategy: Map<BLASTBTGameNode<D, A, P>, BLASTBTGameAction<D, A, P>>,
            U: Map<BLASTBTGameNode<D, A, P>, Double>,
            UStrategy: Map<BLASTBTGameNode<D, A, P>, BLASTBTGameAction<D, A, P>>
        ): Expr<BoolType> {
            TODO()
        }
    }

    data class IntermediateNode<D : ExprState, A : StmtAction, P : Prec>(override val origin: BTUnit<D, A, P>.IntermediateNode) :
        BLASTBTGameNode<D, A, P>(P_CONCRETE, origin)

    override fun toString() = origin.toString()
}

sealed class BLASTBTGameAction<D : ExprState, A : StmtAction, P : Prec> {
    data class EqClassAction<D : ExprState, A : StmtAction, P : Prec>(val intermediateNode: BTUnit<D, A, P>.IntermediateNode) :
        BLASTBTGameAction<D, A, P>() {
        override fun toString() = "EqClass"
    }

    data class CommandAction<D : ExprState, A : StmtAction, P : Prec>(val command: ProbabilisticCommand<A>) :
        BLASTBTGameAction<D, A, P>()

    class CoverAction<D : ExprState, A : StmtAction, P : Prec> : BLASTBTGameAction<D, A, P>() {
        override fun toString() = "COVER"
    }
}

class BLASTBTGame<D : ExprState, A : StmtAction, P : Prec>(val initialUnit: BTUnit<D, A, P>) :
    ImplicitStochasticGame<BLASTBTGameNode<D, A, P>, BLASTBTGameAction<D, A, P>>() {
    private val coverAction = BLASTBTGameAction.CoverAction<D, A, P>()

    override val initialNode = BLASTBTGameNode.StateNode(initialUnit)

    override fun getAvailableActions(node: BLASTBTGameNode<D, A, P>): Collection<BLASTBTGameAction<D, A, P>> {
        when (node) {
            is BLASTBTGameNode.IntermediateNode ->
                return node.origin.results.keys.map {
                    BLASTBTGameAction.CommandAction(it)
                }

            is BLASTBTGameNode.StateNode ->
                if (node.origin.isCovered()) return listOf(coverAction)
                else return node.origin.intermediateNodes.map {
                    BLASTBTGameAction.EqClassAction(it)
                }
        }
    }

    override fun getResult(
        node: BLASTBTGameNode<D, A, P>,
        action: BLASTBTGameAction<D, A, P>
    ): FiniteDistribution<BLASTBTGameNode<D, A, P>> {
        if (node is BLASTBTGameNode.StateNode) {
            if (action is BLASTBTGameAction.CoverAction && node.origin.isCovered())
                return dirac(BLASTBTGameNode.StateNode(node.origin.getCoverer()!!))
            if (action is BLASTBTGameAction.EqClassAction)
                return dirac(BLASTBTGameNode.IntermediateNode(action.intermediateNode)) // TODO: maybe check that the intermediate node really belongs to the unit?
        }

        if (node is BLASTBTGameNode.IntermediateNode
            && action is BLASTBTGameAction.CommandAction
        ) {
            return node.origin.results[action.command]
                ?.transform { BLASTBTGameNode.StateNode(it.second) }
                ?: throw IllegalArgumentException("getResult called with disabled action ")
        }

        throw IllegalArgumentException("getResult called with disabled action ")
    }

    override fun getPlayer(node: BLASTBTGameNode<D, A, P>) = node.player
}