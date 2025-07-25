package hu.bme.mit.theta.prob.analysis.blast2

import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.core.stmt.Stmts
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs
import hu.bme.mit.theta.core.utils.WpState
import hu.bme.mit.theta.prob.analysis.P_ABSTRACTION
import hu.bme.mit.theta.prob.analysis.P_CONCRETE
import hu.bme.mit.theta.prob.analysis.ProbabilisticCommand
import hu.bme.mit.theta.probabilistic.FiniteDistribution
import hu.bme.mit.theta.probabilistic.FiniteDistribution.Companion.dirac
import hu.bme.mit.theta.probabilistic.Goal
import hu.bme.mit.theta.probabilistic.ImplicitStochasticGame
import hu.bme.mit.theta.probabilistic.TargetRewardFunction
import kotlin.math.abs


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
            if(origin.isCovered()) return false
            if(origin.mayBeTarget() != origin.mustBeTarget()) return true
            val diff = minMaxChoiceDifference(L, LStrategy, U, UStrategy, tolerance)
            return diff.first.isNotEmpty() || diff.second.isNotEmpty()
        }

        override fun computeNumericRefinement(
            L: Map<BLASTBTGameNode<D, A, P>, Double>,
            LStrategy: Map<BLASTBTGameNode<D, A, P>, BLASTBTGameAction<D, A, P>>,
            U: Map<BLASTBTGameNode<D, A, P>, Double>,
            UStrategy: Map<BLASTBTGameNode<D, A, P>, BLASTBTGameAction<D, A, P>>,
            tolerance: Double
        ): Expr<BoolType> {
            if (origin.mayBeTarget() != origin.mustBeTarget()) TODO()
            val diff = minMaxChoiceDifference(L, LStrategy, U, UStrategy, tolerance)

            val lowerChoice = getResult(
                diff.first.firstOrNull() ?: ((getAvailableActions()-diff.second).first())
            ).support.first() as IntermediateNode<D, A, P>
            val upperChoice = getResult(
                diff.second.firstOrNull() ?: ((getAvailableActions()-diff.first).first())
            ).support.first() as IntermediateNode<D, A, P>

            fun computeRefinement(commandAction: BLASTBTGameAction.CommandAction<D,A,P>) =
                SmartBoolExprs.And(
                    lowerChoice.origin.results[commandAction.command]!!.support.map { (action, result) ->
                        val stmt = Stmts.SequenceStmt(
                            listOf(Stmts.Assume(commandAction.command.guard)) + action.stmts
                        )
                        val wp = WpState.of(result.stateLabel.toExpr()).wep(stmt).expr
                        wp
                    }
                )


            for (commandAction in lowerChoice.getAvailableActions()) {
                val commandRelevant =
                    abs(lowerChoice.getResult(commandAction).expectedValue { L[it]!! } - L[this]!!) <= tolerance
                if (!commandRelevant) continue
                val commandAction = commandAction as BLASTBTGameAction.CommandAction
                if (commandAction.command !in upperChoice.origin.results) {
                    return commandAction.command.guard
                }
                return computeRefinement(commandAction)
            }

            for (commandAction in upperChoice.getAvailableActions()) {
                val commandRelevant =
                    abs(upperChoice.getResult(commandAction).expectedValue { U[it]!! } - U[this]!!) <= tolerance
                if (!commandRelevant) continue
                val commandAction = commandAction as BLASTBTGameAction.CommandAction
                if (commandAction.command !in lowerChoice.origin.results) {
                    return commandAction.command.guard
                }
                return computeRefinement(commandAction)
            }

            throw UnsupportedOperationException("Refinement unsuccessful")
        }

        private fun minMaxChoiceDifference(
            L: Map<BLASTBTGameNode<D, A, P>, Double>,
            LStrategy: Map<BLASTBTGameNode<D, A, P>, BLASTBTGameAction<D, A, P>>,
            U: Map<BLASTBTGameNode<D, A, P>, Double>,
            UStrategy: Map<BLASTBTGameNode<D, A, P>, BLASTBTGameAction<D, A, P>>,
            tolerance: Double
        ): Pair<List<BLASTBTGameAction<D, A, P>>, List<BLASTBTGameAction<D, A, P>>> {
            if (origin.isCovered()) throw RuntimeException("minMaxChoiceDifference")
            val lowerValue = L[this]!!
            val upperValue = U[this]!!
            val availableActions = this.getAvailableActions()
            val lowerOptimalChoices = availableActions.filter { choice ->
                abs(L[getResult(choice).support.first()]!! - lowerValue) <= tolerance
            }
            val upperOptimalChoices = availableActions.filter { choice ->
                abs(U[getResult(choice).support.first()]!! - upperValue) <= tolerance
            }
            return if (lowerOptimalChoices == upperOptimalChoices) (listOf<BLASTBTGameAction<D,A,P>>() to listOf())
            else lowerOptimalChoices.minus(upperOptimalChoices) to upperOptimalChoices.minus(lowerOptimalChoices)
        }

        override fun getAvailableActions(): List<BLASTBTGameAction<D, A, P>> {
            if (origin.isCovered()) return listOf(BLASTBTGameAction.CoverAction())
            else return origin.intermediateNodes.map {
                BLASTBTGameAction.EqClassAction(it)
            }
        }

        override fun getResult(action: BLASTBTGameAction<D,A,P>): FiniteDistribution<BLASTBTGameNode<D, A, P>> {
            if (action is BLASTBTGameAction.CoverAction && origin.isCovered())
                return dirac(StateNode(origin.getCoverer()!!))
            if (action is BLASTBTGameAction.EqClassAction)
                return dirac(IntermediateNode(action.intermediateNode)) // TODO: maybe check that the intermediate node really belongs to the unit?
            throw IllegalArgumentException("getResult called with disabled action ")
        }
    }

    data class IntermediateNode<D : ExprState, A : StmtAction, P : Prec>(override val origin: BTUnit<D, A, P>.IntermediateNode) :
        BLASTBTGameNode<D, A, P>(P_CONCRETE, origin) {
        override fun getAvailableActions(): List<BLASTBTGameAction<D, A, P>> {
            return origin.results.keys.map {
                BLASTBTGameAction.CommandAction(it)
            }
        }

        override fun getResult(action: BLASTBTGameAction<D, A, P>): FiniteDistribution<BLASTBTGameNode<D, A, P>> {

            if (action is BLASTBTGameAction.CommandAction) {
                return origin.results[action.command]
                    ?.transform { StateNode(it.second) }
                    ?: throw IllegalArgumentException("getResult called with disabled action ")
            }

            throw IllegalArgumentException("getResult called with disabled action ")
        }
    }

    override fun toString() = origin.toString()
    abstract fun getAvailableActions(): List<BLASTBTGameAction<D, A, P>>
    abstract fun getResult(action: BLASTBTGameAction<D,A,P>): FiniteDistribution<BLASTBTGameNode<D, A, P>>
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

    override fun getAvailableActions(node: BLASTBTGameNode<D, A, P>) =
        node.getAvailableActions()

    override fun getResult(
        node: BLASTBTGameNode<D, A, P>,
        action: BLASTBTGameAction<D, A, P>
    ) = node.getResult(action)

    override fun getPlayer(node: BLASTBTGameNode<D, A, P>) = node.player
}