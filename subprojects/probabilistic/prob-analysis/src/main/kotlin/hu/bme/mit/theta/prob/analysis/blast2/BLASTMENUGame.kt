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

sealed class BLASTMENUGameNode<D : ExprState, A : StmtAction, P : Prec>(val player: Int, open val origin: Any):
BLASTGameNode<BLASTMENUGameNode<D,A,P>, MENUUnit<D,A,P>, D, A, P, BLASTMENUGameAction<D,A,P>>
{
    abstract fun isTarget(originalGoal: Goal, abstractionGoal: Goal): Boolean

    data class StateNode<D : ExprState, A : StmtAction, P : Prec>(override val origin: MENUUnit<D, A, P>) :
        BLASTMENUGameNode<D, A, P>(P_CONCRETE, origin) {
        override fun isTarget(originalGoal: Goal, abstractionGoal: Goal) = origin.isTarget(originalGoal, abstractionGoal)
        override fun getAvailableActions(): List<BLASTMENUGameAction<D, A, P>> =
            if (origin.isCovered()) listOf(BLASTMENUGameAction.CoverAction())
            else origin.intermediateNodes.keys.map {
                BLASTMENUGameAction.CommandAction(
                    it
                )
            }

        override fun getResult(action: BLASTMENUGameAction<D,A,P>): FiniteDistribution<BLASTMENUGameNode<D,A,P>> {
            if(action is BLASTMENUGameAction.CoverAction<D,A,P> && origin.isCovered())
                return dirac(StateNode(origin.getCoverer()!!))
            if (action is BLASTMENUGameAction.CommandAction<D, A, P>) {
                val origin = origin.intermediateNodes[action.command]
                    ?: throw IllegalArgumentException("getResult called with disabled action $action on node $this")
                val wrapped = IntermediateNode(origin)
                return dirac(wrapped)
            }
            throw IllegalArgumentException("getResult called with disabled action $action on node $this")
        }

        override fun getOriginUnit() = origin

        override fun computeNumericRefinement(
            L: Map<BLASTMENUGameNode<D, A, P>, Double>,
            LStrategy: Map<BLASTMENUGameNode<D, A, P>, BLASTMENUGameAction<D, A, P>>,
            U: Map<BLASTMENUGameNode<D, A, P>, Double>,
            UStrategy: Map<BLASTMENUGameNode<D, A, P>, BLASTMENUGameAction<D, A, P>>,
            tolerance: Double
        ): Expr<BoolType> {
            if(origin.mayBeTarget() != origin.mustBeTarget()) TODO()

            val itmNodeToRefine = getOptimalRefinableIntermediateNodes(L, LStrategy, U, UStrategy, tolerance).maxByOrNull {
                U[it]!! - L[it]!!
            }!!

            // TODO: this only leads to meaningful progress if the trap node (or a value-equivalent result)
            //  is actually chosen by the strategy where the refined itmNode is optimal
            if (itmNodeToRefine.origin.canTrap) return itmNodeToRefine.origin.command.guard

            val diff = itmNodeToRefine.minMaxChoiceDifference(L, LStrategy, U, UStrategy, tolerance)
            // As for now, we will only consider a single choice, as all choices would have to be considered separately,
            // which cannot be done by returning a single expression. The result of the related refinement can be either:
            // - the choice is spurious, so it is eliminated
            // - the choice is concretizable, which means (assuming deterministic assignements) it is the ONLY concretizable one,
            //  so all the others are eliminated, as the abstraction choices must be disjoint
            val choiceToConsider = diff.first()
            val wps = (choiceToConsider as BLASTMENUGameAction.ResultAction<D,A,P>).result.support.map {
                WpState.of((it.second as StateNode).origin.stateLabel.toExpr()).wep(
                    Stmts.SequenceStmt(
                        listOf(Stmts.Assume(itmNodeToRefine.origin.command.guard))+(it.first?.stmts ?: listOf())
                    )
                ).expr
            }
            return SmartBoolExprs.And(wps)
        }

        override fun isRefinable(
            L: Map<BLASTMENUGameNode<D, A, P>, Double>,
            LStrategy: Map<BLASTMENUGameNode<D, A, P>, BLASTMENUGameAction<D, A, P>>,
            U: Map<BLASTMENUGameNode<D, A, P>, Double>,
            UStrategy: Map<BLASTMENUGameNode<D, A, P>, BLASTMENUGameAction<D, A, P>>,
            tolerance: Double
        ): Boolean {
            if(origin.isCovered()) return false
            if(U[this]!!-L[this]!! < tolerance) return false
            val optimalItmNodes = getOptimalRefinableIntermediateNodes(L, LStrategy, U, UStrategy, tolerance)
            return optimalItmNodes.any()
        }

        private fun getOptimalRefinableIntermediateNodes(
            L: Map<BLASTMENUGameNode<D, A, P>, Double>,
            LStrategy: Map<BLASTMENUGameNode<D, A, P>, BLASTMENUGameAction<D, A, P>>,
            U: Map<BLASTMENUGameNode<D, A, P>, Double>,
            UStrategy: Map<BLASTMENUGameNode<D, A, P>, BLASTMENUGameAction<D, A, P>>,
            tolerance: Double
        ) = getAvailableActions().filter {
            (abs(U[getResult(it).support.first()]!!-U[this]!!) <= tolerance
                    || abs(L[getResult(it).support.first()]!!-L[this]!!) <= tolerance)
                    && (getResult(it).support.first() as IntermediateNode).itmNodeRefinable(L, LStrategy, U, UStrategy, tolerance)
        }.map { getResult(it).support.first() as IntermediateNode<D,A,P> } // TODO: a lot of redundant getResult() calls

    }

    data class IntermediateNode<D : ExprState, A : StmtAction, P : Prec>(override val origin: MENUUnit<D, A, P>.IntermediateNode) :
        BLASTMENUGameNode<D, A, P>(P_ABSTRACTION, origin) {
        override fun isTarget(originalGoal: Goal, abstractionGoal: Goal)= false
        override fun getAvailableActions(): List<BLASTMENUGameAction<D, A, P>> {
            // TODO: TrapNode should be unique
            val optTrap =
                if (origin.canTrap) listOf(dirac((null as A?) to (TrapNode<D,A,P>() as BLASTMENUGameNode<D,A,P>)))
                else listOf()
            val realResults =
                origin.successorDistros.map { it.transform {
                    it.first as A? to StateNode(it.second) as BLASTMENUGameNode<D,A,P>
                } }
            val combined = optTrap + realResults
            return combined.map { BLASTMENUGameAction.ResultAction(it) }
        }

        fun minMaxChoiceDifference(
            L: Map<BLASTMENUGameNode<D, A, P>, Double>,
            LStrategy: Map<BLASTMENUGameNode<D, A, P>, BLASTMENUGameAction<D, A, P>>,
            U: Map<BLASTMENUGameNode<D, A, P>, Double>,
            UStrategy: Map<BLASTMENUGameNode<D, A, P>, BLASTMENUGameAction<D, A, P>>,
            tolerance: Double
        ): Set<BLASTMENUGameAction<D,A,P>> {
            val abstractionChoices = getAvailableActions()
            val UExpected = abstractionChoices.associateWith {
                getResult(it).expectedValue { U[it]!! }
            }
            val LExpected = abstractionChoices.associateWith {
                getResult(it).expectedValue { L[it]!! }
            }
            val max = abstractionChoices.maxOf { UExpected[it]!! }
            val min = abstractionChoices.minOf { LExpected[it]!! }
            val maxChoices = abstractionChoices.filter {
                abs(UExpected[it]!!-max) < tolerance
            }
            val minChoices = abstractionChoices.filter {
                abs(LExpected[it]!!-min) < tolerance
            }
            if(maxChoices != minChoices)
                return maxChoices.minus(minChoices) union minChoices.minus(maxChoices)
            else return setOf()
        }

        override fun getResult(action: BLASTMENUGameAction<D,A,P>):
                FiniteDistribution<BLASTMENUGameNode<D, A, P>> {
            if(action is BLASTMENUGameAction.ResultAction<D,A,P>)
                return action.result.transform { it.second }
            else throw IllegalArgumentException("getResult called with disabled action $action on node $this")
        }

        fun itmNodeRefinable(
            L: Map<BLASTMENUGameNode<D, A, P>, Double>,
            LStrategy: Map<BLASTMENUGameNode<D, A, P>, BLASTMENUGameAction<D, A, P>>,
            U: Map<BLASTMENUGameNode<D, A, P>, Double>,
            UStrategy: Map<BLASTMENUGameNode<D, A, P>, BLASTMENUGameAction<D, A, P>>,
            tolerance: Double
        ) = minMaxChoiceDifference(L, LStrategy, U, UStrategy, tolerance).isNotEmpty()

    }

    class TrapNode<D : ExprState, A : StmtAction, P : Prec> : BLASTMENUGameNode<D, A, P>(P_ABSTRACTION, "TRAP") {
        private val hashcode = TrapNode::class.hashCode()
        override fun isTarget(originalGoal: Goal, abstractionGoal: Goal) = originalGoal == Goal.MIN
        override fun getAvailableActions(): List<BLASTMENUGameAction<D, A, P>> = listOf()
        override fun getResult(action: BLASTMENUGameAction<D, A, P>): FiniteDistribution<BLASTMENUGameNode<D, A, P>> {
            throw IllegalArgumentException("getResult called with disabled action $action on node $this")
        }

        override fun equals(other: Any?): Boolean {
            return other is TrapNode<*,*,*>
        }

        override fun hashCode(): Int {
            return hashcode
        }
    }

    override fun toString() = origin.toString()

    // TODO: should this be cached?
    abstract fun getAvailableActions(): List<BLASTMENUGameAction<D,A,P>>
    abstract fun getResult(action: BLASTMENUGameAction<D,A,P>): FiniteDistribution<BLASTMENUGameNode<D,A,P>>
}
fun <D : ExprState,A : StmtAction,P : Prec> createBLASTMENUGameRewardFun(originalGoal: Goal, abstractionGoal: Goal) =
    TargetRewardFunction<BLASTMENUGameNode<D,A,P>, BLASTMENUGameAction<D,A,P>> {
        it.isTarget(
            originalGoal,
            abstractionGoal
        )
    }

sealed class BLASTMENUGameAction<D : ExprState, A : StmtAction, P : Prec> {
    data class CommandAction<D : ExprState, A : StmtAction, P : Prec>(val command: ProbabilisticCommand<A>) :
        BLASTMENUGameAction<D, A, P>()

    data class ResultAction<D : ExprState, A : StmtAction, P : Prec>(
        val result: FiniteDistribution<Pair<A?, BLASTMENUGameNode<D, A, P>>>
    ) : BLASTMENUGameAction<D, A, P>()

    class CoverAction<D : ExprState, A : StmtAction, P : Prec>: BLASTMENUGameAction<D,A,P>() {
        override fun toString() = "COVER"
    }
}

class BlastMenuGame<D : ExprState, A : StmtAction, P : Prec>(initialUnit: MENUUnit<D, A, P>) :
    ImplicitStochasticGame<BLASTMENUGameNode<D, A, P>, BLASTMENUGameAction<D, A, P>>() {
    //private val trap: BLASTMENUGameNode<D, A, P> = BLASTMENUGameNode.TrapNode<D, A, P>()
    //private val dtrap = dirac(trap)
    //private val coverAction = BLASTMENUGameAction.CoverAction<D,A,P>()
    override fun getPlayer(node: BLASTMENUGameNode<D, A, P>) = node.player

    override val initialNode = BLASTMENUGameNode.StateNode(initialUnit)

    override fun getResult(
        node: BLASTMENUGameNode<D, A, P>,
        action: BLASTMENUGameAction<D, A, P>
    ) = node.getResult(action)

    override fun getAvailableActions(node: BLASTMENUGameNode<D, A, P>) =
        node.getAvailableActions()
}