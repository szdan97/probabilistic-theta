package hu.bme.mit.theta.prob.analysis.menuabstraction

import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.prob.analysis.P_ABSTRACTION
import hu.bme.mit.theta.prob.analysis.P_CONCRETE
import hu.bme.mit.theta.prob.analysis.ProbabilisticCommand

sealed class MenuGameNode<S : State, A : Action>(val player: Int) {
    class StateNode<S : State, A : Action>(
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
    ) : MenuGameNode<S, A>(P_CONCRETE) {
        init {
            require(maxReward == minReward || rewardSplitExpr != null || rewardExpr != null) {
                "If maximal and minimal rewards are not the same, then either a reward split expression or a reward expression is needed"
            }
        }

        override fun toString(): String {
            return "StateNode(s=$s)"
        }

    }

    class ResultNode<S : State, A : Action>(
        val s: S, val a: ProbabilisticCommand<A>
    ) : MenuGameNode<S, A>(P_ABSTRACTION) {
        override fun toString(): String {
            return "ResultNode(s=$s, a=$a)"
        }
    }

    class TrapNode<S : State, A : Action> : MenuGameNode<S, A>(P_CONCRETE) {
        override fun toString(): String {
            return "TRAP"
        }
    }
}