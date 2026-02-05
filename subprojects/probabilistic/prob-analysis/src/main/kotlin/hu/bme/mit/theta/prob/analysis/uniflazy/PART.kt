package hu.bme.mit.theta.prob.analysis.uniflazy

import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.prob.analysis.ProbabilisticCommandLTS
import hu.bme.mit.theta.probabilistic.FiniteDistribution
import hu.bme.mit.theta.probabilistic.ImplicitStochasticGame
import hu.bme.mit.theta.probabilistic.StochasticGame

class PART<S : ExprState, A : StmtAction, P : Prec, R, L,
        GN: UnitGameNode<GA> /* Game Node type */, GA /* Game Action type */
        >(
    val root: PARTUnit<S, A, P, R, L, GN, GA>,
    val targetExpr: Expr<BoolType>,
    val initExpr: Expr<BoolType>,
    val lts: ProbabilisticCommandLTS<S, A>,
    val domain: Domain<S, A, P, R, L>,
    val buildingConfiguration: PARTBuildingConfiguration<S, A, P, R, L, GN, GA>
): ImplicitStochasticGame<GN,GA>() {
    val reached: MutableSet<PARTUnit<S, A, P, R, L, GN, GA>> = hashSetOf(root)
    val waitlist: MutableList<PARTUnit<S, A, P, R, L, GN, GA>> = arrayListOf(root)

    fun explorePART() {
        while (!waitlist.isEmpty()) {
            val uCurr = waitlist.removeFirst()
            buildingConfiguration.close(uCurr, reached)
            if(!uCurr.isCovered) {
                if(uCurr.mayBeTarget) {
                    val trace = uCurr.getTraceFromRoot()
                    val refinementResult = buildingConfiguration.concretizeOrRefine(trace, initExpr, targetExpr)
                    if(refinementResult is RefinementResult.Spurious<*, *, *, *, *, *, *>) {
                        if (uCurr !in reached) {
                            continue // Refinement removed the currently processed unit from the PART
                        }
                    } else {
                        // Do nothing and move on?
                    }
                }
                // Note: making a mayTarget absorbing even if it is not a mustTarget should not matter,
                // as the lower bound would be higher if it was expanded and a mustTarget was reached
                if(!uCurr.mayBeTarget)
                    uCurr.expand()
            }
        }
    }

    data class ToGameResult<S : ExprState, A : StmtAction, P : Prec, R, L, GN: UnitGameNode<GA>, GA>(
        val game: StochasticGame<GN, GA>, val unitToNodeMap: Map<PARTUnit<S, A, P, R, L, GN, GA>, GN>
    )
    fun toGame(): ToGameResult<S, A, P, R, L, GN, GA> {
        val unitToNodeMap = reached.associateWith { it.toGame() }
        return ToGameResult(this, unitToNodeMap)
    }

    // Stochastic Game Interpretation
    override val initialNode: GN
        get() = root.toGame()

    override fun getPlayer(node: GN) = node.getPlayer()

    override fun getResult(node: GN, action: GA): FiniteDistribution<GN> =
        // TODO: cast necessary without self-bounds with the current interfaces -- can we do better?
        //  replacing the specialized GN with UnitGameNode<GA> could work
        node.getResult(action).transform { it as GN }

    override fun getAvailableActions(node: GN) = node.getAvailableActions()
}

class PARTTrace<S : ExprState, A : StmtAction, P : Prec, R, L, GN: UnitGameNode<GA>, GA>(
    val units: List<PARTUnit<S, A, P, R, L, GN, GA>>,
    val actions: List<PARTUnit.GuardedAction<A>>
) {
    init {
        require(units.size == actions.size + 1)
    }
}