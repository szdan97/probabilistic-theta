package hu.bme.mit.theta.prob.analysis.menuabstraction

import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.probabilistic.StochasticGame

object firstRefinable: PivotSelectionStrategy {
    override fun <S : State, A : Action> selectPivot(
        sg: StochasticGame<MenuGameNode<S, A>, MenuGameAction<S, A>>,
        refinableNodes: List<MenuGameNode.StateNode<S, A>>,
        valueFunctionMax: Map<MenuGameNode<S, A>, Double>,
        valueFunctionMin: Map<MenuGameNode<S, A>, Double>,
        strategyMax: Map<MenuGameNode<S, A>, MenuGameAction<S, A>>,
        strategyMin: Map<MenuGameNode<S, A>, MenuGameAction<S, A>>
    ): MenuGameNode.StateNode<S, A> {
        return refinableNodes.first()
    }
}