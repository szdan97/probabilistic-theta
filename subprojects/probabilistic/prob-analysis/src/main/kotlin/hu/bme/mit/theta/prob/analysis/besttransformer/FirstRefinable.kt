package hu.bme.mit.theta.prob.analysis.besttransformer

import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.probabilistic.StochasticGame

object firstRefinable: PivotSelectionStrategy {
    override fun <S : State, A : Action> selectPivot(
        sg: StochasticGame<BestTransformerAbstractor.BestTransformerGameNode<S, A>, BestTransformerAbstractor.BestTransformerGameAction<S, A>>,
        refinableNodes: List<BestTransformerAbstractor.BestTransformerGameNode.AbstractionChoiceNode<S, A>>,
        valueFunctionMax: Map<BestTransformerAbstractor.BestTransformerGameNode<S, A>, Double>,
        valueFunctionMin: Map<BestTransformerAbstractor.BestTransformerGameNode<S, A>, Double>,
        strategyMax: Map<BestTransformerAbstractor.BestTransformerGameNode<S, A>, BestTransformerAbstractor.BestTransformerGameAction<S, A>>,
        strategyMin: Map<BestTransformerAbstractor.BestTransformerGameNode<S, A>, BestTransformerAbstractor.BestTransformerGameAction<S, A>>
    ): BestTransformerAbstractor.BestTransformerGameNode.AbstractionChoiceNode<S, A> {
        return refinableNodes.first()
    }
}