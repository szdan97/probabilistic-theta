package hu.bme.mit.theta.prob.analysis.blast2

import hu.bme.mit.theta.analysis.PartialOrd
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.prob.analysis.ProbabilisticCommand
import hu.bme.mit.theta.prob.analysis.ProbabilisticCommandLTS
import hu.bme.mit.theta.prob.analysis.besttransformer.BestTransformerTransFunc
import hu.bme.mit.theta.probabilistic.FiniteDistribution

class BTUnit<D : ExprState, A : StmtAction, P : Prec>(
    state: D,
    supportPrec: P,
    partialOrder: PartialOrd<D>,
    val lts: ProbabilisticCommandLTS<D, A>,
    val transFunc: BestTransformerTransFunc<D, A, P>
) : BasicUnit<BTUnit<D, A, P>, D, A, P>(state, supportPrec, partialOrder) {

    inner class IntermediateNode(
        val results: Map<ProbabilisticCommand<A>, FiniteDistribution<Pair<A, BTUnit<D,A,P>>>>
    ) {

    }

    val intermediateNodes = arrayListOf<IntermediateNode>()

    override fun expand(prec: P): Collection<BTUnit<D, A, P>> {
        require(!isCovered()) {"Covered units should not be expanded!"}
        require(intermediateNodes.isEmpty()) {"Expanding already (partially) expanded BT units is not supported"}
        val commands = lts.getAvailableCommands(getState()).toList()
        val equivalenceClasses = transFunc.getNextStates(getState(), commands, prec)
        val successorUnits = arrayListOf<BTUnit<D,A,P>>()
        for (eqClass in equivalenceClasses) {
            val newNode = IntermediateNode(
                eqClass.toMap().mapValues { (key, value) ->
                    val resultWithUnits = value.transform {
                        val (action, state) = it
                        val successorUnit = BTUnit(
                            state, this.supportPrec,
                            this.partialOrder, this.lts, this.transFunc
                        )
                        successorUnits.add(successorUnit)
                        return@transform action to successorUnit
                    }
                    return@mapValues resultWithUnits
                }
            )
            intermediateNodes.add(newNode)
        }
        return successorUnits
    }

    // TODO: cache?
    override fun getSuccessorUnits(): Collection<Pair<Pair<Expr<BoolType>, A>, BTUnit<D, A, P>>> {
        return intermediateNodes.flatMap {
            it.results.flatMap { (command, result) ->
                result.support.map {
                    val (action, unit) = it
                    (command.guard to action) to unit
                }
            }
        }
    }

    override fun clearIntermediateNodes() {
        intermediateNodes.clear()
    }
}