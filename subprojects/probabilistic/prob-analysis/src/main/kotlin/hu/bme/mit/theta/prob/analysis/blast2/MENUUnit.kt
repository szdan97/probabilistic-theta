package hu.bme.mit.theta.prob.analysis.blast2

import hu.bme.mit.theta.analysis.PartialOrd
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.prob.analysis.ProbabilisticCommand
import hu.bme.mit.theta.prob.analysis.ProbabilisticCommandLTS
import hu.bme.mit.theta.prob.analysis.menuabstraction.MenuGameTransFunc
import hu.bme.mit.theta.probabilistic.FiniteDistribution

class MENUUnit<D : ExprState, A : StmtAction, P : Prec>(
    state: D,
    supportPrec: P,
    val incomingIntermediateNode: MENUUnit<D, A, P>.IntermediateNode?,

    // TODO: it is ugly to include model and domain stuff in the unit itself.
    //  maybe move these responsibilities to a MENUPARGBuilder or something like that
    //  for a first prototype, it's okay to put these here (famous last words...)
    partialOrder: PartialOrd<D>,
    val lts: ProbabilisticCommandLTS<D, A>,
    val transFunc: MenuGameTransFunc<D, A, P>,
    val maySatisfy: (D, Expr<BoolType>) -> Boolean,
) : BasicUnit<MENUUnit<D, A, P>, D, A, P>(state, supportPrec, partialOrder) {
    inner class IntermediateNode(
        var state: D,
        val command: ProbabilisticCommand<A>,
        val supportPrec: P,
    ) {
        var canTrap = false //maySatisfy(state, Not(command.guard))
        val successorDistros = arrayListOf<FiniteDistribution<Pair<A, MENUUnit<D, A, P>>>>()
        var isExpanded = false

        fun expand() {
            successorDistros.clear() // TODO: be less dumb
            val (nextDistros, canTrap) =
                this@MENUUnit.transFunc.getNextStates(state, command, supportPrec)
            successorDistros.addAll(
                nextDistros.map {
                    it.transform { (action, nextState) ->
                        action to MENUUnit(
                            nextState, supportPrec,
                            this,
                            partialOrder, lts, transFunc, maySatisfy
                        )
                    }
                }
            )
            this.canTrap = canTrap
            isExpanded = true
        }

        override fun toString(): String {
            return "(($state, $command) | $supportPrec)"
        }
    }

    val intermediateNodes = hashMapOf<ProbabilisticCommand<A>, IntermediateNode>()

    override fun expand(prec: P): Collection<MENUUnit<D, A, P>> {
        require(!isCovered()) {"Covered units should not be expanded!"}
        //TODO: "How will refinements be handled? Currently, if the state node is refined, calling expand will not automatically re-expand with the new state and support prec"
        for (command in lts.getAvailableCommands(stateLabel)) {
            if (maySatisfy(getState(), command.guard))
                intermediateNodes.computeIfAbsent(command) {
                    IntermediateNode(stateLabel, command, supportPrec).also { it.expand() }
                }
        }
        fullyExpanded = true
        return intermediateNodes.values.flatMap { it.successorDistros.flatMap { it.support.map { it.second } } }
    }

    // TODO: cache?
    override fun getSuccessorUnits(): Collection<Pair<Pair<Expr<BoolType>, A>, MENUUnit<D, A, P>>> {
        return intermediateNodes.values.flatMap { intermediateNode ->
            intermediateNode.successorDistros.flatMap { successorDistro ->
                successorDistro.support.map { (action, successorUnit) ->
                    (intermediateNode.command.guard to action) to successorUnit
                }
            }
        }
    }

    override fun clearIntermediateNodes() {
        intermediateNodes.clear()
    }
}
