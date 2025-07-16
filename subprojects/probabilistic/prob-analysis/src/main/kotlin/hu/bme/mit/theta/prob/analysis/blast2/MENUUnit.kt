package hu.bme.mit.theta.prob.analysis.blast2

import hu.bme.mit.theta.analysis.PartialOrd
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.prob.analysis.P_ABSTRACTION
import hu.bme.mit.theta.prob.analysis.P_CONCRETE
import hu.bme.mit.theta.prob.analysis.ProbabilisticCommand
import hu.bme.mit.theta.prob.analysis.ProbabilisticCommandLTS
import hu.bme.mit.theta.prob.analysis.menuabstraction.MenuGameTransFunc
import hu.bme.mit.theta.probabilistic.FiniteDistribution
import hu.bme.mit.theta.probabilistic.FiniteDistribution.Companion.dirac
import hu.bme.mit.theta.probabilistic.ImplicitStochasticGame

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

sealed class BLASTMENUGameNode<D : ExprState, A : StmtAction, P : Prec>(val player: Int) {
    data class StateNode<D : ExprState, A : StmtAction, P : Prec>(val origin: MENUUnit<D, A, P>) :
        BLASTMENUGameNode<D, A, P>(P_CONCRETE) {
        override fun toString() = origin.toString()
    }

    data class IntermediateNode<D : ExprState, A : StmtAction, P : Prec>(val origin: MENUUnit<D, A, P>.IntermediateNode) :
        BLASTMENUGameNode<D, A, P>(P_ABSTRACTION) {
        override fun toString() = origin.toString()
    }

    class TrapNode<D : ExprState, A : StmtAction, P : Prec> : BLASTMENUGameNode<D, A, P>(P_ABSTRACTION) {
        override fun toString() = "TRAP"
    }
}

sealed class BLASTMENUGameAction<D : ExprState, A : StmtAction, P : Prec> {
    data class CommandAction<D : ExprState, A : StmtAction, P : Prec>(val command: ProbabilisticCommand<A>) :
        BLASTMENUGameAction<D, A, P>()

    data class ResultAction<D : ExprState, A : StmtAction, P : Prec>(val result: FiniteDistribution<BLASTMENUGameNode<D, A, P>>) :
        BLASTMENUGameAction<D, A, P>()

    class CoverAction<D : ExprState, A : StmtAction, P : Prec>: BLASTMENUGameAction<D,A,P>() {
        override fun toString() = "COVER"
    }

    //class TrapAction<D : ExprState, A : StmtAction, P : Prec> : BLASTMENUGameAction<D, A, P>()
}

class BlastMenuGame<D : ExprState, A : StmtAction, P : Prec>(val initialUnit: MENUUnit<D, A, P>) :
    ImplicitStochasticGame<BLASTMENUGameNode<D, A, P>, BLASTMENUGameAction<D, A, P>>() {
    private val trap: BLASTMENUGameNode<D, A, P> = BLASTMENUGameNode.TrapNode<D, A, P>()
    private val dtrap = dirac(trap)
    private val coverAction = BLASTMENUGameAction.CoverAction<D,A,P>()
    //private val trapAction = BLASTMENUGameAction.TrapAction<D,A,P>()
    override fun getPlayer(node: BLASTMENUGameNode<D, A, P>) = node.player

    override fun getResult(
        node: BLASTMENUGameNode<D, A, P>,
        action: BLASTMENUGameAction<D, A, P>
    ): FiniteDistribution<BLASTMENUGameNode<D, A, P>> {
        if (node is BLASTMENUGameNode.StateNode<D, A, P>) {
            if(action == coverAction && node.origin.isCovered()) return dirac(BLASTMENUGameNode.StateNode(node.origin.getCoverer()!!))
            if (action is BLASTMENUGameAction.CommandAction<D, A, P>) {
                val origin = node.origin.intermediateNodes[action.command]
                    ?: throw IllegalArgumentException("getResult called with disabled action $action on node $node")
                val wrapped = BLASTMENUGameNode.IntermediateNode(origin)
                return dirac(wrapped)
            }
        }

        if (node is BLASTMENUGameNode.IntermediateNode<D, A, P>)
        {
            if(action is BLASTMENUGameAction.ResultAction<D,A,P>) return action.result //checking would be too expensive
            //if(action is BLASTMENUGameAction.TrapAction<D,A,P> && node.origin.canTrap) return dtrap
        }

        throw IllegalArgumentException("getResult called with disabled action $action on node $node")
    }

    override fun getAvailableActions(node: BLASTMENUGameNode<D, A, P>): Collection<BLASTMENUGameAction<D, A, P>> {
        return when (node) {
            is BLASTMENUGameNode.IntermediateNode -> {
                val optTrap = if (node.origin.canTrap) listOf(dtrap) else listOf()
                val realResults =
                    node.origin.successorDistros.map { it.transform {
                        BLASTMENUGameNode.StateNode(it.second) as BLASTMENUGameNode<D,A,P>
                    } }
                val combined = optTrap + realResults
                combined.map { BLASTMENUGameAction.ResultAction(it) }
            }

            is BLASTMENUGameNode.StateNode -> {
                if (node.origin.isCovered()) listOf(coverAction)
                else node.origin.intermediateNodes.keys.map {
                    BLASTMENUGameAction.CommandAction(
                        it
                    )
                }
            }

            is BLASTMENUGameNode.TrapNode<D, A, P> -> listOf()
        }
    }

    override val initialNode: BLASTMENUGameNode<D, A, P>
        get() = BLASTMENUGameNode.StateNode(initialUnit)

}