package hu.bme.mit.theta.prob.analysis.besttransformer

import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceChecker
import hu.bme.mit.theta.analysis.expr.refinement.Refutation
import hu.bme.mit.theta.analysis.expr.refinement.RefutationToPrec
import hu.bme.mit.theta.core.stmt.SequenceStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.WpState
import hu.bme.mit.theta.prob.analysis.besttransformer.BestTransformerAbstractor.BestTransformerGameAction
import hu.bme.mit.theta.prob.analysis.besttransformer.BestTransformerAbstractor.BestTransformerGameAction.AbstractionChoice
import hu.bme.mit.theta.prob.analysis.besttransformer.BestTransformerAbstractor.BestTransformerGameAction.ConcreteChoice
import hu.bme.mit.theta.prob.analysis.besttransformer.BestTransformerAbstractor.BestTransformerGameNode
import hu.bme.mit.theta.prob.analysis.besttransformer.BestTransformerAbstractor.BestTransformerGameNode.AbstractionChoiceNode
import hu.bme.mit.theta.prob.analysis.besttransformer.BestTransformerAbstractor.BestTransformerGameNode.ConcreteChoiceNode
import hu.bme.mit.theta.solver.Solver
import java.util.*
import kotlin.math.abs

class BestTransformerRefiner<S : ExprState, A : StmtAction, P : Prec, R : Refutation>(
    val solver: Solver,
    val extend: P.(basedOn: Expr<BoolType>) -> P,
    val pivotSelectionStrategy: PivotSelectionStrategy,
    val eliminateSpurious: Boolean = false,
    val traceChecker: ExprTraceChecker<R>? = null,
    val refToPrec: RefutationToPrec<P, R>? = null,
) {
    init {
        require(!eliminateSpurious || (traceChecker != null && refToPrec != null))
    }


    data class RefinementResult<S : ExprState, A : StmtAction, P : Prec>(
        val newPrec: P,
        val pivotNode: AbstractionChoiceNode<S, A>
    )

    fun refine(
        sg: BestTransformerAbstractor.BestTransformerGame<S, A, *>,
        valueFunctionMax: Map<BestTransformerGameNode<S, A>, Double>,
        valueFunctionMin: Map<BestTransformerGameNode<S, A>, Double>,
        strategyMax: Map<BestTransformerGameNode<S, A>, BestTransformerGameAction<S, A>>,
        strategyMin: Map<BestTransformerGameNode<S, A>, BestTransformerGameAction<S, A>>,
        prec: P,
        nodesToConsider: Collection<AbstractionChoiceNode<S, A>>
        = sg.getAllNodes().filterIsInstance<AbstractionChoiceNode<S, A>>(),
        tolerance: Double = 0.0
    ): RefinementResult<S, A, P> {
        fun minMaxChoiceDifference(node: AbstractionChoiceNode<S, A>):
                Pair<List<BestTransformerGameAction<S, A>>, List<BestTransformerGameAction<S, A>>> {
            val lowerValue = valueFunctionMin[node]!!
            val upperValue = valueFunctionMax[node]!!
            val availableActions = sg.getAvailableActions(node)
            val lowerOptimalChoices = availableActions.filter { choice ->
                abs(valueFunctionMin[sg.getResult(node, choice).support.first()]!! - lowerValue) <= tolerance
            }
            val upperOptimalChoices = availableActions.filter { choice ->
                abs(valueFunctionMax[sg.getResult(node, choice).support.first()]!! - upperValue) <= tolerance
            }
            return if (lowerOptimalChoices == upperOptimalChoices) (listOf<BestTransformerGameAction<S, A>>() to listOf())
            else lowerOptimalChoices.minus(upperOptimalChoices) to upperOptimalChoices.minus(lowerOptimalChoices)
        }

        val refinableNodes = nodesToConsider.filter {
            minMaxChoiceDifference(it).let { it.first.isNotEmpty() || it.second.isNotEmpty() }
        }
        val pivotNode = pivotSelectionStrategy.selectPivot(
            sg, refinableNodes, valueFunctionMax, valueFunctionMin, strategyMax, strategyMin
        )

        if (eliminateSpurious) {
            val trace =
                computeMostProbablePath(sg, pivotNode, strategyMax)
                    ?: computeMostProbablePath(sg, pivotNode, strategyMin)
                    ?: throw RuntimeException("Selected pivot node not reachable with either strategy")
            val checkResult = traceChecker!!.check(trace)
            if (checkResult.isInfeasible) {
                val refutation = checkResult.asInfeasible().refutation
                var runningPrec = prec
                for (i in trace.states.indices) {
                    val precFromRef = refToPrec!!.toPrec(refutation, i)
                    runningPrec = refToPrec.join(runningPrec, precFromRef)
                }
                return RefinementResult(runningPrec, pivotNode)
            }
        }

        val diff = minMaxChoiceDifference(pivotNode)

        val lowerChoice = sg.getResult(
            pivotNode,
            diff.first.firstOrNull() ?: ((sg.getAvailableActions(pivotNode)-diff.second).first())
        ).support.first() as ConcreteChoiceNode<S, A>
        val upperChoice = sg.getResult(
            pivotNode,
            diff.second.firstOrNull() ?: ((sg.getAvailableActions(pivotNode)-diff.first).first())
        ).support.first() as ConcreteChoiceNode<S, A>

        var newPrec = prec
        for (it in sg.getAvailableActions(lowerChoice)) {
            // TODO: this might be replaced by making all commands that currently have the same value (up to tolerance), as the selected choice
            val commandRelevant = it == strategyMin[lowerChoice]
            if (!commandRelevant) continue
            val command = (it as ConcreteChoice<S, A>).command
            val otherRes = upperChoice.commandResults[command]
            if (otherRes == null) {
                newPrec = newPrec.extend(it.command.guard)
            } else {
                for ((action, result) in lowerChoice.commandResults[command]!!.support) {
                    val wp = WpState.of(result.toExpr()).wep(SequenceStmt.of(action.stmts)).expr
                    newPrec = newPrec.extend(ExprUtils.simplify(wp))
                }
            }
        }
        for (it in sg.getAvailableActions(upperChoice)) {
            val commandRelevant = it == strategyMax[upperChoice]
            if (!commandRelevant) continue
            val command = (it as ConcreteChoice<S, A>).command
            val otherRes = lowerChoice.commandResults[command]
            if (otherRes == null) {
                newPrec = newPrec.extend(it.command.guard)
            } else {
                for ((action, result) in upperChoice.commandResults[command]!!.support) {
                    val wp = WpState.of(result.toExpr()).wep(SequenceStmt.of(action.stmts)).expr
                    val simped = ExprUtils.simplify(wp)
                    newPrec = newPrec.extend(simped)
                }
            }
        }

        return RefinementResult(newPrec, pivotNode)
    }

    fun computeMostProbablePath(
        sg: BestTransformerAbstractor.BestTransformerGame<S, A, *>,
        target: BestTransformerGameNode<S, A>,
        strategy: Map<BestTransformerGameNode<S, A>, BestTransformerGameAction<S, A>>
    ): Trace<S, A>? {
        val p = sg.getAllNodes().associateWith { 0.0 }.toMutableMap()
        p[target] = 1.0
        val changed: Queue<BestTransformerGameNode<S, A>> = ArrayDeque()
        changed.add(target)
        val next = hashMapOf<BestTransformerGameNode<S, A>, BestTransformerGameNode<S, A>>()
        while (changed.isNotEmpty()) {
            val node = changed.poll()
            for (prevNode in sg.getPreviousNodes(node)) {
                val chosenAction = strategy[prevNode]!!
                val res = sg.getResult(prevNode, chosenAction)
                val pp = res[node]
                val ppp = pp * p[node]!!
                if(ppp > p[prevNode]!!) {
                    p[prevNode] = ppp
                    changed.add(prevNode)
                    next[prevNode] = node
                }
            }
        }
        if(p[sg.initialNode] == 0.0) return null
        val states = arrayListOf<S>()
        val actions = arrayListOf<A>()
        var curr = sg.initialNode
        while (curr != target) {
            if(curr is AbstractionChoiceNode) {
                states.add(curr.s)
                val abstractionChoiceResult = next[curr] as ConcreteChoiceNode
                val command = (strategy[abstractionChoiceResult]!! as ConcreteChoice).command
                val commandResult = (strategy[curr]!! as AbstractionChoice).commandResults[command]!!
                val action = commandResult.support.find {
                    it.second == (next[abstractionChoiceResult]!! as AbstractionChoiceNode).s
                }!!.first
                actions.add(action)
            }
            curr = next[curr]!!
        }
        states.add((target as AbstractionChoiceNode).s)
        return Trace.of(states, actions)
    }
}