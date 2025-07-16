package hu.bme.mit.theta.prob.analysis.menuabstraction

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
import hu.bme.mit.theta.core.utils.WpState
import hu.bme.mit.theta.prob.analysis.besttransformer.BestTransformerRefiner.RefinementResult
import hu.bme.mit.theta.prob.analysis.menuabstraction.MenuGameAction.AbstractionDecision
import hu.bme.mit.theta.prob.analysis.menuabstraction.MenuGameAction.ChosenCommand
import hu.bme.mit.theta.prob.analysis.menuabstraction.MenuGameNode.ResultNode
import hu.bme.mit.theta.prob.analysis.menuabstraction.MenuGameNode.StateNode
import hu.bme.mit.theta.probabilistic.StochasticGame
import hu.bme.mit.theta.solver.Solver
import java.util.*

class MenuGameRefiner<S: ExprState, A: StmtAction, P: Prec, R: Refutation>(
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

    data class RefinementResult<S: ExprState, A: StmtAction, P: Prec>(
        val newPrec: P,
        val pivotNode: ResultNode<S, A>
    )

    fun  refine(
        sg: StochasticGame<
                MenuGameNode<S, A>,
                MenuGameAction<S, A>
                >,
        valueFunctionMax: Map<MenuGameNode<S, A>, Double>,
        valueFunctionMin: Map<MenuGameNode<S, A>, Double>,
        strategyMax: Map<MenuGameNode<S, A>, MenuGameAction<S, A>>,
        strategyMin: Map<MenuGameNode<S, A>, MenuGameAction<S, A>>,
        prec: P,
        nodesToConsider: Collection<StateNode<S, A>>
        = sg.getAllNodes().filterIsInstance<StateNode<S, A>>(),
        tolerance: Double = 0.0
    ): RefinementResult<S, A, P> {
        return refine(sg, valueFunctionMax, valueFunctionMin, strategyMax, strategyMin, {prec}, nodesToConsider, tolerance)
    }

    fun  refine(
        sg: StochasticGame<
                MenuGameNode<S, A>,
                MenuGameAction<S, A>
                >,
        valueFunctionMax: Map<MenuGameNode<S, A>, Double>,
        valueFunctionMin: Map<MenuGameNode<S, A>, Double>,
        strategyMax: Map<MenuGameNode<S, A>, MenuGameAction<S, A>>,
        strategyMin: Map<MenuGameNode<S, A>, MenuGameAction<S, A>>,
        prec: (MenuGameNode<S,A>) -> P,
        nodesToConsider: Collection<StateNode<S, A>>
            = sg.getAllNodes().filterIsInstance<StateNode<S, A>>(),
        tolerance: Double = 0.0
    ): RefinementResult<S, A, P> {
        fun minMaxChoiceDifference(node: ResultNode<S, A>): Set<MenuGameAction<S, A>> {
            val abstractionChoices = sg.getAvailableActions(node)
            val max = abstractionChoices.maxOf {
                sg.getResult(node, it).expectedValue { valueFunctionMax[it]!! }
            }
            val min = abstractionChoices.minOf {
                sg.getResult(node, it).expectedValue { valueFunctionMin[it]!! }
            }
            val maxChoices = abstractionChoices.filter {
                sg.getResult(node, it).expectedValue { valueFunctionMax[it]!! } == max
            }
            val minChoices = abstractionChoices.filter {
                sg.getResult(node, it).expectedValue { valueFunctionMin[it]!! } == min
            }
            if(maxChoices != minChoices) return maxChoices.minus(minChoices) union minChoices.minus(maxChoices)
            else return setOf()
        }

        fun refinable(node: ResultNode<S, A>): Boolean = minMaxChoiceDifference(node).isNotEmpty()

        fun refinable(node: StateNode<S, A>): Boolean =
                valueFunctionMax[node]!! - valueFunctionMin[node]!! > tolerance && (
                        node.minReward != node.maxReward || sg.getAvailableActions(node).any { a ->
                            val resNode = sg.getResult(node, a).support.first() as ResultNode // always dirac
                            refinable(resNode)
                        }
                )

        //val nodeToRefine = nodesToConsider.sortedBy { if(sg.getAvailableActions(it).toString().contains("isSpurious")) 1 else 0 }.find {
        val refinableNodes = nodesToConsider.filter(::refinable)
        if(refinableNodes.isEmpty())
            throw IllegalArgumentException("Unable to refine menu game, no refinable node found")
        val nodeToRefine = pivotSelectionStrategy.selectPivot(
            sg,
            refinableNodes,
            valueFunctionMax, valueFunctionMin,
            strategyMax, strategyMin
        )

        val actions = sg.getAvailableActions(nodeToRefine)
        var resnodeToRefine: ResultNode<S, A>? = null
        for (a in actions) {
            val resnode = sg.getResult(nodeToRefine, a).support.first() as ResultNode<S, A>
            if(refinable(resnode)) {
                resnodeToRefine = resnode
                break
            }
        }
        if (resnodeToRefine == null) throw IllegalArgumentException("Unable to refine menu game, no refinable node found")
        val diff = minMaxChoiceDifference(resnodeToRefine)

        if (eliminateSpurious && sg is MenuGameAbstractor.StandardMenuGame<*,*,*>) {
            // TODO: make this better
            val trace = computeMostProbablePath(sg as MenuGameAbstractor.StandardMenuGame<S,A,P>, nodeToRefine, strategyMax)
            val checkResult = traceChecker!!.check(trace)
            if (checkResult.isInfeasible) {
                val refutation = checkResult.asInfeasible().refutation
                var runningPrec = prec(nodeToRefine)
                for (i in trace.states.indices) {
                    val precFromRef = refToPrec!!.toPrec(refutation, i)
                    runningPrec = refToPrec.join(runningPrec, precFromRef)
                }
                return RefinementResult(runningPrec, resnodeToRefine)
            }
        }

        var newPrec = prec(resnodeToRefine)
        for(abstractionDecision in diff) {
            when(abstractionDecision){
                is MenuGameAction.EnterTrap -> {
                    val command = resnodeToRefine.a
                    newPrec = newPrec.extend(command.guard)
                }
                is AbstractionDecision -> {
                    newPrec = abstractionDecision.result.support.map {
                        (action, nextState) ->
                        WpState.of(nextState.toExpr()).wep(SequenceStmt.of(action.stmts)).expr
                    }.fold(newPrec) { p, expr -> p.extend(expr) }
                }
                is ChosenCommand -> throw RuntimeException("WTF")
            }
        }

        return RefinementResult(newPrec, resnodeToRefine)

    }

    fun computeMostProbablePath(
        sg: MenuGameAbstractor.StandardMenuGame<S, A, *>,
        target: MenuGameNode<S, A>,
        strategy: Map<MenuGameNode<S, A>, MenuGameAction<S, A>>
    ): Trace<S, A> {
        val p = sg.getAllNodes().associateWith { 0.0 }.toMutableMap()
        p[target] = 1.0
        val changed: Queue<MenuGameNode<S, A>> = ArrayDeque()
        changed.add(target)
        val next = hashMapOf<MenuGameNode<S, A>, MenuGameNode<S, A>>()
        while (changed.isNotEmpty()) {
            val node = changed.poll()
            for (prevNode in sg.getPreviousNodes(node)!!) {
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
        if(p[sg.initialNode] == 0.0) TODO("The chosen pivot node is not reachable with this strategy")
        val states = arrayListOf<S>()
        val actions = arrayListOf<A>()
        var curr = sg.initialNode
        while (curr != target) {
            if(curr is StateNode) {
                states.add(curr.s)
                val command = (strategy[curr]!! as ChosenCommand)
                val abstractionChoiceNode = sg.getResult(curr, command).support.first()
                val res =
                    (strategy[abstractionChoiceNode]!! as AbstractionDecision<S, A>).result
                val action = res.support.find {
                    it.second == (next[abstractionChoiceNode]!! as StateNode).s
                }!!.first
                actions.add(action)
            }
            curr = next[curr]!!
        }
        states.add((target as StateNode).s)
        return Trace.of(states, actions)
    }


}