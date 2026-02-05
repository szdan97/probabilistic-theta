package hu.bme.mit.theta.prob.analysis.uniflazy.units

import hu.bme.mit.theta.analysis.Action
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
import hu.bme.mit.theta.prob.analysis.besttransformer.BasicBestTransformerTransFunc
import hu.bme.mit.theta.prob.analysis.uniflazy.Domain
import hu.bme.mit.theta.prob.analysis.uniflazy.PART
import hu.bme.mit.theta.prob.analysis.uniflazy.PARTUnit
import hu.bme.mit.theta.prob.analysis.uniflazy.UnitGameNode
import hu.bme.mit.theta.probabilistic.FiniteDistribution
import hu.bme.mit.theta.probabilistic.Goal
import hu.bme.mit.theta.probabilistic.dirac
import kotlin.math.abs

class BestTransformerUnit<S : ExprState, A : StmtAction, P : Prec, R, L>(
    supportPrec: P, state: S, domain: Domain<S, A, P, R, L>,
    containingPART: PART<S, A, P, R, L, BestTransformerUnitGameNode, BestTransformerUnitGameAction>,
    parent: PARTUnit<S, A, P, R, L, BestTransformerUnitGameNode, BestTransformerUnitGameAction>?,
    parentAction: GuardedAction<A>?
) : PARTUnit<S, A, P, R, L, BestTransformerUnitGameNode, BestTransformerUnitGameAction>(
    supportPrec, state, domain, containingPART, parent, parentAction
), BestTransformerUnitGameNode {
    inner class IntermediateNode(
        val results: Map<ProbabilisticCommand<A>, FiniteDistribution<UnitSuccessor<S, A, P, R, L, BestTransformerUnitGameNode, BestTransformerUnitGameAction>>>
    ): BestTransformerUnitGameNode {
        override fun isTarget(originalGoal: Goal, abstractionGoal: Goal) = false
        override fun getPlayer() = P_CONCRETE
        override fun getAvailableActions() =
            enabledCommands.map(BestTransformerUnitGameAction::ConcreteChoice)

        override fun getResult(action: BestTransformerUnitGameAction):
                FiniteDistribution<UnitGameNode<BestTransformerUnitGameAction>> {
            return when(action) {
                BestTransformerUnitGameAction.CoverAction,
                is BestTransformerUnitGameAction.AbstractionChoice<*, *, *, *, *> ->
                    throw IllegalArgumentException("Wrong action type.")
                is BestTransformerUnitGameAction.ConcreteChoice<*> ->
                    results[action.command]?.transform { it.resultingUnit as BestTransformerUnitGameNode }
                    ?: throw IllegalArgumentException("Command not enabled or itmNode not expanded.")
            }
        }

        override fun toString(): String {
            return "ItmNode"
        }

        val enabledCommands get() = results.keys

        fun remove() {
            for (result in results.values) {
                for (unitSuccessor in result.support) {
                    unitSuccessor.resultingUnit.remove() // Also removes its subtree
                }
            }
            this@BestTransformerUnit.itmNodes.remove(this)
        }
    }

    val itmNodes = arrayListOf<IntermediateNode>()
    val transFunc = BasicBestTransformerTransFunc(domain.linkedTransFunc, domain.getGuardSatisfactionConfigs)


    override fun expand() {
        require(!isCovered) { "Covered units should not be expanded!" }
        require(itmNodes.isEmpty()) { "Expanding already (partially) expanded BT units is not supported" }
        val commands = containingPART.lts.getAvailableCommands(state).toList()
        val equivalenceClasses = transFunc.getNextStates(state, commands, supportPrec)
        val successorUnits =
            arrayListOf<PARTUnit<S, A, P, R, L, BestTransformerUnitGameNode, BestTransformerUnitGameAction>>()
        for (eqClass in equivalenceClasses) {
            val newNode = IntermediateNode(
                eqClass.toMap().mapValues { (command, resultStateDistribution) ->
                    val resultWithUnits = resultStateDistribution.transform {
                        val (action, state) = it
                        val guardedAction = GuardedAction(command.guard, action)
                        val successorUnit = BestTransformerUnit(
                            this.supportPrec, state, domain,
                            containingPART, this, guardedAction
                        ) as PARTUnit<S, A, P, R, L, BestTransformerUnitGameNode, BestTransformerUnitGameAction>
                        successorUnits.add(successorUnit)
                        return@transform UnitSuccessor(guardedAction, successorUnit)
                    }
                    return@mapValues resultWithUnits
                }
            )
            itmNodes.add(newNode)
        }
        isExpanded = true
        containingPART.reached.addAll(successorUnits)
        containingPART.waitlist.addAll(successorUnits)
    }

    override fun removeSubtree() {
        for (itmNode in itmNodes) {
            itmNode.remove()
        }
    }

    override fun getSuccessorUnits(): Collection<UnitSuccessor<S, A, P, R, L, BestTransformerUnitGameNode, BestTransformerUnitGameAction>> {
        return itmNodes.flatMap { it.results.values.flatMap { it.support } }
    }

    override fun refineState(newState: S) {
        val commands = containingPART.lts.getAvailableCommands(state).toList()
        val newGuardConfigs = domain.getGuardSatisfactionConfigs(newState, commands).map { it.toSet() }
        for (itmNode in itmNodes) {
            if (itmNode.enabledCommands !in newGuardConfigs)
                itmNode.remove()
        }
        state = newState
        if (mayBeTarget && !mustBeTarget) { // If targetness is unknown
            mayBeTarget = domain.maySats(newState, containingPART.targetExpr)
            mustBeTarget = domain.mustSats(newState, containingPART.targetExpr)
        }
    }

    //// Numeric stuff

    override fun isNumericRefinable(
        L: Map<BestTransformerUnitGameNode, Double>,
        LStrategy: Map<BestTransformerUnitGameNode, BestTransformerUnitGameAction>,
        U: Map<BestTransformerUnitGameNode, Double>,
        UStrategy: Map<BestTransformerUnitGameNode, BestTransformerUnitGameAction>,
        tolerance: Double
    ): Boolean {
        if(this.isCovered) return false
        if(this.mayBeTarget != this.mustBeTarget) return true
        val diff = minMaxChoiceDifference(L, LStrategy, U, UStrategy, tolerance)
        return diff.first.isNotEmpty() || diff.second.isNotEmpty()
    }

    override fun computeNumericRefinement(
        L: Map<BestTransformerUnitGameNode, Double>,
        LStrategy: Map<BestTransformerUnitGameNode, BestTransformerUnitGameAction>,
        U: Map<BestTransformerUnitGameNode, Double>,
        UStrategy: Map<BestTransformerUnitGameNode, BestTransformerUnitGameAction>,
        tolerance: Double
    ): Expr<BoolType> {
        if (this.mayBeTarget != this.mustBeTarget) TODO()
        val diff = minMaxChoiceDifference(L, LStrategy, U, UStrategy, tolerance)

        val lowerChoice = getResult(
            diff.first.firstOrNull() ?: ((getAvailableActions()-diff.second).first())
        ).support.first() as BestTransformerUnit<S, A, P, R, L>.IntermediateNode
        val upperChoice = getResult(
            diff.second.firstOrNull() ?: ((getAvailableActions()-diff.first).first())
        ).support.first() as BestTransformerUnit<S, A, P, R, L>.IntermediateNode

        fun computeRefinement(commandAction: BestTransformerUnitGameAction.ConcreteChoice<A>) =
            SmartBoolExprs.And(
                lowerChoice.results[commandAction.command]!!.support.map { (action, result) ->
                    val stmt = Stmts.SequenceStmt(
                        listOf(Stmts.Assume(commandAction.command.guard)) + action.stmts
                    )
                    val wp = WpState.of(result.state.toExpr()).wep(stmt).expr
                    wp
                }
            )


        for (commandAction in lowerChoice.getAvailableActions()) {
            val commandRelevant =
                abs(lowerChoice.getResult(commandAction).expectedValue { L[it]!! } - L[this]!!) <= tolerance
            if (!commandRelevant) continue
            if (commandAction.command !in upperChoice.results) {
                return commandAction.command.guard
            }
            return computeRefinement(commandAction)
        }

        for (commandAction in upperChoice.getAvailableActions()) {
            val commandRelevant =
                abs(upperChoice.getResult(commandAction).expectedValue { U[it]!! } - U[this]!!) <= tolerance
            if (!commandRelevant) continue
            if (commandAction.command !in lowerChoice.results) {
                return commandAction.command.guard
            }
            return computeRefinement(commandAction)
        }

        throw UnsupportedOperationException("Refinement unsuccessful")
    }

    private fun minMaxChoiceDifference(
        L: Map<BestTransformerUnitGameNode, Double>,
        LStrategy: Map<BestTransformerUnitGameNode, BestTransformerUnitGameAction>,
        U: Map<BestTransformerUnitGameNode, Double>,
        UStrategy: Map<BestTransformerUnitGameNode, BestTransformerUnitGameAction>,
        tolerance: Double
    ): Pair<List<BestTransformerUnitGameAction>, List<BestTransformerUnitGameAction>> {
        if (this.isCovered) throw RuntimeException("minMaxChoiceDifference")
        val lowerValue = L[this]!!
        val upperValue = U[this]!!
        val availableActions = this.getAvailableActions()
        val lowerOptimalChoices = availableActions.filter { choice ->
            val first: UnitGameNode<BestTransformerUnitGameAction> = getResult(choice).support.first()
            abs(L[first]!! - lowerValue) <= tolerance
        }
        val upperOptimalChoices = availableActions.filter { choice ->
            abs(U[getResult(choice).support.first()]!! - upperValue) <= tolerance
        }
        return if (lowerOptimalChoices == upperOptimalChoices) (listOf<BestTransformerUnitGameAction>() to listOf())
        else lowerOptimalChoices.minus(upperOptimalChoices) to upperOptimalChoices.minus(lowerOptimalChoices)
    }


    //// Stochastic Game interpretation

    override fun toGame() = this

    override fun isTarget(originalGoal: Goal, abstractionGoal: Goal) =
        if (abstractionGoal == Goal.MAX) mayBeTarget else mustBeTarget

    override fun getPlayer() = P_ABSTRACTION
    override fun getAvailableActions() =
        if(isCovered) listOf(BestTransformerUnitGameAction.CoverAction)
        else itmNodes.map { BestTransformerUnitGameAction.AbstractionChoice(it) }

    override fun getResult(action: BestTransformerUnitGameAction): FiniteDistribution<UnitGameNode<BestTransformerUnitGameAction>> =
        when(action) {
            is BestTransformerUnitGameAction.AbstractionChoice<*, *, *, *, *> ->
                action.itmNode.dirac()
            is BestTransformerUnitGameAction.ConcreteChoice<*> -> throw IllegalArgumentException("Wrong action type.")
            BestTransformerUnitGameAction.CoverAction ->
                this.coverer?.toGame()?.dirac() ?: throw IllegalArgumentException("Coveraction for non-covered unit.")
        }
}

sealed interface BestTransformerUnitGameNode : UnitGameNode<BestTransformerUnitGameAction>
sealed class BestTransformerUnitGameAction {
    class AbstractionChoice<S : ExprState, A : StmtAction, P : Prec, R, L>(val itmNode: BestTransformerUnit<S, A, P, R, L>.IntermediateNode): BestTransformerUnitGameAction()
    class ConcreteChoice<A : Action>(val command: ProbabilisticCommand<A>): BestTransformerUnitGameAction()
    object CoverAction: BestTransformerUnitGameAction()
}