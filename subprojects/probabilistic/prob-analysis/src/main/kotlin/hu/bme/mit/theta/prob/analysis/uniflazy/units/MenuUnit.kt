package hu.bme.mit.theta.prob.analysis.uniflazy.units

import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.core.stmt.Stmts
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs
import hu.bme.mit.theta.core.utils.WpState
import hu.bme.mit.theta.prob.analysis.P_ABSTRACTION
import hu.bme.mit.theta.prob.analysis.P_CONCRETE
import hu.bme.mit.theta.prob.analysis.ProbabilisticCommand
import hu.bme.mit.theta.prob.analysis.menuabstraction.BasicMenuGameTransFunc
import hu.bme.mit.theta.prob.analysis.uniflazy.Domain
import hu.bme.mit.theta.prob.analysis.uniflazy.PART
import hu.bme.mit.theta.prob.analysis.uniflazy.PARTUnit
import hu.bme.mit.theta.prob.analysis.uniflazy.PARTUnit.UnitSuccessor
import hu.bme.mit.theta.prob.analysis.uniflazy.UnitGameNode
import hu.bme.mit.theta.probabilistic.FiniteDistribution
import hu.bme.mit.theta.probabilistic.Goal
import hu.bme.mit.theta.probabilistic.dirac
import kotlin.math.abs

class MenuUnit<S : ExprState, A : StmtAction, P : Prec, R, L>(
    supportPrec: P, state: S, domain: Domain<S, A, P, R, L>,
    containingPART: PART<S, A, P, R, L, MenuUnitGameNode, MenuUnitGameAction>,
    parent: PARTUnit<S, A, P, R, L, MenuUnitGameNode, MenuUnitGameAction>?,
    parentAction: GuardedAction<A>?
) : PARTUnit<S, A, P, R, L, MenuUnitGameNode, MenuUnitGameAction>(
    supportPrec, state, domain, containingPART, parent, parentAction
), MenuUnitGameNode {
    val transFunc = BasicMenuGameTransFunc(domain.linkedTransFunc, { s, e -> domain.maySats(s, Not(e)) })

    inner class IntermediateNode(
        val command: ProbabilisticCommand<A>
    ): MenuUnitGameNode {
        val results: MutableList<FiniteDistribution<UnitSuccessor<S, A, P, R, L, MenuUnitGameNode, MenuUnitGameAction>>> =
            arrayListOf()
        var canTrap: Boolean = false // The trans func computes this, it'd be wasteful to compute it in the constructor
        fun expand() {
            require(results.isEmpty()) { "Intermediate node already expanded" }
            val (nextDistros, canTrap) =
                this@MenuUnit.transFunc.getNextStates(state, command, supportPrec)
            results.addAll(
                nextDistros.map {
                    it.transform { (action, nextState) ->
                        val guardedAction = GuardedAction(command.guard, action)
                        UnitSuccessor(
                            guardedAction, MenuUnit(
                                supportPrec, nextState, domain,
                                containingPART, this@MenuUnit,
                                guardedAction
                            )
                        )
                    }
                }
            )
            this.canTrap = canTrap
            isExpanded = true
        }

        fun remove() {
            for (unitSuccessor in results.flatMap { it.support }) {
                unitSuccessor.resultingUnit.remove() // Also removes its subtree
            }
            this@MenuUnit.itmNodes.remove(this.command)
        }

        override fun isTarget(originalGoal: Goal, abstractionGoal: Goal) = false
        override fun getPlayer() = P_ABSTRACTION
        override fun getAvailableActions() =
            if(isCovered) listOf(MenuUnitGameAction.CoverAction)
            else this.results.map { MenuUnitGameAction.AbstractionChoice(it) } +
                    if(canTrap) listOf(MenuUnitGameAction.TrapAction) else listOf()

        override fun getResult(action: MenuUnitGameAction): FiniteDistribution<UnitGameNode<MenuUnitGameAction>> {
            return when(action) {
                is MenuUnitGameAction.AbstractionChoice<*, *, *, *, *> -> action.res.transform {
                    it.resultingUnit as MenuUnitGameNode
                }
                is MenuUnitGameAction.TrapAction -> TrapNode.dirac()
                is MenuUnitGameAction.CommandChoice<*>, MenuUnitGameAction.CoverAction -> throw IllegalArgumentException("Wrong action type.")
            }
        }

        fun minMaxChoiceDifference(
            L: Map<MenuUnitGameNode, Double>,
            LStrategy: Map<MenuUnitGameNode, MenuUnitGameAction>,
            U: Map<MenuUnitGameNode, Double>,
            UStrategy: Map<MenuUnitGameNode, MenuUnitGameAction>,
            tolerance: Double
        ): Set<MenuUnitGameAction> {
            val abstractionChoices = getAvailableActions()
            val UExpected = abstractionChoices.associateWith {
                getResult(it).expectedValue { U[it]!! }
            }
            val LExpected = abstractionChoices.associateWith {
                getResult(it).expectedValue { L[it]!! }
            }
            val max = abstractionChoices.maxOf { UExpected[it]!! }
            val min = abstractionChoices.minOf { LExpected[it]!! }
            val maxChoices = abstractionChoices.filter {
                abs(UExpected[it]!!-max) < tolerance
            }
            val minChoices = abstractionChoices.filter {
                abs(LExpected[it]!!-min) < tolerance
            }
            if(maxChoices != minChoices)
                return maxChoices.minus(minChoices) union minChoices.minus(maxChoices)
            else return setOf()
        }

        fun isNumericRefinable(
            L: Map<MenuUnitGameNode, Double>,
            LStrategy: Map<MenuUnitGameNode, MenuUnitGameAction>,
            U: Map<MenuUnitGameNode, Double>,
            UStrategy: Map<MenuUnitGameNode, MenuUnitGameAction>,
            tolerance: Double
        ) = minMaxChoiceDifference(L, LStrategy, U, UStrategy, tolerance).isNotEmpty()

        override fun toString(): String {
            return "(($state, $command) | $supportPrec)"
        }
    }

    val itmNodes = hashMapOf<ProbabilisticCommand<A>, IntermediateNode>()

    override fun expand() {
        val commands = containingPART.lts.getAvailableCommands(state)
        for (command in commands) {
            if (domain.maySats(state, command.guard)) {
                if (command in itmNodes) {
                    TODO("Handle partially expanded node")
                } else {
                    itmNodes[command] = IntermediateNode(command)
                    itmNodes[command]!!.expand()
                }
            }
        }
    }

    override fun removeSubtree() {
        for ((_, itmNode) in itmNodes) {
            itmNode.remove()
        }
    }

    override fun getSuccessorUnits(): Collection<UnitSuccessor<S, A, P, R, L, MenuUnitGameNode, MenuUnitGameAction>> {
        return itmNodes.values.flatMap { it.results.flatMap { it.support } }
    }

    //// Numeric Stuff

    override fun computeNumericRefinement(
        L: Map<MenuUnitGameNode, Double>,
        LStrategy: Map<MenuUnitGameNode, MenuUnitGameAction>,
        U: Map<MenuUnitGameNode, Double>,
        UStrategy: Map<MenuUnitGameNode, MenuUnitGameAction>,
        tolerance: Double
    ): Expr<BoolType> {
        if(this.mayBeTarget != this.mustBeTarget) TODO()

        val itmNodeToRefine = getOptimalRefinableIntermediateNodes(L, LStrategy, U, UStrategy, tolerance).maxByOrNull {
            U[it]!! - L[it]!!
        }!!

        // TODO: this only leads to meaningful progress if the trap node (or a value-equivalent result)
        //  is actually chosen by the strategy where the refined itmNode is optimal
        if (itmNodeToRefine.canTrap) return itmNodeToRefine.command.guard

        val diff = itmNodeToRefine.minMaxChoiceDifference(L, LStrategy, U, UStrategy, tolerance)
        // As for now, we will only consider a single choice, as all choices would have to be considered separately,
        // which cannot be done by returning a single expression. The result of the related refinement can be either:
        // - the choice is spurious, so it is eliminated
        // - the choice is concretizable, which means (assuming deterministic assignments) it is the ONLY concretizable one,
        //  so all the others are eliminated, as the abstraction choices must be disjoint
        val choiceToConsider = diff.first()
        val wps = (choiceToConsider as MenuUnitGameAction.AbstractionChoice<*, *, *, *, *>).res.support.map {
            WpState.of((it.resultingUnit.state.toExpr())).wep(
                Stmts.SequenceStmt(it.guardedAction.stmts)
            ).expr
        }
        return SmartBoolExprs.And(wps)
    }

    override fun isNumericRefinable(
        L: Map<MenuUnitGameNode, Double>,
        LStrategy: Map<MenuUnitGameNode, MenuUnitGameAction>,
        U: Map<MenuUnitGameNode, Double>,
        UStrategy: Map<MenuUnitGameNode, MenuUnitGameAction>,
        tolerance: Double
    ): Boolean {
        if(isCovered) return false
        if(U[this]!!-L[this]!! < tolerance) return false
        val optimalItmNodes = getOptimalRefinableIntermediateNodes(L, LStrategy, U, UStrategy, tolerance)
        return optimalItmNodes.any()
    }

    override fun refineState(newState: S) {
        for ((command, itmNode) in itmNodes) {
            if (!domain.maySats(newState, command.guard))
                itmNode.remove()
            if (itmNode.canTrap && domain.mustSats(newState, command.guard))
                itmNode.canTrap = false
        }
        state = newState
    }

    private fun getOptimalRefinableIntermediateNodes(
        L: Map<MenuUnitGameNode, Double>,
        LStrategy: Map<MenuUnitGameNode, MenuUnitGameAction>,
        U: Map<MenuUnitGameNode, Double>,
        UStrategy: Map<MenuUnitGameNode, MenuUnitGameAction>,
        tolerance: Double
    ) = getAvailableActions().filter {
        (abs(U[getResult(it).support.first()]!!-U[this]!!) <= tolerance
                || abs(L[getResult(it).support.first()]!!-L[this]!!) <= tolerance)
                && (getResult(it).support.first() as MenuUnit<S,A,P,R,L>.IntermediateNode)
            .isNumericRefinable(L, LStrategy, U, UStrategy, tolerance)
    }.map { getResult(it).support.first() as MenuUnit<S,A,P,R,L>.IntermediateNode } // TODO: a lot of redundant getResult() calls


    //// Stochastic Game Interpretation

    override fun toGame(): MenuUnitGameNode = this

    override fun isTarget(originalGoal: Goal, abstractionGoal: Goal) =
        if (abstractionGoal == Goal.MAX) mayBeTarget else mustBeTarget

    override fun getPlayer() = P_CONCRETE
    override fun getAvailableActions(): Collection<MenuUnitGameAction> =
        this.itmNodes.map { MenuUnitGameAction.CommandChoice(it.key) }

    override fun getResult(action: MenuUnitGameAction):
            FiniteDistribution<UnitGameNode<MenuUnitGameAction>> {
        return when(action) {
            is MenuUnitGameAction.AbstractionChoice<*, *, *, *, *>,
            MenuUnitGameAction.TrapAction -> throw IllegalArgumentException("Wrong action type.")
            MenuUnitGameAction.CoverAction -> this.coverer?.toGame()?.dirac() ?: throw IllegalArgumentException("Cover action for non-covered unit")
            is MenuUnitGameAction.CommandChoice<*> -> itmNodes[action.command]?.dirac()
                ?: throw IllegalArgumentException("Command not enabled or not expanded.")

        }
    }
}

sealed class MenuUnitGameAction {
    class CommandChoice<A: StmtAction>(val command: ProbabilisticCommand<A>): MenuUnitGameAction()
    class AbstractionChoice<S : ExprState, A : StmtAction, P : Prec, R, L>(
        val res: FiniteDistribution<UnitSuccessor<S, A, P, R, L, MenuUnitGameNode, MenuUnitGameAction>>
    ): MenuUnitGameAction()
    object TrapAction: MenuUnitGameAction()
    object CoverAction: MenuUnitGameAction()
}
sealed interface MenuUnitGameNode: UnitGameNode<MenuUnitGameAction>

object TrapNode: MenuUnitGameNode {
    override fun isTarget(originalGoal: Goal, abstractionGoal: Goal) =
        originalGoal == Goal.MIN

    override fun getPlayer() = P_ABSTRACTION // Does not really matter as it is absorbing
    override fun getAvailableActions(): Collection<MenuUnitGameAction> = listOf()
    override fun getResult(action: MenuUnitGameAction): FiniteDistribution<UnitGameNode<MenuUnitGameAction>> {
        throw IllegalArgumentException("The trap node is absorbing, no action is available.")
    }
}