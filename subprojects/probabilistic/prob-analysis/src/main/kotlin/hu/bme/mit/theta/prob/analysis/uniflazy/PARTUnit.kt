package hu.bme.mit.theta.prob.analysis.uniflazy

import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.core.stmt.SequenceStmt
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.stmt.Stmts
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.probabilistic.FiniteDistribution
import hu.bme.mit.theta.probabilistic.Goal

/**
 * Generic interface for Units in a Probabilistic Abstract Reachability Tree.
 * A Unit generally consists of a single state node, labeled by an abstract state,
 * and its successor intermediate nodes, which enable the separation of original and
 * abstraction-induced non-determinism.
 * This separation is the main underlying idea of game-based abstraction-refinement methods).
 */
abstract class PARTUnit<S : ExprState, A : StmtAction, P : Prec, R, L,
        GN : UnitGameNode<GA> /* Game Node type */, GA /* Game Action type */>(
    supportPrec: P,
    state: S,
    val domain: Domain<S, A, P, R, L>,
    val containingPART: PART<S, A, P, R, L, GN, GA>,

    // Used when computing the trace from the root
    // QoL/optimization-related (could be stored in a separate map)
    // -> not described in the theory
    val parent: PARTUnit<S, A, P, R, L, GN, GA>?,
    val parentAction: GuardedAction<A>?
) {
    init {
        require( (parent == null) == (parentAction == null) ) { "Inconsistent parent and parentAction" }
    }

    /**
     * Fully expands the unit, creating the internal structure and initializing the successor units.
     * Adds the newly created successor units to the reached set and waitlist of the containing PART.
     * Ensures that isExpanded is true.
     */
    abstract fun expand()
    var supportPrec: P = supportPrec
        protected set
    var state: S = state
        protected set

    abstract fun refineState(newState: S)
    fun refineSupportPrec(newPrec: P) { supportPrec = newPrec }
    abstract fun removeSubtree()
    abstract fun getSuccessorUnits(): Collection<UnitSuccessor<S, A, P, R, L, GN, GA>>

    class GuardedAction<A: StmtAction>(val guard: Expr<BoolType>, val action: A): StmtAction() {
        override fun getStmts(): List<Stmt> {
            return listOf(SequenceStmt.of(listOf(Stmts.Assume(guard)) + action.stmts))
        }
    }
    data class UnitSuccessor<S : ExprState, A : StmtAction, P : Prec, R, L,
            GN : UnitGameNode<GA> /* Game Node type */, GA /* Game Action type */>(
        val guardedAction: GuardedAction<A>, val resultingUnit: PARTUnit<S, A, P, R, L, GN, GA>
    )

    abstract fun toGame(): GN
    /**
     * If true, then an expression can be computed using computeNumericRefinement, whose knowledge would make
     * the numerical bounds tighter.
     */
    abstract fun isNumericRefinable(
        L: Map<GN, Double>,
        LStrategy: Map<GN, GA>,
        U: Map<GN, Double>,
        UStrategy: Map<GN, GA>,
        tolerance: Double
    ): Boolean

    /**
     * Returns an expression whose knowledge would make the value bounds tighter.
     * Only computes the relevant expression, does not change the node or the related unit.
     * Might throw an exception if isRefinable() is false.
     */
    abstract fun computeNumericRefinement(
        L: Map<GN, Double>,
        LStrategy: Map<GN, GA>,
        U: Map<GN, Double>,
        UStrategy: Map<GN, GA>,
        tolerance: Double
    ): Expr<BoolType>

    // These are not described in the theoretical treatment of unit
    // as part of the unit interface, as they are not meant to be configurable,
    // but storing them together with the unit is more efficient than
    // separate maps

    var mustBeTarget: Boolean = domain.mustSats(state, containingPART.targetExpr)
    var mayBeTarget: Boolean = mustBeTarget || domain.maySats(state, containingPART.targetExpr)
    var coverer: PARTUnit<S, A, P, R, L, GN, GA>? = null
    val coveredUnits = hashSetOf<PARTUnit<S, A, P, R, L, GN, GA>>()
    fun removeCover() {
        coverer?.coveredUnits?.remove(this)
            ?: throw IllegalArgumentException("Trying to remove the covering edge of a non-covered node")
        coverer = null
        if(this in containingPART.reached)
            containingPART.waitlist.add(this)
    }
    fun coverWith(newCoverer: PARTUnit<S, A, P, R, L, GN, GA>) {
        require(coverer == null) { "Trying to cover an already covered node" }
        coverer = newCoverer
        newCoverer.coveredUnits.add(this)
        containingPART.waitlist.remove(this)
    }
    fun remove() {
        for (coveredUnit in coveredUnits) {
            coveredUnit.removeCover()
        }
        this.removeSubtree()
        containingPART.reached.remove(this)
        containingPART.waitlist.remove(this)
    }


    var isExpanded: Boolean = false
    val isCovered get() = coverer != null
    val isFinished get() = isExpanded || isCovered || mustBeTarget
    fun getTraceFromRoot(): PARTTrace<S, A, P, R, L, GN, GA> {
        val units = arrayListOf(this)
        val actions = arrayListOf<GuardedAction<A>>()
        while (units.last().parent != null) {
            units.add(units.last().parent!!)
            actions.add(units.last().parentAction!!)
        }
        return PARTTrace(units.reversed(), actions.reversed())
    }

    companion object {
        var nextId = 0
    }

    val id = nextId++
}

interface UnitGameNode<GA>{
    fun isTarget(originalGoal: Goal, abstractionGoal: Goal): Boolean
    fun getPlayer(): Int
    fun getAvailableActions(): Collection<GA>
    fun getResult(action: GA): FiniteDistribution<UnitGameNode<GA>>
}