package hu.bme.mit.theta.prob.analysis.uniflazy.buildingconfigs

import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.expl.StmtApplier
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceSeqItpChecker
import hu.bme.mit.theta.core.model.MutableValuation
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.stmt.SequenceStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.core.utils.WpState
import hu.bme.mit.theta.prob.analysis.uniflazy.*
import hu.bme.mit.theta.solver.ItpSolver
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.utils.WithPushPop
import hu.bme.mit.theta.xta.analysis.expl.XtaExplUtils

class IMPACTConfig<S : ExprState, A : StmtAction, P : Prec, R, L, GN : UnitGameNode<GA>, GA>(
    val domain: Domain<S, A, P, R, L>,
    val computeRefutationSequence:
        (
        trace: PARTTrace<S, A, P, R, L, GN, GA>,
        initialAssertion: Expr<BoolType>,
        finalAssertion: Expr<BoolType>
    ) -> List<R>?,
    val forceCloseScope: (PARTUnit<S, A, P, R, L, GN, GA>, Set<PARTUnit<S, A, P, R, L, GN, GA>>) -> Set<PARTUnit<S, A, P, R, L, GN, GA>> = { u, set ->
        set.filter { domain.extractStructure(it.state) == domain.extractStructure(u.state) }.toSet()
    }
) : PARTBuildingConfiguration<S, A, P, R, L, GN, GA> {

    override fun close(u: PARTUnit<S, A, P, R, L, GN, GA>, reachedSet: Set<PARTUnit<S, A, P, R, L, GN, GA>>) {
        if (u.isCovered) return //TODO: should this be a throw instead?
        for (potentialCoverer in reachedSet) {
            if (potentialCoverer.isExpanded && domain.stateOrd.isLeq(u.state, potentialCoverer.state)) {
                u.coverWith(potentialCoverer)
                return
            }
        }
        forceClose(u, forceCloseScope(u, reachedSet))
    }

    private fun forceClose(u: PARTUnit<S, A, P, R, L, GN, GA>, allowedCoverers: Set<PARTUnit<S, A, P, R, L, GN, GA>>) {
        for (allowedCoverer in allowedCoverers) {
            if (u == allowedCoverer) continue

            // TODO: how will the structural information work here?
            //      is forceCloseScope only an efficiency/heuristics thing,
            //      or does it have a soundness responsibility as well?
            val fullTrace = u.getTraceFromRoot()
            val fullOtherTrace = allowedCoverer.getTraceFromRoot()
            var cutIndex = 0
            while (fullOtherTrace.units.size > cutIndex &&
                fullOtherTrace.units[cutIndex] == fullTrace.units[cutIndex]
            ) {
                cutIndex++
            }
            // cutIndex is the first non-common ancestor
            val subTrace = PARTTrace(fullTrace.units.take(cutIndex), fullTrace.actions.take(cutIndex - 1))
            val refinementResult = concretizeOrRefine(
                subTrace,
                subTrace.units.first().state.toExpr(),
                Not(allowedCoverer.state.toExpr())
            )
            if (refinementResult is RefinementResult.Spurious<*, *, *, *, *, *, *>) {
                u.coverWith(allowedCoverer)
                return
            }
        }
    }

    override fun concretizeOrRefine(
        trace: PARTTrace<S, A, P, R, L, GN, GA>,
        initialAssertion: Expr<BoolType>,
        finalAssertion: Expr<BoolType>
    ): RefinementResult<S, A, P, GN, GA> {
        val refutation = computeRefutationSequence(trace, initialAssertion, finalAssertion)
        if (refutation == null) return RefinementResult.Concretizable()
        for (i in refutation.indices) {
            if (refutation[i] == False()) break
            if (refutation[i] == True()) continue
            val newState = domain.refineState(trace.units[i].state, refutation[i])
            trace.units[i].refineState(newState)
        }
        return RefinementResult.Spurious(trace.units[refutation.indexOfFirst { it != True() }])
        // TODO("should we try to cover nodes after refinement?")
    }
}

fun <S : ExprState, A : StmtAction, P : Prec, L, GN : UnitGameNode<GA>, GA> ExprIMPACTConfig(
    solver: ItpSolver,
    domain: Domain<S, A, P, Expr<BoolType>, L>,
    forceCloseScope: (PARTUnit<S, A, P, Expr<BoolType>, L, GN, GA>, Set<PARTUnit<S, A, P, Expr<BoolType>, L, GN, GA>>) -> Set<PARTUnit<S, A, P, Expr<BoolType>, L, GN, GA>> = { u, set ->
        set.filter { domain.extractStructure(it.state) == domain.extractStructure(u.state) }.toSet()
    }
): PARTBuildingConfiguration<S, A, P, Expr<BoolType>, L, GN, GA> {
    fun computeRefutationSequence(
        trace: PARTTrace<S, A, P, Expr<BoolType>, L, GN, GA>,
        initialAssertion: Expr<BoolType>,
        finalAssertion: Expr<BoolType>
    ): List<Expr<BoolType>>? {
        val traceRefiner = ExprTraceSeqItpChecker.create(initialAssertion, finalAssertion, solver)
        val states = trace.units.map { it.state }
        val transformedTrace = Trace.of(states, trace.actions)
        val refRes = traceRefiner.check(transformedTrace)
        if (refRes.isFeasible) {
            return null
        }
        val refutation = refRes.asInfeasible().refutation.toList()
        return refutation
    }
    return IMPACTConfig(
        domain,
        ::computeRefutationSequence,
        forceCloseScope
    )
}

fun <S : ExprState, A : StmtAction, P : Prec, L, GN : UnitGameNode<GA>, GA> ExplValIMPACTConfig(
    solver: Solver,
    stateToValuation: (S) -> Valuation,
    domain: Domain<S, A, P, Valuation, L>,
    forceCloseScope: (PARTUnit<S, A, P, Valuation, L, GN, GA>, Set<PARTUnit<S, A, P, Valuation, L, GN, GA>>) -> Set<PARTUnit<S, A, P, Valuation, L, GN, GA>> = {
        u, set -> set.filter { domain.extractStructure(it.state) == domain.extractStructure(u.state) }.toSet()
    }
): PARTBuildingConfiguration<S, A, P, Valuation, L, GN, GA> {
    fun computeRefutationSequence(
        trace: PARTTrace<S, A, P, Valuation, L, GN, GA>,
        initialAssertion: Expr<BoolType>,
        finalAssertion: Expr<BoolType>
    ): List<Valuation>? {
        TODO("Take initial assertion into account somehow")

        val exactStates = arrayListOf(stateToValuation(trace.units[0].state))
        for (action in trace.actions) {
            val nextState = MutableValuation.copyOf(exactStates.last())
            val applyResult = StmtApplier.apply(SequenceStmt.of(action.stmts), nextState, true)
            if (applyResult == StmtApplier.ApplyResult.BOTTOM) TODO("compute interpolants backward from here and make the rest False()?")
            exactStates.add(nextState)
        }
        val simplified = ExprUtils.simplify(finalAssertion, exactStates.last())
        fun checkSat(expr: Expr<BoolType>): Boolean {
            WithPushPop(solver).use {
                solver.add(PathUtils.unfold(expr, 0))
                solver.check()
                return solver.status.isSat
            }
        }
        val concretizable =
            simplified == True() || (simplified != False() && checkSat(simplified))
        if(concretizable) return null
        val lastInterpolant = XtaExplUtils.interpolate(exactStates.last(), finalAssertion)
        val interpolantsReversed = arrayListOf<Valuation>(lastInterpolant)
        for (i in exactStates.indices.reversed().drop(1)) {
            val exactState = exactStates[i]
            val abstractState = trace.units[i].state
            val badRegion = WpState.of(Not(interpolantsReversed.last().toExpr())).wp(SequenceStmt.of(trace.actions[i - 1].stmts)).expr
            val nextInterpolant = XtaExplUtils.interpolate(exactState, badRegion)
            interpolantsReversed.add(nextInterpolant)
        }
        TODO("what to do about the initial assertion?")

        val refutation = interpolantsReversed.reversed()
        return refutation
    }
    return IMPACTConfig(
        domain,
        ::computeRefutationSequence,
        forceCloseScope
    )
}