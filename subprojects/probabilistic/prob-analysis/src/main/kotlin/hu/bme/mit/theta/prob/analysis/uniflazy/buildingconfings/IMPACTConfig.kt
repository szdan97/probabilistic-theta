package hu.bme.mit.theta.prob.analysis.uniflazy.buildingconfings

import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceChecker
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceSeqItpChecker
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.prob.analysis.uniflazy.*
import hu.bme.mit.theta.solver.ItpSolver

class IMPACTConfig<S: ExprState, A: StmtAction, P: Prec, L, GN: UnitGameNode<GA>, GA>(
    val createTraceChecker:
        (initialAssertion: Expr<BoolType>, finalAssertion: Expr<BoolType>) -> ExprTraceChecker<ItpRefutation>,
    val domain: Domain<S, A, P, Expr<BoolType>, L>,
    val forceCloseScope: (Set<PARTUnit<S, A, P, Expr<BoolType>, L, GN, GA>>) -> Set<PARTUnit<S, A, P, Expr<BoolType>, L, GN, GA>> = {it}
): PARTBuildingConfiguration<S, A, P, Expr<BoolType>, L, GN, GA> {
    constructor(
        solver: ItpSolver,
        domain: Domain<S, A, P, Expr<BoolType>, L>,
        forceCloseScope: (Set<PARTUnit<S, A, P, Expr<BoolType>, L, GN, GA>>) -> Set<PARTUnit<S, A, P, Expr<BoolType>, L, GN, GA>> = {it}
    ) : this(
        {init, final -> ExprTraceSeqItpChecker.create(init, final, solver) },
        domain,
        forceCloseScope
    )

    override fun close(u: PARTUnit<S, A, P, Expr<BoolType>, L, GN, GA>, reachedSet: Set<PARTUnit<S, A, P, Expr<BoolType>, L, GN, GA>>) {
        if (u.isCovered) return //TODO: should this be a throw instead?
        for (potentialCoverer in reachedSet) {
            if (potentialCoverer.isExpanded && domain.stateOrd.isLeq(u.state, potentialCoverer.state)) {
                u.coverWith(potentialCoverer)
                return
            }
        }
        forceClose(u, forceCloseScope(reachedSet))
    }

    private fun forceClose(u: PARTUnit<S, A, P, Expr<BoolType>, L, GN, GA>, allowedCoverers: Set<PARTUnit<S, A, P, Expr<BoolType>, L, GN, GA>>) {
        for (allowedCoverer in allowedCoverers) {
            if(u == allowedCoverer) continue

            // TODO: how will the structural information work here?
            //      is forceCloseScope only an efficiency/heuristics thing,
            //      or does it have a soundness responsibility as well?
            val fullTrace = u.getTraceFromRoot()
            val fullOtherTrace = allowedCoverer.getTraceFromRoot()
            var cutIndex = 0
            while (fullOtherTrace.units.size > cutIndex &&
                fullOtherTrace.units[cutIndex] == fullTrace.units[cutIndex]) {
                cutIndex++
            }
            // cutIndex is the first non-common ancestor
            val subTrace = PARTTrace(fullTrace.units.take(cutIndex), fullTrace.actions.take(cutIndex-1))
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
        trace: PARTTrace<S, A, P, Expr<BoolType>, L, GN, GA>,
        initialAssertion: Expr<BoolType>,
        finalAssertion: Expr<BoolType>
    ): RefinementResult<S, A, P, GN, GA> {
        val traceRefiner = createTraceChecker(initialAssertion, finalAssertion)
        val states = trace.units.map { it.state }
        val transformedTrace = Trace.of(states, trace.actions)
        val refRes = traceRefiner.check(transformedTrace)
        if(refRes.isFeasible) {
            return RefinementResult.Concretizable()
        }
        val refutation = refRes.asInfeasible().refutation.toList()
        for (i in refutation.indices) {
            if(refutation[i] == False()) break
            if(refutation[i] == True()) continue
            val newState = domain.refineState(trace.units[i].state, refutation[i])
            trace.units[i].refineState(newState)
        }
        return RefinementResult.Spurious(trace.units[refutation.indexOfFirst { it != True() }])
        // TODO("should we try to cover nodes after refinement?")
    }

}