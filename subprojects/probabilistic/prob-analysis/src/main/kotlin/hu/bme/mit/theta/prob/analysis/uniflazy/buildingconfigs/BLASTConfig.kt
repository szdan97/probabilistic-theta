package hu.bme.mit.theta.prob.analysis.uniflazy.buildingconfigs

import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceBwBinItpChecker
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceChecker
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.prob.analysis.uniflazy.*
import hu.bme.mit.theta.solver.ItpSolver

class BLASTConfig<S: ExprState, A: StmtAction, P: Prec, R, L, GN: UnitGameNode<GA>, GA>(
    val createTraceChecker:
        (initialAssertion: Expr<BoolType>, finalAssertion: Expr<BoolType>) -> ExprTraceChecker<ItpRefutation>,
    val domain: Domain<S, A, P, R, L>
): PARTBuildingConfiguration<S, A, P, R, L, GN, GA> {
    constructor(solver: ItpSolver, domain: Domain<S, A, P, R, L>) : this(
        {init, final -> ExprTraceBwBinItpChecker.create(init, final, solver) },
        domain
    )

    override fun close(u: PARTUnit<S, A, P, R, L, GN, GA>, reachedSet: Set<PARTUnit<S, A, P, R, L, GN, GA>>) {
        if (u.isCovered) return //TODO: should this be a throw instead?
        for (potentialCoverer in reachedSet) {
            if (potentialCoverer.isExpanded && domain.stateOrd.isLeq(u.state, potentialCoverer.state)) {
                u.coverWith(potentialCoverer)
                return
            }
        }
    }

    override fun concretizeOrRefine(
        trace: PARTTrace<S, A, P, R, L, GN, GA>,
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
        val refutationIndex = refutation.indexOfFirst { !it.equals(BoolExprs.True()) }
        val refutationExpr = refutation[refutationIndex]
        val pivotIndex = refutationIndex - 1
        if(pivotIndex >= 0) { // No reinit needed, pruning + support prec change is enough
            val pivotUnit = trace.units[pivotIndex]
            val newPrec = domain.extendPrec(pivotUnit.supportPrec, refutationExpr)
            pivotUnit.refineSupportPrec(newPrec)
            pivotUnit.removeSubtree()
            return RefinementResult.Spurious(pivotUnit)
        }
        // Reinit needed: The init node must be a more precise abstraction of the concrete init state
        val pivotNode = trace.units.first()
        pivotNode.removeSubtree()
        val newPrec = domain.extendPrec(pivotNode.supportPrec, refutationExpr)
        pivotNode.refineSupportPrec(newPrec)
        val initialStructure = domain.extractStructure(pivotNode.state)
        pivotNode.refineState(domain.abstractFromExpr(initialAssertion, initialStructure, newPrec))
        return RefinementResult.Spurious(pivotNode)
    }

}