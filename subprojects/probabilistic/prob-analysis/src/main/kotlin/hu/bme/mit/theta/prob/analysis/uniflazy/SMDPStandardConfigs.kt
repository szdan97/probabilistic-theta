package hu.bme.mit.theta.prob.analysis.uniflazy

import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.expl.ExplPrec
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.analysis.pred.ExprSplitters
import hu.bme.mit.theta.analysis.pred.PredPrec
import hu.bme.mit.theta.analysis.pred.PredState
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.prob.analysis.jani.SMDP
import hu.bme.mit.theta.prob.analysis.jani.SMDPCommandAction
import hu.bme.mit.theta.prob.analysis.jani.SMDPState
import hu.bme.mit.theta.prob.analysis.uniflazy.buildingconfigs.BLASTConfig
import hu.bme.mit.theta.prob.analysis.uniflazy.buildingconfigs.ExplValIMPACTConfig
import hu.bme.mit.theta.prob.analysis.uniflazy.buildingconfigs.ExprIMPACTConfig
import hu.bme.mit.theta.prob.analysis.uniflazy.domains.ExplDomain
import hu.bme.mit.theta.prob.analysis.uniflazy.domains.PredDomain
import hu.bme.mit.theta.prob.analysis.uniflazy.domains.SMDPDomain
import hu.bme.mit.theta.prob.analysis.uniflazy.units.*
import hu.bme.mit.theta.probabilistic.gamesolvers.VISolver
import hu.bme.mit.theta.solver.ItpSolver
import hu.bme.mit.theta.solver.Solver

private fun <S : ExprState, P : Prec, A : StmtAction, LL, GN : UnitGameNode<GA>, GA, R> firstRefinable(
    units: Set<PARTUnit<S, A, P, R, LL, GN, GA>>,
    unitToNodeMap: Map<PARTUnit<S, A, P, R, LL, GN, GA>, GN>,
    L: Map<GN, Double>,
    LStrategy: Map<GN, GA>,
    U: Map<GN, Double>,
    UStrategy: Map<GN, GA>
): PARTUnit<S, A, P, R, LL, GN, GA> {
    return units.find {
        it.isNumericRefinable(L, LStrategy, U, UStrategy, 1e-7)
    }!!
}

fun SMDP_EXPL_BLAST_MENU(solver: Solver, itpSolver: ItpSolver) {
    val domain = SMDPDomain(ExplDomain.ExplDomainWithExprRef(solver, 0))
    UnifiedLazyChecker<
            SMDPState<ExplState>, SMDPCommandAction,
            ExplPrec, Expr<BoolType>, List<SMDP.Location>,
            MenuUnitGameNode, MenuUnitGameAction
            >(
        domain,
        { s, p, part -> MenuUnit(p, s, domain, part, null, null) },
        BLASTConfig(itpSolver, domain),
        VISolver(1e-7),
        ::firstRefinable
    )
}

fun SMDP_EXPL_BLAST_BT(solver: Solver, itpSolver: ItpSolver) {
    val domain = SMDPDomain(ExplDomain.ExplDomainWithExprRef(solver, 0))
    UnifiedLazyChecker<
            SMDPState<ExplState>, SMDPCommandAction,
            ExplPrec, Expr<BoolType>, List<SMDP.Location>,
            BestTransformerUnitGameNode, BestTransformerUnitGameAction
            >(
        domain,
        { s, p, part -> BestTransformerUnit(p, s, domain, part, null, null) },
        BLASTConfig(itpSolver, domain),
        VISolver(1e-7),
        ::firstRefinable
    )
}

fun SMDP_PRED_BLAST_MENU(solver: Solver, itpSolver: ItpSolver) {
    val domain = SMDPDomain(PredDomain(solver, ExprSplitters.atoms()))
    UnifiedLazyChecker<
            SMDPState<PredState>, SMDPCommandAction,
            PredPrec, Expr<BoolType>, List<SMDP.Location>,
            MenuUnitGameNode, MenuUnitGameAction
            >(
        domain,
        { s, p, part -> MenuUnit(p, s, domain, part, null, null) },
        BLASTConfig(itpSolver, domain),
        VISolver(1e-7),
        ::firstRefinable
    )
}

fun SMDP_PRED_BLAST_BT(solver: Solver, itpSolver: ItpSolver) {
    val domain = SMDPDomain(PredDomain(solver, ExprSplitters.atoms()))
    UnifiedLazyChecker<
            SMDPState<PredState>, SMDPCommandAction,
            PredPrec, Expr<BoolType>, List<SMDP.Location>,
            BestTransformerUnitGameNode, BestTransformerUnitGameAction
            >(
        domain,
        { s, p, part -> BestTransformerUnit(p, s, domain, part, null, null) },
        BLASTConfig(itpSolver, domain),
        VISolver(1e-7),
        ::firstRefinable
    )
}

fun SMDP_EXPL_IMPACT_MENU(solver: Solver, itpSolver: ItpSolver) {
    val domain = SMDPDomain(ExplDomain.WithValRef(solver, 0))
    UnifiedLazyChecker<
            SMDPState<ExplState>, SMDPCommandAction,
            ExplPrec, Valuation, List<SMDP.Location>,
            MenuUnitGameNode, MenuUnitGameAction
            >(
        domain,
        { s, p, part -> MenuUnit(p, s, domain, part, null, null) },
        ExplValIMPACTConfig(solver, {it.domainState}, domain),
        VISolver(1e-7),
        ::firstRefinable
    )
}

fun SMDP_EXPL_IMPACT_BT(solver: Solver, itpSolver: ItpSolver) {
    val domain = SMDPDomain(ExplDomain.WithValRef(solver, 0))
    UnifiedLazyChecker<
            SMDPState<ExplState>, SMDPCommandAction,
            ExplPrec, Valuation, List<SMDP.Location>,
            BestTransformerUnitGameNode, BestTransformerUnitGameAction
            >(
        domain,
        { s, p, part -> BestTransformerUnit(p, s, domain, part, null, null) },
        ExplValIMPACTConfig(solver, {it.domainState}, domain),
        VISolver(1e-7),
        ::firstRefinable
    )
}

fun SMDP_PRED_IMPACT_MENU(solver: Solver, itpSolver: ItpSolver) {
    val domain = SMDPDomain(PredDomain(solver, ExprSplitters.atoms()))
    UnifiedLazyChecker<
            SMDPState<PredState>, SMDPCommandAction,
            PredPrec, Expr<BoolType>, List<SMDP.Location>,
            MenuUnitGameNode, MenuUnitGameAction
            >(
        domain,
        { s, p, part -> MenuUnit(p, s, domain, part, null, null) },
        ExprIMPACTConfig(itpSolver, domain),
        VISolver(1e-7),
        ::firstRefinable
    )
}

fun SMDP_PRED_IMPACT_BT(solver: Solver, itpSolver: ItpSolver) {
    val domain = SMDPDomain(PredDomain(solver, ExprSplitters.atoms()))
    UnifiedLazyChecker<
            SMDPState<PredState>, SMDPCommandAction,
            PredPrec, Expr<BoolType>, List<SMDP.Location>,
            BestTransformerUnitGameNode, BestTransformerUnitGameAction
            >(
        domain,
        { s, p, part -> BestTransformerUnit(p, s, domain, part, null, null) },
        ExprIMPACTConfig(itpSolver, domain),
        VISolver(1e-7),
        ::firstRefinable
    )
}
