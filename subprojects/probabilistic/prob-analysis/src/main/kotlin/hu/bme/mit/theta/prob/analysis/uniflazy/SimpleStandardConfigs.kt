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
import hu.bme.mit.theta.prob.analysis.uniflazy.buildingconfigs.BLASTConfig
import hu.bme.mit.theta.prob.analysis.uniflazy.buildingconfigs.ExplValIMPACTConfig
import hu.bme.mit.theta.prob.analysis.uniflazy.buildingconfigs.ExprIMPACTConfig
import hu.bme.mit.theta.prob.analysis.uniflazy.domains.ExplDomain
import hu.bme.mit.theta.prob.analysis.uniflazy.domains.PredDomain
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

fun Simple_EXPL_BLAST_MENU(solver: Solver, itpSolver: ItpSolver) {
    val domain = ExplDomain.ExplDomainWithExprRef<StmtAction>(solver, 0)
    UnifiedLazyChecker<
            ExplState, StmtAction,
            ExplPrec, Expr<BoolType>, Unit,
            MenuUnitGameNode, MenuUnitGameAction
            >(
        domain,
        { s, p, part -> MenuUnit(p, s, domain, part, null, null) },
        BLASTConfig(itpSolver, domain),
        VISolver(1e-7),
        ::firstRefinable
    )
}

fun Simple_EXPL_BLAST_BT(solver: Solver, itpSolver: ItpSolver) {
    val domain = ExplDomain.ExplDomainWithExprRef<StmtAction>(solver, 0)
    UnifiedLazyChecker<
            ExplState, StmtAction,
            ExplPrec, Expr<BoolType>, Unit,
            BestTransformerUnitGameNode, BestTransformerUnitGameAction
            >(
        domain,
        { s, p, part -> BestTransformerUnit(p, s, domain, part, null, null) },
        BLASTConfig(itpSolver, domain),
        VISolver(1e-7),
        ::firstRefinable
    )
}

fun Simple_PRED_BLAST_MENU(solver: Solver, itpSolver: ItpSolver) {
    val domain = PredDomain<StmtAction>(solver, ExprSplitters.atoms())
    UnifiedLazyChecker<
            PredState, StmtAction,
            PredPrec, Expr<BoolType>, Unit,
            MenuUnitGameNode, MenuUnitGameAction
            >(
        domain,
        { s, p, part -> MenuUnit(p, s, domain, part, null, null) },
        BLASTConfig(itpSolver, domain),
        VISolver(1e-7),
        ::firstRefinable
    )
}

fun Simple_PRED_BLAST_BT(solver: Solver, itpSolver: ItpSolver) {
    val domain = PredDomain<StmtAction>(solver, ExprSplitters.atoms())
    UnifiedLazyChecker<
            PredState, StmtAction,
            PredPrec, Expr<BoolType>, Unit,
            BestTransformerUnitGameNode, BestTransformerUnitGameAction
            >(
        domain,
        { s, p, part -> BestTransformerUnit(p, s, domain, part, null, null) },
        BLASTConfig(itpSolver, domain),
        VISolver(1e-7),
        ::firstRefinable
    )
}

fun Simple_EXPL_IMPACT_MENU(solver: Solver, itpSolver: ItpSolver) {
    val domain = ExplDomain.WithValRef<StmtAction>(solver, 0)
    UnifiedLazyChecker<
            ExplState, StmtAction,
            ExplPrec, Valuation, Unit,
            MenuUnitGameNode, MenuUnitGameAction
            >(
        domain,
        { s, p, part -> MenuUnit(p, s, domain, part, null, null) },
        ExplValIMPACTConfig(solver, {it}, domain),
        VISolver(1e-7),
        ::firstRefinable
    )
}

fun Simple_EXPL_IMPACT_BT(solver: Solver, itpSolver: ItpSolver) {
    val domain = ExplDomain.WithValRef<StmtAction>(solver, 0)
    UnifiedLazyChecker<
            ExplState, StmtAction,
            ExplPrec, Valuation, Unit,
            BestTransformerUnitGameNode, BestTransformerUnitGameAction
            >(
        domain,
        { s, p, part -> BestTransformerUnit(p, s, domain, part, null, null) },
        ExplValIMPACTConfig(solver, {it}, domain),
        VISolver(1e-7),
        ::firstRefinable
    )
}

fun Simple_PRED_IMPACT_MENU(solver: Solver, itpSolver: ItpSolver) {
    val domain = PredDomain<StmtAction>(solver, ExprSplitters.atoms())
    UnifiedLazyChecker<
            PredState, StmtAction,
            PredPrec, Expr<BoolType>, Unit,
            MenuUnitGameNode, MenuUnitGameAction
            >(
        domain,
        { s, p, part -> MenuUnit(p, s, domain, part, null, null) },
        ExprIMPACTConfig(itpSolver, domain),
        VISolver(1e-7),
        ::firstRefinable
    )
}

fun Simple_PRED_IMPACT_BT(solver: Solver, itpSolver: ItpSolver) {
    val domain = PredDomain<StmtAction>(solver, ExprSplitters.atoms())
    UnifiedLazyChecker<
            PredState, StmtAction,
            PredPrec, Expr<BoolType>, Unit,
            BestTransformerUnitGameNode, BestTransformerUnitGameAction
            >(
        domain,
        { s, p, part -> BestTransformerUnit(p, s, domain, part, null, null) },
        ExprIMPACTConfig(itpSolver, domain),
        VISolver(1e-7),
        ::firstRefinable
    )
}
