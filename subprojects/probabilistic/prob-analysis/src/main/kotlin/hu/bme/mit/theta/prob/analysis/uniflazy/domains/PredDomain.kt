package hu.bme.mit.theta.prob.analysis.uniflazy.domains

import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.analysis.pred.*
import hu.bme.mit.theta.analysis.pred.ExprSplitters.ExprSplitter
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.prob.analysis.besttransformer.predGetGuardSatisfactionConfigs
import hu.bme.mit.theta.prob.analysis.linkedtransfuncs.PredLinkedTransFunc
import hu.bme.mit.theta.prob.analysis.menuabstraction.predMaySatisfy
import hu.bme.mit.theta.prob.analysis.menuabstraction.predMustSatisfy
import hu.bme.mit.theta.prob.analysis.uniflazy.Domain
import hu.bme.mit.theta.solver.Solver

fun PredDomain(
    solver: Solver,
    exprSplitter: ExprSplitter,
    predAbstractor: PredAbstractors.PredAbstractor = PredAbstractors.booleanSplitAbstractor(solver)
) = Domain<PredState, StmtAction, PredPrec, Expr<BoolType>, Unit>(
    stateOrd = PredOrd.create(solver),
    extendPrec = { p, e -> p.join(PredPrec.of(exprSplitter.apply(e))) },
    refineState = { s, e ->
        PredState.of(s.preds + e)
        // TODO: exprSplitting would be great here as well,
        //  but we would need an exact valuation to evaluate each expr
    },
    abstractFromValuation = { v, _, p ->
        predAbstractor.createStatesForExpr(
            v.toExpr(), VarIndexingFactory.indexing(0),
            p, VarIndexingFactory.indexing(0)
        ).first() // TODO: handle non-det result
        // TODO: more efficient state creation through eval
    },
    abstractFromExpr = { e, _, p ->
        predAbstractor.createStatesForExpr(
            e, VarIndexingFactory.indexing(0),
            p, VarIndexingFactory.indexing(0)
        ).first() // TODO: handle non-det result
    },
    extractStructure = {},
    transFunc = PredTransFunc.create<StmtAction>(predAbstractor),
    linkedTransFunc = PredLinkedTransFunc(solver),
    maySats = predMaySatisfy(solver), mustSats = predMustSatisfy(solver),
    getGuardSatisfactionConfigs = predGetGuardSatisfactionConfigs(solver)
)