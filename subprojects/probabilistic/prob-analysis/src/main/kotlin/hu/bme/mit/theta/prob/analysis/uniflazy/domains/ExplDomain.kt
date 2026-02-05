package hu.bme.mit.theta.prob.analysis.uniflazy.domains

import hu.bme.mit.theta.analysis.expl.ExplOrd
import hu.bme.mit.theta.analysis.expl.ExplPrec
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expl.ExplStmtTransFunc
import hu.bme.mit.theta.analysis.expr.ExprStates
import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.core.model.MutableValuation
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import hu.bme.mit.theta.prob.analysis.besttransformer.explGetGuardSatisfactionConfigs
import hu.bme.mit.theta.prob.analysis.linkedtransfuncs.ExplLinkedTransFunc
import hu.bme.mit.theta.prob.analysis.menuabstraction.explMaySatisfy
import hu.bme.mit.theta.prob.analysis.menuabstraction.explMustSatisfy
import hu.bme.mit.theta.prob.analysis.uniflazy.Domain
import hu.bme.mit.theta.solver.Solver

object ExplDomain {

    private fun <R> explDomain(
        solver: Solver,
        maxEnum: Int,
        refine: (ExplState, R) -> ExplState
    ) = Domain<ExplState, StmtAction, ExplPrec, R, Unit>(
        stateOrd = ExplOrd.getInstance(),
        extendPrec = { p, e ->
            p.join(ExplPrec.of(ExprUtils.getVars(e)))
        },
        refineState = refine,
        abstractFromExpr = { e, _, p ->
            ExprStates.createStatesForExpr(
                solver, e, 0,
                p::createState,
                VarIndexingFactory.indexing(0)
            ).first() // TODO: handle non-det
        },
        abstractFromValuation = { v, _, p ->
            p.createState(v)
        },
        extractStructure = {},
        transFunc = ExplStmtTransFunc.create(solver, 0),
        linkedTransFunc = ExplLinkedTransFunc(maxEnum, solver),
        maySats = ::explMaySatisfy,
        mustSats = ::explMustSatisfy,
        getGuardSatisfactionConfigs = explGetGuardSatisfactionConfigs(solver)
    )

    fun ExplDomainWithValRef(
        solver: Solver,
        maxEnum: Int = 0
    ) = explDomain<Valuation>(solver, maxEnum) { s, v ->
        val sMap = s.`val`.toMap()
        val vMap = v.toMap()
        val newVal = MutableValuation.copyOf(v)
        for ((key, value) in sMap) {
            if (key in vMap && value != vMap[key]) {
                throw IllegalArgumentException("Inconsistent state refinement")
            }
            newVal.put(key, value)
        }
        ExplState.of(newVal)
    }

    fun ExplDomainWithExprRef(
        solver: Solver,
        maxEnum: Int = 0
    ) = explDomain<Expr<BoolType>>(solver, maxEnum) { s, e ->
        val combinedExpr = And(s.toExpr(), e)
        ExprStates.createStatesForExpr(
            solver,
            combinedExpr,
            0,
            ExplPrec.of(ExprUtils.getVars(combinedExpr))::createState,
            VarIndexingFactory.indexing(0)
        ).let {
            if (it.isEmpty()) { throw IllegalArgumentException("Inconsistent state refinement") }
            if (it.size > 1) { TODO("I was afraid this would happen...") }
            it.first()
        }
    }
}