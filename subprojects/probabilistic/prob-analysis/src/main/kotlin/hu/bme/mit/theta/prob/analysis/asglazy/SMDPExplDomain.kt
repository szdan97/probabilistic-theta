package hu.bme.mit.theta.prob.analysis.asglazy

import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.TransFunc
import hu.bme.mit.theta.analysis.expl.ExplOrd
import hu.bme.mit.theta.analysis.expl.ExplPrec
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expl.StmtApplier
import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceSeqItpChecker
import hu.bme.mit.theta.common.container.Containers
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.model.MutableValuation
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.stmt.Stmts
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.ExprSimplifier
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.WpState
import hu.bme.mit.theta.prob.analysis.BasicStmtAction
import hu.bme.mit.theta.prob.analysis.ProbabilisticCommand
import hu.bme.mit.theta.prob.analysis.jani.SMDPCommandAction
import hu.bme.mit.theta.prob.analysis.jani.SMDPState
import hu.bme.mit.theta.prob.analysis.jani.nextLocs
import hu.bme.mit.theta.solver.ItpSolver
import hu.bme.mit.theta.xta.analysis.expl.XtaExplUtils

class SMDPExplDomain(
    val domainTransFunc: TransFunc<ExplState, StmtAction, ExplPrec>,
    val fullPrec: ExplPrec,
    val itpSolver: ItpSolver
): LazyDomain<SMDPState<ExplState>, SMDPState<ExplState>, SMDPCommandAction> {

    override fun checkContainment(sc: SMDPState<ExplState>, sa: SMDPState<ExplState>): Boolean =
        sc.locs == sa.locs &&
                ExplOrd.getInstance().isLeq(sc.domainState, sa.domainState)

    override fun isLeq(sc: SMDPState<ExplState>, sa: SMDPState<ExplState>) =
        sc.locs == sa.locs &&
                ExplOrd.getInstance().isLeq(sc.domainState, sa.domainState)

    override fun mayBeEnabled(state: SMDPState<ExplState>, command: ProbabilisticCommand<SMDPCommandAction>): Boolean {
        val simplified = ExprSimplifier.simplify(command.guard, state.domainState)
        return simplified != BoolExprs.False()
    }

    override fun mustBeEnabled(state: SMDPState<ExplState>, command: ProbabilisticCommand<SMDPCommandAction>): Boolean {
        val simplified = ExprSimplifier.simplify(command.guard, state.domainState)
        return simplified == BoolExprs.True()
    }

    override fun block(
        abstrState: SMDPState<ExplState>,
        expr: Expr<BoolType>,
        concrState: SMDPState<ExplState>
    ): SMDPState<ExplState> {
        require(
            ExplOrd.getInstance().isLeq(concrState.domainState, abstrState.domainState) &&
                    concrState.locs == abstrState.locs
        ) {
            "Block failed: Concrete state $concrState not contained in abstract state $abstrState!"
        }
        require(expr.eval(concrState.domainState) == BoolExprs.False()) {
            "Block failed: Concrete state $concrState does not contradict $expr"
        }

        // Using backward strategy
        val valI = XtaExplUtils.interpolate(concrState.domainState, expr)

        val newVars: MutableCollection<Decl<*>> = Containers.createSet()
        newVars.addAll(valI.getDecls())
        newVars.addAll(abstrState.domainState.getDecls())
        val builder = ImmutableValuation.builder()
        for (decl in newVars) {
            builder.put(decl, concrState.domainState.eval(decl).get())
        }
        val `val`: Valuation = builder.build()
        val newAbstractExpl = SMDPState<ExplState>(ExplState.of(`val`), concrState.locs)

        return newAbstractExpl
    }

    override fun blockSeq(
        nodes: List<ASGLazyChecker<SMDPState<ExplState>, SMDPState<ExplState>, SMDPCommandAction>.Node>,
        guards: List<Expr<BoolType>>,
        actions: List<SMDPCommandAction>,
        toBlockAtLast: Expr<BoolType>
    ): List<SMDPState<ExplState>> {
        val seqItpChecker = ExprTraceSeqItpChecker.create(nodes.first().sc.toExpr(), toBlockAtLast, itpSolver)
        val states = nodes.map { it.sa }
        val actions = guards.zip(actions).map { (g: Expr<BoolType>, a: SMDPCommandAction) ->
            BasicStmtAction(listOf(Stmts.Assume(g)) + a.stmts)
        }
        val trace = Trace.of(states, actions)
        val status = seqItpChecker.check(trace)
        if (status.isFeasible) throw RuntimeException("cannot block sequence")
        else {
            return nodes.zip(status.asInfeasible().refutation).map { (node, itp) ->
                val newVars: MutableCollection<Decl<*>> = Containers.createSet()
                newVars.addAll(ExprUtils.getVars(itp))
                newVars.addAll(node.sa.domainState.getDecls())
                val builder = ImmutableValuation.builder()
                for (decl in newVars) {
                    builder.put(decl, node.sc.domainState.eval(decl).get())
                }
                val `val`: Valuation = builder.build()
                val newAbstractExpl = SMDPState<ExplState>(ExplState.of(`val`), node.sc.locs)
                newAbstractExpl
            }
        }
    }

    override fun postImage(
        state: SMDPState<ExplState>,
        action: SMDPCommandAction,
        guard: Expr<BoolType>
    ): SMDPState<ExplState> {
        val res = MutableValuation.copyOf(state.domainState.`val`)
        val stmts = listOf(Stmts.Assume(guard)) + action.stmts
        StmtApplier.apply(Stmts.SequenceStmt(stmts), res, true)
        return SMDPState(ExplState.of(res), nextLocs(state.locs, action.destination))
    }

    override fun preImage(state: SMDPState<ExplState>, action: SMDPCommandAction): Expr<BoolType> =
        WpState.of(state.toExpr()).wep(Stmts.SequenceStmt(action.stmts)).expr

    override fun topAfter(state: SMDPState<ExplState>, action: SMDPCommandAction): SMDPState<ExplState> =
        SMDPState(ExplState.top(), nextLocs(state.locs, action.destination))

    override fun isEnabled(s: SMDPState<ExplState>, probabilisticCommand: ProbabilisticCommand<SMDPCommandAction>): Boolean {
        return probabilisticCommand.guard.eval(s.domainState) == BoolExprs.True()
    }

    override fun concreteTransFunc(sc: SMDPState<ExplState>, a: SMDPCommandAction): SMDPState<ExplState> {
        val res = domainTransFunc.getSuccStates(
            sc.domainState, a, fullPrec
        )
        require(res.size == 1) { "Concrete trans func returned multiple successor states :-(" }
        return SMDPState(res.first(), nextLocs(sc.locs, a.destination))
    }
}