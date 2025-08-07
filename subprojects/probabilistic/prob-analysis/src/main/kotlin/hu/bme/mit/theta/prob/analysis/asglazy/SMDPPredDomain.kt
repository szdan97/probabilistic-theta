package hu.bme.mit.theta.prob.analysis.asglazy

import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.TransFunc
import hu.bme.mit.theta.analysis.expl.ExplPrec
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceSeqItpChecker
import hu.bme.mit.theta.analysis.pred.ExprSplitters.ExprSplitter
import hu.bme.mit.theta.analysis.pred.PredOrd
import hu.bme.mit.theta.analysis.pred.PredState
import hu.bme.mit.theta.core.stmt.Stmts
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.core.utils.WpState
import hu.bme.mit.theta.prob.analysis.BasicStmtAction
import hu.bme.mit.theta.prob.analysis.ProbabilisticCommand
import hu.bme.mit.theta.prob.analysis.jani.SMDPCommandAction
import hu.bme.mit.theta.prob.analysis.jani.SMDPState
import hu.bme.mit.theta.prob.analysis.jani.nextLocs
import hu.bme.mit.theta.solver.ItpSolver
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.UCSolver
import hu.bme.mit.theta.solver.utils.WithPushPop

class SMDPPredDomain(
    val domainTransFunc: TransFunc<ExplState, StmtAction, ExplPrec>,
    val fullPrec: ExplPrec,
    val smtSolver: Solver,
    val itpSolver: ItpSolver,
    val ucSolver: UCSolver,
    val useItp: Boolean,
    val exprSplitter: ExprSplitter
): LazyDomain<SMDPState<ExplState>, SMDPState<PredState>, SMDPCommandAction> {
    val ord = PredOrd.create(smtSolver)

    override fun checkContainment(sc: SMDPState<ExplState>, sa: SMDPState<PredState>): Boolean {
        if (sc.locs != sa.locs)
            return false

        val res = sa.toExpr().eval(sc.domainState)
        return if (res == True()) true
        else if (res == BoolExprs.False()) false
        else throw IllegalArgumentException("concrete state must be a full valuation")
    }

    override fun isLeq(sa1: SMDPState<PredState>, sa2: SMDPState<PredState>) =
        sa1.locs == sa2.locs &&
                ord.isLeq(sa1.domainState, sa2.domainState)

    override fun mayBeEnabled(state: SMDPState<PredState>, command: ProbabilisticCommand<SMDPCommandAction>): Boolean {
        WithPushPop(smtSolver).use {
            smtSolver.add(PathUtils.unfold(state.toExpr(), 0))
            smtSolver.add(PathUtils.unfold(command.guard, 0))
            return smtSolver.check().isSat
        }
    }

    override fun mustBeEnabled(state: SMDPState<PredState>, command: ProbabilisticCommand<SMDPCommandAction>): Boolean {
        WithPushPop(smtSolver).use {
            smtSolver.add(PathUtils.unfold(state.toExpr(), 0))
            smtSolver.add(PathUtils.unfold(BoolExprs.Not(command.guard), 0))
            return smtSolver.check().isUnsat
        }
    }

    override fun block(
        abstrState: SMDPState<PredState>,
        expr: Expr<BoolType>,
        concrState: SMDPState<ExplState>
    ): SMDPState<PredState> {
        require(checkContainment(concrState, abstrState)) {
            "Block failed: Concrete state $concrState not contained in abstract state $abstrState!"
        }
        require(expr.eval(concrState.domainState) == BoolExprs.False()) {
            "Block failed: Concrete state $concrState does not contradict $expr"
        }

        val newAbstract = if (useItp) {
            lateinit var itp: Expr<BoolType>
            WithPushPop(itpSolver).use {
                val A = itpSolver.createMarker()
                val B = itpSolver.createMarker()
                itpSolver.add(A, PathUtils.unfold(concrState.toExpr(), 0))
                itpSolver.add(B, PathUtils.unfold(expr, 0))
                val pattern = itpSolver.createBinPattern(A, B)
                if (itpSolver.check().isSat)
                    throw IllegalArgumentException("Block failed: Concrete state $concrState does not contradict $expr")
                itp = PathUtils.foldin(itpSolver.getInterpolant(pattern).eval(A), 0)
            }

            val itpConjuncts = exprSplitter.apply(itp).map {
                val p = ExprUtils.ponate(it)
                val truth = (p.eval(concrState.domainState) as BoolLitExpr).value
                if(truth) p
                else SmartBoolExprs.Not(p)
            }
            /*
            val itpConjuncts = ExprUtils.getConjuncts(PathUtils.foldin(itp, 0)).filter {
                WithPushPop(smtSolver).use { _ ->
                    smtSolver.add(PathUtils.unfold(abstrState.toExpr(), 0))
                    smtSolver.add(PathUtils.unfold(BoolExprs.Not(it), 0))
                    smtSolver.check().isSat
                }
            }
             */
            val newConjuncts = abstrState.domainState.preds.toSet().union(itpConjuncts)

            PredState.of(newConjuncts)
        } else {
            val newPred = SmartBoolExprs.Not(expr)
            val addedConjuncts = exprSplitter.apply(newPred).map {
                val p = ExprUtils.ponate(it)
                val truth = (p.eval(concrState.domainState) as BoolLitExpr).value
                if(truth) p
                else SmartBoolExprs.Not(p)
            }
            val newConjuncts = abstrState.domainState.preds.toSet().union(addedConjuncts)
            PredState.of(newConjuncts)
            /*
            val newPred = ExprUtils.canonize(BoolExprs.Not(expr))
            if (abstrState.domainState.preds.contains(newPred)) abstrState.domainState
            else {
                val needed = WithPushPop(smtSolver).use {
                    smtSolver.add(PathUtils.unfold(abstrState.domainState.toExpr(), 0))
                    smtSolver.add(PathUtils.unfold(expr, 0))
                    smtSolver.check().isSat
                }
                if (needed) {
                    PredState.of(abstrState.domainState.preds + newPred)
                } else abstrState.domainState
            }
             */
        }

        return SMDPState(newAbstract, abstrState.locs)
    }

    override fun blockSeq(
        nodes: List<ASGLazyChecker<SMDPState<ExplState>, SMDPState<PredState>, SMDPCommandAction>.Node>,
        guards: List<Expr<BoolType>>,
        actions: List<SMDPCommandAction>,
        toBlockAtLast: Expr<BoolType>
    ): List<SMDPState<PredState>> {
        val seqItpChecker = ExprTraceSeqItpChecker.create(nodes.first().sc.toExpr(), toBlockAtLast, itpSolver)
//        val nwtChecker = ExprTraceNewtonChecker.create(True(), True(), ucSolver)
//            .withIT().withWP().withoutLV()
//        val states = listOf(nodes.first().sc) + nodes.drop(1).map { it.sa } + nodes.last().sa
        val states = nodes.map { it.sa }
        val actions = guards.zip(actions).map { (g: Expr<BoolType>, a: SMDPCommandAction) ->
            BasicStmtAction(listOf(Stmts.Assume(g)) + a.stmts)
        } //+ BasicStmtAction(listOf(Stmts.Assume(toBlockAtLast)))
        val trace = Trace.of(states, actions)
        val status = seqItpChecker.check(trace)
        if (status.isFeasible)
            throw RuntimeException("cannot block sequence")
        else {
            return nodes.zip(status.asInfeasible().refutation
                //.drop(1)
                .take(nodes.size)
            ).map { (node, itp) ->
//                val itpConjuncts = ExprUtils.getConjuncts(PathUtils.foldin(itp, 0))
//                    .map { ExprUtils.simplify(it) }
//                    .filter {
//                        WithPushPop(smtSolver).use { _ ->
//                            smtSolver.add(PathUtils.unfold(node.sa.toExpr(), 0))
//                            smtSolver.add(PathUtils.unfold(Not(it), 0))
//                            smtSolver.check().isSat
//                        }
//                    }
                val itpConjuncts = exprSplitter.apply(itp).map {
                    val p = ExprUtils.ponate(it)
                    val truth = (p.eval(node.sc.domainState) as BoolLitExpr).value
                    if(truth) p
                    else SmartBoolExprs.Not(p)
                }
                val newConjuncts = node.sa.domainState.preds.toSet().union(itpConjuncts)

                SMDPState(PredState.of(newConjuncts), node.sc.locs)
            }
        }
    }

    override fun postImage(
        state: SMDPState<PredState>,
        action: SMDPCommandAction,
        guard: Expr<BoolType>
    ): SMDPState<PredState> {
        TODO()
    }

    override fun preImage(state: SMDPState<PredState>, action: SMDPCommandAction): Expr<BoolType> =
        WpState.of(state.toExpr()).wep(Stmts.SequenceStmt(action.stmts)).expr

    override fun topAfter(state: SMDPState<PredState>, action: SMDPCommandAction): SMDPState<PredState> =
        SMDPState(PredState.of(), nextLocs(state.locs, action.destination))

    override fun isEnabled(state: SMDPState<ExplState>, command: ProbabilisticCommand<SMDPCommandAction>): Boolean {
        return command.guard.eval(state.domainState) == True()
    }

    override fun concreteTransFunc(state: SMDPState<ExplState>, action: SMDPCommandAction): SMDPState<ExplState> {
        val res = domainTransFunc.getSuccStates(
            state.domainState, action, fullPrec
        )
        require(res.size == 1) { "Concrete trans func returned multiple successor states :-(" }
        return SMDPState(res.first(), nextLocs(state.locs, action.destination))
    }
}