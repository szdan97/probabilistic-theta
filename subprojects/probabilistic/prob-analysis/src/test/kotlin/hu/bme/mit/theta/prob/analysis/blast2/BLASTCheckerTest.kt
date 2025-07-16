package hu.bme.mit.theta.prob.analysis.blast2

import hu.bme.mit.theta.analysis.InitFunc
import hu.bme.mit.theta.analysis.expl.ExplOrd
import hu.bme.mit.theta.analysis.expl.ExplPrec
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.analysis.pred.PredAbstractors
import hu.bme.mit.theta.analysis.pred.PredInitFunc
import hu.bme.mit.theta.analysis.pred.PredPrec
import hu.bme.mit.theta.analysis.pred.PredState
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.stmt.Stmts
import hu.bme.mit.theta.core.stmt.Stmts.Assign
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.inttype.IntExprs.*
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.prob.analysis.linkedtransfuncs.ExplLinkedTransFunc
import hu.bme.mit.theta.prob.analysis.linkedtransfuncs.PredLinkedTransFunc
import hu.bme.mit.theta.prob.analysis.menuabstraction.*
import hu.bme.mit.theta.solver.z3.Z3SolverFactory
import hu.bme.mit.theta.xta.analysis.expl.XtaExplUtils
import org.junit.Test

class BLASTCheckerTest {

    val A = Decls.Var("A", Int())
    val B = Decls.Var("B", Int())
    val C = Decls.Var("C", Int())
    val fullInit = createState(A to 0, B to 0, C to 0)

    lateinit var targetExpr: Expr<BoolType>
    val solver = Z3SolverFactory.getInstance().createSolver()
    val itpSolver = Z3SolverFactory.getInstance().createItpSolver()
    val ucSolver = Z3SolverFactory.getInstance().createUCSolver()

    val explInit = InitFunc<ExplState, ExplPrec> { prec -> listOf(prec.createState(fullInit)) }
    val innerPredInitFunc = PredInitFunc.create(PredAbstractors.booleanAbstractor(solver), fullInit.toExpr())
    val predInit = InitFunc<PredState, PredPrec> { prec -> innerPredInitFunc.getInitStates(prec) }

    lateinit var explLts: SimpleProbLTS<ExplState>
    lateinit var predLts: SimpleProbLTS<PredState>

    lateinit var explTransFunc: MenuGameTransFunc<ExplState, StmtAction, ExplPrec>
    lateinit var predTransFunc: MenuGameTransFunc<PredState, StmtAction, PredPrec>

    private fun simpleSetup() {
        // [A < 2 && B < 3]:
        // - 0.8: A:=A+1
        // - 0.2: B:=B+1
        // [C < 3]:
        // - 1.0: C:=C+1
        val commands = listOf(
            And(Lt(A.ref, Int(2)), Lt(B.ref, Int(1))).then(
                0.8 to Stmts.SequenceStmt(listOf(
                    Assign(A, Add(A.ref, Int(1))),
                    Assign(B, Add(B.ref, Int(1))),
                )),
                0.2 to Assign(B, Add(B.ref, Int(1)))
            ),
            Lt(C.ref, Int(3)).then(1.0 to Assign(C, Add(C.ref, Int(1))))
        )
        explLts = SimpleProbLTS(commands)
        predLts = SimpleProbLTS(commands)
        targetExpr = Eq(A.ref, Int(2))

        predTransFunc =
            BasicMenuGameTransFunc(
                PredLinkedTransFunc(solver),
                predCanBeDisabled(solver)
            )
        explTransFunc =
            BasicMenuGameTransFunc(
                ExplLinkedTransFunc(0, solver),
                ::explCanBeDisabled
            )
    }


    @Test
    fun menuExplExplorationTest() {
        simpleSetup()

        val initPrec = ExplPrec.of(listOf(A))
        val checker = BLASTChecker<
                MENUUnit<ExplState, StmtAction, ExplPrec>,
                ExplState, StmtAction, ExplPrec
                >(
            fullInit, explInit,
            {s,p -> MENUUnit(s, p, null,
                ExplOrd.getInstance(), explLts,
                explTransFunc, ::explMaySatisfy,
            ) },
            targetExpr,
            ::explMaySatisfy,
            {s, e -> XtaExplUtils.interpolate(s, e).toExpr() },
            {v, e -> XtaExplUtils.interpolate(v, e).toExpr()},
            {p, e -> p.join(ExplPrec.of(ExprUtils.getVars(e)))}
        )
        val root = checker.doInitialExploration(initPrec)
        val game = BlastMenuGame(root)
        val viz = game.materialize().materializedGame.visualize()
        val dot = GraphvizWriter.getInstance().writeString(viz)
        println(dot)
    }

}