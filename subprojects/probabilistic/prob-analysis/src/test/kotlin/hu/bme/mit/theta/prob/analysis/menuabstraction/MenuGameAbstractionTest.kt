package hu.bme.mit.theta.prob.analysis.menuabstraction

import hu.bme.mit.theta.analysis.InitFunc
import hu.bme.mit.theta.analysis.expl.ExplOrd
import hu.bme.mit.theta.analysis.expl.ExplPrec
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation
import hu.bme.mit.theta.analysis.pred.PredAbstractors
import hu.bme.mit.theta.analysis.pred.PredInitFunc
import hu.bme.mit.theta.analysis.pred.PredPrec
import hu.bme.mit.theta.analysis.pred.PredState
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.stmt.Stmts.Assign
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.inttype.IntExprs.*
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.prob.analysis.P_ABSTRACTION
import hu.bme.mit.theta.prob.analysis.P_CONCRETE
import hu.bme.mit.theta.prob.analysis.linkedtransfuncs.ExplLinkedTransFunc
import hu.bme.mit.theta.prob.analysis.linkedtransfuncs.PredLinkedTransFunc
import hu.bme.mit.theta.probabilistic.AnalysisTask
import hu.bme.mit.theta.probabilistic.Goal
import hu.bme.mit.theta.probabilistic.StochasticGame
import hu.bme.mit.theta.probabilistic.gamesolvers.VISolver
import hu.bme.mit.theta.probabilistic.gamesolvers.initializers.TargetSetLowerInitializer
import hu.bme.mit.theta.probabilistic.setGoal
import hu.bme.mit.theta.solver.z3.Z3SolverFactory
import org.junit.Test
import java.awt.Color

class MenuGameAbstractionTest {

    val A = Decls.Var("A", Int())
    val B = Decls.Var("B", Int())
    val C = Decls.Var("C", Int())
    val fullInit = createState(A to 0, B to 0, C to 0)

    lateinit var targetExpr: Expr<BoolType>
    val solver = Z3SolverFactory.getInstance().createSolver()

    val explInit = InitFunc<ExplState, ExplPrec> { prec -> listOf(prec.createState(fullInit)) }
    val innerPredInitFunc = PredInitFunc.create(PredAbstractors.booleanAbstractor(solver), fullInit.toExpr())
    val predInit = InitFunc<PredState, PredPrec> { prec -> innerPredInitFunc.getInitStates(prec) }

    lateinit var explLts: SimpleProbLTS<ExplState>
    lateinit var predLts: SimpleProbLTS<PredState>

    lateinit var explTransFunc: MenuGameTransFunc<ExplState, StmtAction, ExplPrec>
    lateinit var predTransFunc: MenuGameTransFunc<PredState, StmtAction, PredPrec>
    lateinit var explAbstractor: MenuGameAbstractor<ExplState, StmtAction, ExplPrec>
    lateinit var predAbstractor: MenuGameAbstractor<PredState, StmtAction, PredPrec>

    private fun simpleSetup() {
        // [A < 2 && B < 3]:
        // - 0.8: A:=A+1
        // - 0.2: B:=B+1
        // [C < 3]:
        // - 1.0: C:=C+1
        val commands = listOf(
            And(Lt(A.ref, Int(2)), Lt(B.ref, Int(3))).then(
                0.8 to Assign(A, Add(A.ref, Int(1))),
                0.2 to Assign(B, Add(B.ref, Int(1)))
            ),
            Lt(C.ref, Int(3)).then(1.0 to Assign(C, Add(C.ref, Int(1))))
        )
        explLts = SimpleProbLTS(commands)
        predLts = SimpleProbLTS(commands)
        targetExpr = Eq(A.ref, Int(2))

        explTransFunc =
            BasicMenuGameTransFunc(
                ExplLinkedTransFunc(0, solver),
                ::explCanBeDisabled
            ) //deprecated: ExplMenuGameTransFunc(0, solver)
        explAbstractor = MenuGameAbstractor(
            explLts, explInit, explTransFunc,
            targetExpr,
            ::explMaySatisfy,
            ::explMustSatisfy
        )

        predTransFunc =
            BasicMenuGameTransFunc(
                PredLinkedTransFunc(solver),
                predCanBeDisabled(solver)
            )
        predAbstractor = MenuGameAbstractor(
            predLts, predInit, predTransFunc,
            targetExpr,
            predMaySatisfy(solver),
            predMustSatisfy(solver)
        )
    }

    private fun <S: ExprState> checkAndViz(abstraction: MenuGameAbstractor.AbstractionResult<S, StmtAction>) {
        val (lowerValues, upperValues) = computeValues(abstraction)

        // checked manually
        testViz(abstraction.game, lowerValues.first, upperValues.first)
    }

    private fun <S: ExprState> testViz(
        sg: StochasticGame<MenuGameNode<S, StmtAction>, MenuGameAction<S, StmtAction>>,
        lowerValues: Map<MenuGameNode<S, StmtAction>, Double>,
        upperValues: Map<MenuGameNode<S, StmtAction>, Double>
    ) {
        val materResult = sg.materialize()
        val viz = GraphvizWriter.getInstance().writeString(
            materResult.materializedGame.visualize(
                lowerValues.mapKeys { materResult.originalToMaterializedNodeMapping[it.key]!! },
                upperValues.mapKeys { materResult.originalToMaterializedNodeMapping[it.key]!! },
                sg.getAllNodes().filter {
                    it is MenuGameNode.StateNode && it.maxReward == 1
                }.map { materResult.originalToMaterializedNodeMapping[it]!! }.associateWith { Color(255, 150, 150) }
            )
        )
        println(viz)
    }

    private fun <S: ExprState> computeValues(
        abstraction: MenuGameAbstractor.AbstractionResult<S, StmtAction>
    ): Pair<
            Pair<
                    Map<MenuGameNode<S, StmtAction>, Double>,
                    Map<MenuGameNode<S, StmtAction>, MenuGameAction<S, StmtAction>>
                    >,
            Pair<
                    Map<MenuGameNode<S, StmtAction>, Double>,
                    Map<MenuGameNode<S, StmtAction>, MenuGameAction<S, StmtAction>>
                    >
            > {
        val lowerAnalysisTask =
            AnalysisTask(abstraction.game, setGoal(P_CONCRETE to Goal.MAX, P_ABSTRACTION to Goal.MIN), abstraction.rewardMin)
        val lowerSolution =
            VISolver<MenuGameNode<S, StmtAction>, MenuGameAction<S, StmtAction>>(
            1e-6,
            false
        ).solveWithStrategy(lowerAnalysisTask, TargetSetLowerInitializer {
                it is MenuGameNode.StateNode && abstraction.rewardMin(it) == 1.0
            })

        val upperAnalysisTask =
            AnalysisTask(abstraction.game, setGoal(P_CONCRETE to Goal.MAX, P_ABSTRACTION to Goal.MAX), abstraction.rewardMax)
        val upperSolution =
            VISolver<MenuGameNode<S, StmtAction>, MenuGameAction<S, StmtAction>>(
            1e-6,
            false
        ).solveWithStrategy(upperAnalysisTask, TargetSetLowerInitializer {
                it is MenuGameNode.StateNode && abstraction.rewardMax(it) == 1.0
            })
        return Pair(lowerSolution, upperSolution)
    }

    @Test
    fun explicitAllVarsAbstractionTest() {
        simpleSetup()
        val abstraction = explAbstractor.computeAbstraction(ExplPrec.of(listOf(A, B, C)))
        val sg = abstraction.game
        val nodes = sg.getAllNodes()

        // There cannot be any abstraction choice as all vars are tracked
        assert(nodes.all { it.player ==  P_CONCRETE || sg.getAvailableActions(it).size == 1})
        val initialNode = sg.initialNode
        assert(
            initialNode is MenuGameNode.StateNode &&
                    initialNode.s == createState(A to 0, B to 0, C to 0)
        )
        assert(sg.getAllNodes().none {
            sg.getAvailableActions(it).let { it.size > 1 && it.any { it is MenuGameAction.EnterTrap } }
        })

        checkAndViz(abstraction)
    }

    @Test
    fun explicit2VarsTest() {
        simpleSetup()
        val abstraction = explAbstractor.computeAbstraction(ExplPrec.of(listOf(A, B)))
        val sg = abstraction.game
        val initialNode = sg.initialNode
        assert(
            initialNode is MenuGameNode.StateNode &&
                    initialNode.s == createState(A to 0, B to 0)
        )

        checkAndViz(abstraction)
    }

    @Test
    fun explicit1VarTest() {
        simpleSetup()
        val abstraction = explAbstractor.computeAbstraction(ExplPrec.of(listOf(A)))
        val sg = abstraction.game

        val initialNode = sg.initialNode
        assert(initialNode is MenuGameNode.StateNode && initialNode.s == createState(A to 0))

        checkAndViz(abstraction)
    }

    @Test
    fun `more abstract node's interval should contain the interval of a less abstract node`() {
        simpleSetup()
        val abstraction1 = explAbstractor.computeAbstraction(ExplPrec.of(listOf(A)))
        val abstraction2 = explAbstractor.computeAbstraction(ExplPrec.of(listOf(A, B)))
        val abstraction3 = explAbstractor.computeAbstraction(ExplPrec.of(listOf(A, B, C)))

        val (lower1, upper1) = computeValues(abstraction1)
        val (lower2, upper2) = computeValues(abstraction2)
        val (lower3, upper3) = computeValues(abstraction3)

        for (refinedNode in abstraction2.game.getAllNodes()
            .filterIsInstance<MenuGameNode.StateNode<ExplState,StmtAction>>()) {
            val abstractNodes = abstraction1.game.getAllNodes()
                .filterIsInstance<MenuGameNode.StateNode<ExplState,StmtAction>>()
                .filter {
                    ExplOrd.getInstance().isLeq(refinedNode.s, it.s)
            }
            assert(abstractNodes.isNotEmpty())
            for (abstractNode in abstractNodes) {
                assert(lower2.first[refinedNode]!! >= lower1.first[abstractNode]!!)
                assert(upper2.first[refinedNode]!! <= upper1.first[abstractNode]!!)
            }
        }

        for (refinedNode in abstraction3.game.getAllNodes()
            .filterIsInstance<MenuGameNode.StateNode<ExplState,StmtAction>>()) {
            val abstractNodes = abstraction2.game.getAllNodes()
                .filterIsInstance<MenuGameNode.StateNode<ExplState,StmtAction>>()
                .filter {
                    ExplOrd.getInstance().isLeq(refinedNode.s, it.s)
            }
            assert(abstractNodes.isNotEmpty())
            for (abstractNode in abstractNodes) {
                assert(lower3.first[refinedNode]!! >= lower2.first[abstractNode]!!)
                assert(upper3.first[refinedNode]!! <= upper2.first[abstractNode]!!)
            }
        }
    }

    @Test
    fun refinerTestExpl() {
        simpleSetup()

        val initPrec = ExplPrec.of(listOf(A))
        val abstraction = explAbstractor.computeAbstraction(initPrec)
        val (lower, upper) = computeValues(abstraction)

        val refiner = MenuGameRefiner<ExplState, StmtAction, ExplPrec, ItpRefutation>(solver, {
            this.join(ExplPrec.of(ExprUtils.getVars(it)))
        }, firstRefinable)

        val (newPrec, pivot) = refiner.refine(
            abstraction.game,
            upper.first,
            lower.first,
            upper.second,
            lower.second,
            initPrec
        )
        println(pivot)
        println(newPrec)

        assert(newPrec == ExplPrec.of(listOf(A, B))) //C can be ignored, but B is needed for more precise result
    }

    @Test
    fun cegarTestExpl() {
        simpleSetup()
        val refiner = MenuGameRefiner<ExplState, StmtAction, ExplPrec, ItpRefutation>(solver, {
            this.join(ExplPrec.of(ExprUtils.getVars(it)))
        }, firstRefinable)

        val threshold = 1e-6
        val res = MenuGameCegarChecker(explAbstractor, refiner, VISolver(threshold/2, false))
            .check(ExplPrec.of(listOf(A)), Goal.MAX, threshold)

        println(res)
        assert(res.finalPrec == ExplPrec.of(listOf(A, B)))
        assert(res.finalUpperInitValue-res.finalLowerInitValue <= threshold)
    }

    @Test
    fun blastTestExpl() {
        simpleSetup()
        val refiner = MenuGameRefiner<ExplState, StmtAction, ExplPrec, ItpRefutation>(solver, {
            this.join(ExplPrec.of(ExprUtils.getVars(it)))
        }, firstRefinable)

        val threshold = 1e-6
        val res = MenuGameBLASTChecker(
            explLts, explInit, explTransFunc, targetExpr, ::explMaySatisfy, ::explMustSatisfy,
            ExplOrd.getInstance(), refiner, ExplPrec::join, VISolver(threshold/2, false))
            .check(ExplPrec.of(listOf(A)), Goal.MAX, threshold)

        println(res)
        //assert(res.finalPrec == ExplPrec.of(listOf(A, B)))
        assert(res.finalUpperInitValue-res.finalLowerInitValue <= threshold)
    }


    @Test
    fun predOnlyTargetTest() {
        simpleSetup()
        val prec = PredPrec.of(listOf(targetExpr))
        val abstraction = predAbstractor.computeAbstraction(prec)
        val sg = abstraction.game

        val initialNode = sg.initialNode
        assert(initialNode is MenuGameNode.StateNode && initialNode.s == PredState.of(prec.negate(targetExpr)))

        checkAndViz(abstraction)
    }

    @Test
    fun refinerTestPred() {
        simpleSetup()

        val initPrec = PredPrec.of(listOf(targetExpr))
        val abstraction = predAbstractor.computeAbstraction(initPrec)
        val (lower, upper) = computeValues(abstraction)

        val refiner = MenuGameRefiner<PredState, StmtAction, PredPrec, ItpRefutation>(solver, {
            this.join(PredPrec.of(ExprUtils.getAtoms(it)))
        }, firstRefinable)

        val (newPrec, pivot) = refiner.refine(
            abstraction.game,
            upper.first,
            lower.first,
            upper.second,
            lower.second,
            initPrec
        )
        println(pivot)
        println(newPrec)
    }

    @Test
    fun cegarTestPred() {
        simpleSetup()
        val refiner = MenuGameRefiner<PredState, StmtAction, PredPrec, ItpRefutation>(solver, {
            this.join(PredPrec.of(ExprUtils.getAtoms(it)))
        }, firstRefinable)

        val threshold = 1e-6
        val res = MenuGameCegarChecker(predAbstractor, refiner, VISolver(threshold/2, false))
            .check(PredPrec.of(listOf(targetExpr)), Goal.MAX, threshold)

        println(res)
        assert(res.finalUpperInitValue-res.finalLowerInitValue <= threshold)
    }
}