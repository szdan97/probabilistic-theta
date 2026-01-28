package hu.bme.mit.theta.prob.analysis.blast2

import hu.bme.mit.theta.analysis.InitFunc
import hu.bme.mit.theta.analysis.expl.ExplOrd
import hu.bme.mit.theta.analysis.expl.ExplPrec
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.analysis.pred.*
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.stmt.Stmts.Assign
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.inttype.IntExprs.*
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.prob.analysis.ProbabilisticCommand
import hu.bme.mit.theta.prob.analysis.besttransformer.BasicBestTransformerTransFunc
import hu.bme.mit.theta.prob.analysis.besttransformer.BestTransformerTransFunc
import hu.bme.mit.theta.prob.analysis.besttransformer.explGetGuardSatisfactionConfigs
import hu.bme.mit.theta.prob.analysis.besttransformer.predGetGuardSatisfactionConfigs
import hu.bme.mit.theta.prob.analysis.linkedtransfuncs.ExplLinkedTransFunc
import hu.bme.mit.theta.prob.analysis.linkedtransfuncs.PredLinkedTransFunc
import hu.bme.mit.theta.prob.analysis.menuabstraction.*
import hu.bme.mit.theta.probabilistic.Goal
import hu.bme.mit.theta.probabilistic.gamesolvers.VISolver
import hu.bme.mit.theta.probabilistic.gamesolvers.initializers.TargetSetLowerInitializer
import hu.bme.mit.theta.solver.utils.WithPushPop
import hu.bme.mit.theta.solver.z3.Z3SolverFactory
import hu.bme.mit.theta.xta.analysis.expl.XtaExplUtils
import org.junit.Assert
import org.junit.Test
import java.awt.Color

private typealias ExplBTNode = BLASTBTGameNode<ExplState, StmtAction, ExplPrec>
private typealias ExplBTAction = BLASTBTGameAction<ExplState, StmtAction, ExplPrec>
private typealias ExplMenuNode = BLASTMENUGameNode<ExplState, StmtAction, ExplPrec>
private typealias ExplMenuAction = BLASTMENUGameAction<ExplState, StmtAction, ExplPrec>
private typealias PredBTNode = BLASTBTGameNode<PredState, StmtAction, PredPrec>
private typealias PredBTAction = BLASTBTGameAction<PredState, StmtAction, PredPrec>
private typealias PredMenuNode = BLASTMENUGameNode<PredState, StmtAction, PredPrec>
private typealias PredMenuAction = BLASTMENUGameAction<PredState, StmtAction, PredPrec>

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

    lateinit var explMenuTransFunc: MenuGameTransFunc<ExplState, StmtAction, ExplPrec>
    lateinit var predMenuTransFunc: MenuGameTransFunc<PredState, StmtAction, PredPrec>
    lateinit var explBTTransFunc: BestTransformerTransFunc<ExplState, StmtAction, ExplPrec>
    lateinit var predBTTransFunc: BestTransformerTransFunc<PredState, StmtAction, PredPrec>

    val exprSplitter = ExprSplitters.atoms()
    lateinit var commands: List<ProbabilisticCommand<StmtAction>>

    private fun simpleSetup() {
        // [A < 2 && B < 3]:
        // - 0.8: A:=A+1
        // - 0.2: B:=B+1
        // [C < 3]:
        // - 1.0: C:=C+1
        commands = listOf(
            And(Lt(A.ref, Int(2)), Lt(B.ref, Int(3))).then(
                0.8 to Assign(A, Add(A.ref, Int(1))),
                0.2 to Assign(B, Add(B.ref, Int(1)))
            ),
            Lt(C.ref, Int(3)).then(1.0 to Assign(C, Add(C.ref, Int(1))))
        )
        explLts = SimpleProbLTS(commands)
        predLts = SimpleProbLTS(commands)
        targetExpr = Eq(A.ref, Int(2))

        predMenuTransFunc =
            BasicMenuGameTransFunc(
                PredLinkedTransFunc(solver),
                predCanBeDisabled(solver)
            )
        explMenuTransFunc =
            BasicMenuGameTransFunc(
                ExplLinkedTransFunc(0, solver),
                ::explCanBeDisabled
            )
        predBTTransFunc =
            BasicBestTransformerTransFunc(
                PredLinkedTransFunc(solver),
                predGetGuardSatisfactionConfigs(solver)
            )
        explBTTransFunc =
            BasicBestTransformerTransFunc(
                ExplLinkedTransFunc(0, solver),
                explGetGuardSatisfactionConfigs(solver)
            )
    }

    @Test
    fun menuExplExplorationTest() {
        simpleSetup()

        val initPrec = ExplPrec.of(ExprUtils.getVars(targetExpr))
        val LReward = createBLASTMENUGameRewardFun<ExplState, StmtAction, ExplPrec>(
            originalGoal = Goal.MAX,  abstractionGoal = Goal.MIN
        )
        val UReward = createBLASTMENUGameRewardFun<ExplState, StmtAction, ExplPrec>(
            originalGoal = Goal.MAX,  abstractionGoal = Goal.MAX
        )
        // WARNING: explicit type parameters in the instantiations below seem totally unnecessary,
        //  but intellij and the kotlin compiler do not work without it
        //  deducing the types might be too complex. At least the BLASTChecker type paremeters can be omitted this way
        val checker = BLASTChecker(
            fullInit, explInit, { s, p ->
                MENUUnit(
                    s, p, null,
                    ExplOrd.getInstance(), explLts,
                    explMenuTransFunc, ::explMaySatisfy,
                )
            },
            targetExpr, ::explMaySatisfy,
            itpSolver,
            { v, e -> XtaExplUtils.interpolate(v, e).toExpr() },
            { p, e -> p.join(ExplPrec.of(ExprUtils.getVars(e))) },
            ::BlastMenuGame, VISolver<ExplMenuNode, ExplMenuAction>(1e-7),
            LReward, UReward,
            TargetSetLowerInitializer<ExplMenuNode, ExplMenuAction>(LReward.isTarget),
            TargetSetLowerInitializer<ExplMenuNode, ExplMenuAction>(UReward.isTarget)
        )
        val (numResult, finalGame) = checker.check(
            initPrec, Goal.MAX, 1e-6,
            { game, L, U ->
                println("Result: [${L[game.initialNode]}, ${U[game.initialNode]}]")
                val (materGame, materMap) = game.materialize()
                val invMatMap = materMap.entries.associate { it.value to it.key }
                val LM = materMap.entries.associate { it.value to L[it.key]!! }
                val UM = materMap.entries.associate { it.value to U[it.key]!! }
                val color = materMap.entries.associate {
                    it.value to if (LReward.isTarget(it.key)) Color.RED
                    else if (UReward.isTarget(it.key)) Color.ORANGE
                    else Color.WHITE
                }
                val viz = materGame.visualize(
                    LM, UM, color
                )
                //println(GraphvizWriter.getInstance().writeString(viz))
            }
        )
        val viz = finalGame.materialize().materializedGame.visualize()
        val dot = GraphvizWriter.getInstance().writeString(viz)
        println("Final result: $numResult")
        //println(dot)
        return
    }


    @Test
    fun btExplExplorationTest() {
        simpleSetup()

        val initPrec = ExplPrec.of(ExprUtils.getVars(targetExpr))
        val LReward = createBLASTBTGameRewardFunction<ExplState, StmtAction, ExplPrec>(Goal.MAX, Goal.MIN)
        val UReward = createBLASTBTGameRewardFunction<ExplState, StmtAction, ExplPrec>(Goal.MAX, Goal.MAX)
        val checker = BLASTChecker(
            fullInit, explInit,
            {s,p -> BTUnit(s, p,
                ExplOrd.getInstance(), explLts,
                explBTTransFunc, explGetGuardSatisfactionConfigs(solver)
            ) },
            targetExpr,
            ::explMaySatisfy,
            itpSolver,
            {v, e -> XtaExplUtils.interpolate(v, e).toExpr()},
            {p, e -> p.join(ExplPrec.of(ExprUtils.getVars(e)))},
            ::BLASTBTGame,
            VISolver<ExplBTNode, ExplBTAction>(1e-7, false),
            LReward, UReward,
            TargetSetLowerInitializer<ExplBTNode, ExplBTAction>(LReward.isTarget),
            TargetSetLowerInitializer<ExplBTNode, ExplBTAction>(UReward.isTarget)
        )

        val (numResult, finalGame) = checker.check(
            initPrec, Goal.MAX, 1e-6,
          { game, L, U ->
              println("Result: [${L[game.initialNode]}, ${U[game.initialNode]}]")
              val (materGame, materMap) = game.materialize()
              val invMatMap = materMap.entries.associate { it.value to it.key }
              val LM = materMap.entries.associate { it.value to L[it.key]!! }
              val UM = materMap.entries.associate { it.value to U[it.key]!! }
              val color = materMap.entries.associate {
                  it.value to if (LReward.isTarget(it.key)) Color.RED
                  else if (UReward.isTarget(it.key)) Color.ORANGE
                  else Color.WHITE
              }
              val viz = materGame.visualize(
                  LM, UM, color
              )
              //println(GraphvizWriter.getInstance().writeString(viz))
          }
        )
        println("Final result: $numResult")
    }

    private fun predRefute(s: PredState, e: Expr<BoolType>): Expr<BoolType> {
        WithPushPop(itpSolver).use {
            val A = itpSolver.createMarker()
            val B = itpSolver.createMarker()
            val pattern = itpSolver.createBinPattern(A, B)
            itpSolver.add(A, PathUtils.unfold(s.toExpr(), 0))
            itpSolver.add(B, PathUtils.unfold(e, 0))
            itpSolver.check()
            if(itpSolver.status.isSat) throw IllegalArgumentException("$s cannot refute $e")
            val itp = itpSolver.getInterpolant(pattern).eval(A)
            return PathUtils.foldin(itp, 0)
        }
    }

    @Test
    fun menuPredExplorationTest() {
        simpleSetup()

        val initPrec = PredPrec.of(targetExpr)
        val LReward = createBLASTMENUGameRewardFun<PredState, StmtAction, PredPrec>(
            originalGoal = Goal.MAX,  abstractionGoal = Goal.MIN
        )
        val UReward = createBLASTMENUGameRewardFun<PredState, StmtAction, PredPrec>(
            originalGoal = Goal.MAX,  abstractionGoal = Goal.MAX
        )
        // WARNING: explicit type parameters in the instantiations below seem totally unnecessary,
        //  but intellij and the kotlin compiler do not work without it
        //  deducing the types might be too complex. At least the BLASTChecker type paremeters can be omitted this way
        val checker = BLASTChecker(
            fullInit, predInit, { s, p ->
                MENUUnit(
                    s, p, null,
                    PredOrd.create(solver), predLts,
                    predMenuTransFunc, predMaySatisfy(solver),
                )
            },
            targetExpr, predMaySatisfy(solver),
            itpSolver,
            { v, e -> XtaExplUtils.interpolate(v, e).toExpr() },
            { p, e -> p.join(PredPrec.of(exprSplitter.apply(e))) },
            ::BlastMenuGame, VISolver<PredMenuNode, PredMenuAction>(1e-7),
            LReward, UReward,
            TargetSetLowerInitializer<PredMenuNode, PredMenuAction>(LReward.isTarget),
            TargetSetLowerInitializer<PredMenuNode, PredMenuAction>(UReward.isTarget)
        )
        val (numResult, finalGame) = checker.check(
            initPrec, Goal.MAX, 1e-6,
            { game, L, U ->
                println("Result: [${L[game.initialNode]}, ${U[game.initialNode]}]")
                val (materGame, materMap) = game.materialize()
                val invMatMap = materMap.entries.associate { it.value to it.key }
                val LM = materMap.entries.associate { it.value to L[it.key]!! }
                val UM = materMap.entries.associate { it.value to U[it.key]!! }
                val color = materMap.entries.associate {
                    it.value to if(LReward.isTarget(it.key)) Color.RED
                        else if(UReward.isTarget(it.key)) Color.ORANGE
                        else Color.WHITE
                }
                Assert.assertFalse(U[game.initialNode]!! < 0.972 || L[game.initialNode]!! > 0.973 )
                require(
                    game.getAllNodes().all { node ->
                        node.getOriginUnit()?.let { unit ->
                            if(unit.isCovered() || unit.mustBeTarget()) return@all true
                            if(unit.intermediateNodes.keys.toSet() != commands.filter {
                                    predMaySatisfy(unit.getState(), it.guard, solver)
                                }.toSet()) return@all false
                            return@all true
                            // TODO: check that the next results overapproximate the exact next
                        } ?: true
                    }
                )
                val viz = materGame.visualize(
                    LM, UM, color
                )
                //println(GraphvizWriter.getInstance().writeString(viz))
            }
        )
        // TODO: for some reason, the [L, U] interval does not get monotonically tighter
        val viz = finalGame.materialize().materializedGame.visualize()
        val dot = GraphvizWriter.getInstance().writeString(viz)
        println("Final result: $numResult")
        //println(dot)
    }


    @Test
    fun btPredExplorationTest() {
        simpleSetup()

        val initPrec = PredPrec.of(targetExpr)
        val LReward = createBLASTBTGameRewardFunction<PredState, StmtAction, PredPrec>(Goal.MAX, Goal.MIN)
        val UReward = createBLASTBTGameRewardFunction<PredState, StmtAction, PredPrec>(Goal.MAX, Goal.MAX)
        val checker = BLASTChecker(
            fullInit, predInit,
            {s,p -> BTUnit(s, p,
                PredOrd.create(solver), predLts,
                predBTTransFunc, predGetGuardSatisfactionConfigs(solver)
            ) },
            targetExpr,
            predMaySatisfy(solver),
            itpSolver,
            {v, e -> XtaExplUtils.interpolate(v, e).toExpr()},
            {p, e -> p.join(PredPrec.of(exprSplitter.apply(e)))},
            ::BLASTBTGame,
            VISolver<PredBTNode, PredBTAction>(1e-7, false),
            LReward, UReward,
            TargetSetLowerInitializer<PredBTNode, PredBTAction>(LReward.isTarget),
            TargetSetLowerInitializer<PredBTNode, PredBTAction>(UReward.isTarget)
        )

        val (numResult, finalGame) = checker.check(
            initPrec, Goal.MAX, 1e-6,
             { game, L, U ->
                println("Result: [${L[game.initialNode]}, ${U[game.initialNode]}]")
                val (materGame, materMap) = game.materialize()
                val invMatMap = materMap.entries.associate { it.value to it.key }
                val LM = materMap.entries.associate { it.value to L[it.key]!! }
                val UM = materMap.entries.associate { it.value to U[it.key]!! }
                val color = materMap.entries.associate {
                    it.value to if(LReward.isTarget(it.key)) Color.RED
                    else if(UReward.isTarget(it.key)) Color.ORANGE
                    else Color.WHITE
                }
                val viz = materGame.visualize(
                    LM, UM, color
                )
                //Assert.assertFalse(U[game.initialNode]!! < 0.972 || L[game.initialNode]!! > 0.973 )
                //println(GraphvizWriter.getInstance().writeString(viz))
            }, { game, L, U, numericPivot, refinementExpression ->
                val (materGame, materMap) = game.materialize()
                val invMatMap = materMap.entries.associate { it.value to it.key }
                val LM = materMap.entries.associate { it.value to L[it.key]!! }
                val UM = materMap.entries.associate { it.value to U[it.key]!! }
                val color = materMap.entries.associate {
                    it.value to if(LReward.isTarget(it.key)) Color.RED
                    else if(UReward.isTarget(it.key)) Color.ORANGE
                    else if(it.key == numericPivot) Color.YELLOW
                    //else if(it.key.getOriginUnit() == logicalPivotUnit) Color.GREEN
                    else Color.WHITE
                }
                val viz = materGame.visualize(
                    LM, UM, color
                )
                println("Numeric pivot: $numericPivot")
                println("Refinement expression: $refinementExpression")
                //println(GraphvizWriter.getInstance().writeString(viz))
            }
        )
        // TODO: for some reason, the [L, U] interval does not get monotonically tighter,
        //  and it is even unsound in some iterations, although the final one is correct
        println("Final result: $numResult")
    }
}