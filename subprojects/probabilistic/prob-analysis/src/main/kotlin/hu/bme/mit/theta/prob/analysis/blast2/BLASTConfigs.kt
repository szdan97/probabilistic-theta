package hu.bme.mit.theta.prob.analysis.blast2

import hu.bme.mit.theta.analysis.PartialOrd
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.expl.ExplInitFunc
import hu.bme.mit.theta.analysis.expl.ExplOrd
import hu.bme.mit.theta.analysis.expl.ExplPrec
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.pred.*
import hu.bme.mit.theta.analysis.pred.ExprSplitters.ExprSplitter
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.prob.analysis.besttransformer.*
import hu.bme.mit.theta.prob.analysis.jani.*
import hu.bme.mit.theta.prob.analysis.linkedtransfuncs.ExplLinkedTransFunc
import hu.bme.mit.theta.prob.analysis.linkedtransfuncs.PredLinkedTransFunc
import hu.bme.mit.theta.prob.analysis.linkedtransfuncs.SMDPLinkedTransFunc
import hu.bme.mit.theta.prob.analysis.menuabstraction.*
import hu.bme.mit.theta.probabilistic.Goal
import hu.bme.mit.theta.probabilistic.StochasticGameSolver
import hu.bme.mit.theta.probabilistic.gamesolvers.VISolver
import hu.bme.mit.theta.probabilistic.gamesolvers.initializers.TargetSetLowerInitializer
import hu.bme.mit.theta.solver.ItpSolver
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.utils.WithPushPop
import hu.bme.mit.theta.xta.analysis.expl.XtaExplUtils

private typealias SMDPExplBTNode = BLASTBTGameNode<SMDPState<ExplState>, SMDPCommandAction, ExplPrec>
private typealias SMDPExplBTAction = BLASTBTGameAction<SMDPState<ExplState>, SMDPCommandAction, ExplPrec>
private typealias SMDPExplMenuNode = BLASTMENUGameNode<SMDPState<ExplState>, SMDPCommandAction, ExplPrec>
private typealias SMDPExplMenuAction = BLASTMENUGameAction<SMDPState<ExplState>, SMDPCommandAction, ExplPrec>
private typealias SMDPPredBTNode = BLASTBTGameNode<SMDPState<PredState>, SMDPCommandAction, PredPrec>
private typealias SMDPPredBTAction = BLASTBTGameAction<SMDPState<PredState>, SMDPCommandAction, PredPrec>
private typealias SMDPPredMenuNode = BLASTMENUGameNode<SMDPState<PredState>, SMDPCommandAction, PredPrec>
private typealias SMDPPredMenuAction = BLASTMENUGameAction<SMDPState<PredState>, SMDPCommandAction, PredPrec>
private typealias SMDPGenericMenuNode<D, P> = BLASTMENUGameNode<SMDPState<D>, SMDPCommandAction, P>
private typealias SMDPGenericMenuAction<D, P> = BLASTMENUGameAction<SMDPState<D>, SMDPCommandAction, P>
private typealias SMDPGenericBTNode<D, P> = BLASTBTGameNode<SMDPState<D>, SMDPCommandAction, P>
private typealias SMDPGenericBTAction<D, P> = BLASTBTGameAction<SMDPState<D>, SMDPCommandAction, P>

object SMDPBLASTCheckerConfigs {

    fun <D: ExprState, P: Prec> MENU_GENERIC(
        goal: Goal,
        fullInit: Valuation,
        initFunc: SmdpInitFunc<D, P>,
        partialOrd: PartialOrd<SMDPState<D>>,
        lts: SmdpCommandLts<D>,
        transFunc: MenuGameTransFunc<SMDPState<D>, SMDPCommandAction, P>,
        maySatisfy: (SMDPState<D>, Expr<BoolType>) -> Boolean,
        targetExpr: Expr<BoolType>,
        refute: (SMDPState<D>, Expr<BoolType>) -> Expr<BoolType>,
        refinePrec: (P, Expr<BoolType>) -> P,
        quantSolver: StochasticGameSolver<SMDPGenericMenuNode<D, P>, SMDPGenericMenuAction<D, P>>
    ): BLASTChecker<
            MENUUnit<SMDPState<D>, SMDPCommandAction, P>, SMDPState<D>,
            SMDPCommandAction, P, SMDPGenericMenuNode<D,P>, SMDPGenericMenuAction<D,P>
            > {
        val LReward = createBLASTMENUGameRewardFun<SMDPState<D>, SMDPCommandAction, P>(
            originalGoal = goal,  abstractionGoal = Goal.MIN
        )
        val LInitializer = TargetSetLowerInitializer<SMDPGenericMenuNode<D, P>, SMDPGenericMenuAction<D, P>>(
            LReward.isTarget
        )
        val UReward = createBLASTMENUGameRewardFun<SMDPState<D>, SMDPCommandAction, P>(
            originalGoal = goal,  abstractionGoal = Goal.MAX
        )
        val UInitializer = TargetSetLowerInitializer<SMDPGenericMenuNode<D, P>, SMDPGenericMenuAction<D, P>>(
            UReward.isTarget
        )

        return BLASTChecker(
            fullInit, initFunc,
            { s, p ->
                MENUUnit(
                    s, p, null,
                    partialOrd, lts,
                    transFunc, maySatisfy
                )
            }, targetExpr, maySatisfy, refute,
            {v, e -> XtaExplUtils.interpolate(v, e).toExpr()},
            refinePrec, ::BlastMenuGame, quantSolver,
            LReward, UReward,
            LInitializer, UInitializer
        )
    }


    fun MENU_EXPL(
        // Input-related parameters
        goal: Goal,
        smdp: SMDP,
        targetExpr: Expr<BoolType>,

        // Dependencies
        solver: Solver,
    ): BLASTChecker<
            MENUUnit<SMDPState<ExplState>, SMDPCommandAction, ExplPrec>, SMDPState<ExplState>,
            SMDPCommandAction, ExplPrec, SMDPExplMenuNode, SMDPExplMenuAction
            > {
        // TODO: this is quite an ugly workaround, and SMDP should have an init valuation as well
        //  this will always give only a single init, so won't work if multiple inits are possible
        val fullInit = smdp.getFullInitExpr().let { expr ->
            WithPushPop(solver).use {
                solver.add(PathUtils.unfold(expr, 0))
                solver.check()
                solver.model
            }
        }
        val initFunc = SmdpInitFunc<ExplState, ExplPrec>(
            ExplInitFunc.create(solver, smdp.getFullInitExpr()), smdp
        )
        val lts = SmdpCommandLts<ExplState>(smdp)
        val transFunc = BasicMenuGameTransFunc(SMDPLinkedTransFunc(
            ExplLinkedTransFunc(0, solver)),
            smdpCanBeDisabled(::explCanBeDisabled)
        )
        val pord = SmdpOrd(ExplOrd.getInstance())
        val maySatisfy = smdpMaySatisfy(::explMaySatisfy)
        val quantSolver = VISolver<SMDPExplMenuNode, SMDPExplMenuAction>(1e-7)
        val refinePrec = { p: ExplPrec, e: Expr<BoolType> -> p.join(ExplPrec.of(ExprUtils.getVars(e))) }


        return MENU_GENERIC(
            goal, fullInit, initFunc,
            pord, lts, transFunc,
            maySatisfy, targetExpr,
            ::smdpExplRefute,
            refinePrec,
            quantSolver
        )
    }

    fun MENU_PRED(
        // Input-related parameters
        goal: Goal,
        smdp: SMDP,
        targetExpr: Expr<BoolType>,

        // Dependencies
        solver: Solver,
        itpSolver: ItpSolver,
        exprSplitter: ExprSplitter = ExprSplitters.atoms()
    ): BLASTChecker<
            MENUUnit<SMDPState<PredState>, SMDPCommandAction, PredPrec>, SMDPState<PredState>,
            SMDPCommandAction, PredPrec, SMDPPredMenuNode, SMDPPredMenuAction
            > {
        // TODO: this is quite an ugly workaround, and SMDP should have an init valuation as well
        //  this will always give only a single init, so won't work if multiple inits are possible
        val fullInit = smdp.getFullInitExpr().let { expr ->
            WithPushPop(solver).use {
                solver.add(PathUtils.unfold(expr, 0))
                solver.check()
                solver.model
            }
        }
        val initFunc = SmdpInitFunc<PredState, PredPrec>(
            PredInitFunc.create(
                PredAbstractors.booleanSplitAbstractor(solver), smdp.getFullInitExpr()
            ), smdp
        )
        val lts = SmdpCommandLts<PredState>(smdp)
        val transFunc = BasicMenuGameTransFunc(SMDPLinkedTransFunc(
            PredLinkedTransFunc(solver)),
            smdpCanBeDisabled(predCanBeDisabled(solver))
        )

        val pord = SmdpOrd(PredOrd.create(solver))
        val maySatisfy = smdpMaySatisfy(predMaySatisfy(solver))
        val refinePrec = { p: PredPrec, e: Expr<BoolType> -> p.join(PredPrec.of(exprSplitter.apply(e))) }
        val refute = smdpPredRefute(itpSolver)
        val quantSolver = VISolver<SMDPPredMenuNode, SMDPPredMenuAction>(1e-7)


        return MENU_GENERIC(
            goal, fullInit, initFunc,
            pord, lts, transFunc,
            maySatisfy, targetExpr,
            refute,
            refinePrec,
            quantSolver
        )
    }


    fun <D: ExprState, P: Prec> BT_GENERIC(
        goal: Goal,
        fullInit: Valuation,
        initFunc: SmdpInitFunc<D, P>,
        partialOrd: PartialOrd<SMDPState<D>>,
        lts: SmdpCommandLts<D>,
        transFunc: BestTransformerTransFunc<SMDPState<D>, SMDPCommandAction, P>,
        maySatisfy: (SMDPState<D>, Expr<BoolType>) -> Boolean,
        targetExpr: Expr<BoolType>,
        refute: (SMDPState<D>, Expr<BoolType>) -> Expr<BoolType>,
        refinePrec: (P, Expr<BoolType>) -> P,
        quantSolver: StochasticGameSolver<SMDPGenericBTNode<D, P>, SMDPGenericBTAction<D, P>>
    ): BLASTChecker<
            BTUnit<SMDPState<D>, SMDPCommandAction, P>, SMDPState<D>,
            SMDPCommandAction, P, SMDPGenericBTNode<D,P>, SMDPGenericBTAction<D,P>
            > {
        val LReward = createBLASTBTGameRewardFunction<SMDPState<D>, SMDPCommandAction, P>(
            originalGoal = goal,  abstractionGoal = Goal.MIN
        )
        val LInitializer = TargetSetLowerInitializer<SMDPGenericBTNode<D, P>, SMDPGenericBTAction<D, P>>(
            LReward.isTarget
        )
        val UReward = createBLASTBTGameRewardFunction<SMDPState<D>, SMDPCommandAction, P>(
            originalGoal = goal,  abstractionGoal = Goal.MAX
        )
        val UInitializer = TargetSetLowerInitializer<SMDPGenericBTNode<D, P>, SMDPGenericBTAction<D, P>>(
            UReward.isTarget
        )

        return BLASTChecker(
            fullInit, initFunc,
            { s, p ->
                BTUnit(
                    s, p,
                    partialOrd, lts,
                    transFunc
                )
            }, targetExpr, maySatisfy, refute,
            {v, e -> XtaExplUtils.interpolate(v, e).toExpr()},
            refinePrec, ::BLASTBTGame, quantSolver,
            LReward, UReward,
            LInitializer, UInitializer
        )
    }


    fun BT_EXPL(
        // Input-related parameters
        goal: Goal,
        smdp: SMDP,
        targetExpr: Expr<BoolType>,

        // Dependencies
        solver: Solver,
    ): BLASTChecker<
            BTUnit<SMDPState<ExplState>, SMDPCommandAction, ExplPrec>, SMDPState<ExplState>,
            SMDPCommandAction, ExplPrec, SMDPExplBTNode, SMDPExplBTAction
            > {
        // TODO: this is quite an ugly workaround, and SMDP should have an init valuation as well
        //  this will always give only a single init, so won't work if multiple inits are possible
        val fullInit = smdp.getFullInitExpr().let { expr ->
            WithPushPop(solver).use {
                solver.add(PathUtils.unfold(expr, 0))
                solver.check()
                solver.model
            }
        }
        val initFunc = SmdpInitFunc<ExplState, ExplPrec>(
            ExplInitFunc.create(solver, smdp.getFullInitExpr()), smdp
        )
        val lts = SmdpCommandLts<ExplState>(smdp)
        val transFunc = BasicBestTransformerTransFunc(SMDPLinkedTransFunc(
            ExplLinkedTransFunc(0, solver)),
            smdpGetGuardSatisfactionConfigs(explGetGuardSatisfactionConfigs(solver))
        )
        val pord = SmdpOrd(ExplOrd.getInstance())
        val maySatisfy = smdpMaySatisfy(::explMaySatisfy)
        val quantSolver = VISolver<SMDPExplBTNode, SMDPExplBTAction>(1e-7)
        val refinePrec = { p: ExplPrec, e: Expr<BoolType> -> p.join(ExplPrec.of(ExprUtils.getVars(e))) }

        return BT_GENERIC(
            goal, fullInit, initFunc,
            pord, lts, transFunc,
            maySatisfy, targetExpr,
            ::smdpExplRefute,
            refinePrec,
            quantSolver
        )
    }

    fun BT_PRED(
        // Input-related parameters
        goal: Goal,
        smdp: SMDP,
        targetExpr: Expr<BoolType>,

        // Dependencies
        solver: Solver,
        itpSolver: ItpSolver,
        exprSplitter: ExprSplitter = ExprSplitters.atoms()
    ): BLASTChecker<
            BTUnit<SMDPState<PredState>, SMDPCommandAction, PredPrec>, SMDPState<PredState>,
            SMDPCommandAction, PredPrec, SMDPPredBTNode, SMDPPredBTAction
            > {
        // TODO: this is quite an ugly workaround, and SMDP should have an init valuation as well
        //  this will always give only a single init, so won't work if multiple inits are possible
        val fullInit = smdp.getFullInitExpr().let { expr ->
            WithPushPop(solver).use {
                solver.add(PathUtils.unfold(expr, 0))
                solver.check()
                solver.model
            }
        }
        val initFunc = SmdpInitFunc<PredState, PredPrec>(
            PredInitFunc.create(
                PredAbstractors.booleanSplitAbstractor(solver), smdp.getFullInitExpr()
            ), smdp
        )
        val lts = SmdpCommandLts<PredState>(smdp)
        val transFunc = BasicBestTransformerTransFunc(SMDPLinkedTransFunc(
            PredLinkedTransFunc(solver)),
            smdpGetGuardSatisfactionConfigs(predGetGuardSatisfactionConfigs(solver))
        )

        val pord = SmdpOrd(PredOrd.create(solver))
        val maySatisfy = smdpMaySatisfy(predMaySatisfy(solver))
        val refinePrec = { p: PredPrec, e: Expr<BoolType> -> p.join(PredPrec.of(exprSplitter.apply(e))) }
        val refute = smdpPredRefute(itpSolver)
        val quantSolver = VISolver<SMDPPredBTNode, SMDPPredBTAction>(1e-7)

        return BT_GENERIC(
            goal, fullInit, initFunc,
            pord, lts, transFunc,
            maySatisfy, targetExpr,
            refute,
            refinePrec,
            quantSolver
        )
    }

    fun smdpExplRefute(s: SMDPState<ExplState>, e: Expr<BoolType>): Expr<BoolType> {
        return XtaExplUtils.interpolate(s.domainState, e).toExpr()
    }

    fun smdpPredRefute(itpSolver: ItpSolver) = fun(s: SMDPState<PredState>, e: Expr<BoolType>): Expr<BoolType> {
        WithPushPop(itpSolver).use {
            val A = itpSolver.createMarker()
            val B = itpSolver.createMarker()
            val pattern = itpSolver.createBinPattern(A, B)
            itpSolver.add(A, PathUtils.unfold(s.domainState.toExpr(), 0))
            itpSolver.add(B, PathUtils.unfold(e, 0))
            itpSolver.check()
            if(itpSolver.status.isSat) throw IllegalArgumentException("$s cannot refute $e")
            val itp = itpSolver.getInterpolant(pattern).eval(A)
            return PathUtils.foldin(itp, 0)
        }
    }

}
