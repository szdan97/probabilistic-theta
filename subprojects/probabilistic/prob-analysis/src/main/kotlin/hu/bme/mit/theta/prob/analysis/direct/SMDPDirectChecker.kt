package hu.bme.mit.theta.prob.analysis.direct

import hu.bme.mit.theta.analysis.expl.ExplInitFunc
import hu.bme.mit.theta.analysis.expl.ExplPrec
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expl.ExplStmtTransFunc
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.rattype.RatLitExpr
import hu.bme.mit.theta.prob.analysis.ProbabilisticCommand
import hu.bme.mit.theta.prob.analysis.jani.*
import hu.bme.mit.theta.probabilistic.FiniteDistribution
import hu.bme.mit.theta.probabilistic.StochasticGame
import hu.bme.mit.theta.probabilistic.StochasticGameSolver
import hu.bme.mit.theta.solver.Solver

typealias SMDPDirectCheckerNode = DirectCheckerNode<SMDPState<ExplState>, SMDPCommandAction>
typealias SMDPDirectCheckerGame = StochasticGame<SMDPDirectCheckerNode, FiniteDistribution<SMDPDirectCheckerNode>>
class SMDPDirectChecker(
    val solver: Solver,
    val verboseLogging: Boolean = false,
    val useQualitativePreprocessing: Boolean = false
) {
    fun check(
        smdp: SMDP,
        smdpExpectedRewardTask: SMDPExpectedRewardTask,
        quantSolver: StochasticGameSolver<SMDPDirectCheckerNode, FiniteDistribution<SMDPDirectCheckerNode>>
    ): Double {
        val directChecker = getInnerCheckerFor(smdp, smdpExpectedRewardTask, quantSolver)
        return directChecker.check(smdpExpectedRewardTask.goal)
    }

    fun check(
        smdp: SMDP,
        smdpReachabilityTask: SMDPReachabilityTask,
        quantSolver: StochasticGameSolver<SMDPDirectCheckerNode, FiniteDistribution<SMDPDirectCheckerNode>>
    ): Double {
        val directChecker = getInnerCheckerFor(smdp, smdpReachabilityTask, quantSolver)
        return directChecker.check(smdpReachabilityTask.goal)
    }

    fun getInnerCheckerFor(
        smdp: SMDP,
        smdpExpectedRewardTask: SMDPExpectedRewardTask,
        quantSolver: StochasticGameSolver<SMDPDirectCheckerNode, FiniteDistribution<SMDPDirectCheckerNode>>
    ): DirectChecker<SMDPState<ExplState>, SMDPCommandAction> {
        val initFunc = SmdpInitFunc<ExplState, ExplPrec>(
            ExplInitFunc.create(solver, smdp.getFullInitExpr()),
            smdp
        )
        val fullPrec = ExplPrec.of(smdp.getAllVars())
        val initStates = initFunc.getInitStates(fullPrec)
        if (initStates.size != 1)
            throw RuntimeException("initial state must be deterministic")

        val smdpLts = SmdpCommandLts<ExplState>(smdp)
        fun commandsWithPrecondition(state: SMDPState<ExplState>) =
            smdpLts.getCommandsFor(state).map { it.withPrecondition(smdpExpectedRewardTask.constraint) }

        val transFunc = SMDPTransFunc(ExplStmtTransFunc.create(solver, 0))

        return DirectChecker<SMDPState<ExplState>, SMDPCommandAction>(
            ::commandsWithPrecondition,
            this::isEnabled,
            null,
            { s ->
                val ratLitExpr = smdpExpectedRewardTask.rewardExpr.eval(s.domainState) as RatLitExpr
                ratLitExpr.num.toDouble() / ratLitExpr.denom.toDouble()
            },
            smdpExpectedRewardTask.accumulateOnExit,
            smdpExpectedRewardTask.accumulateAfterStep,
            initStates.first(),
            transFunc,
            fullPrec,
            quantSolver,
            useQualitativePreprocessing,
            verboseLogging
        )
    }

    fun getInnerCheckerFor(
    smdp: SMDP,
    smdpReachabilityTask: SMDPReachabilityTask,
    quantSolver: StochasticGameSolver<SMDPDirectCheckerNode, FiniteDistribution<SMDPDirectCheckerNode>>
    ): DirectChecker<SMDPState<ExplState>, SMDPCommandAction> {
        val initFunc = SmdpInitFunc<ExplState, ExplPrec>(
            ExplInitFunc.create(solver, smdp.getFullInitExpr()),
            smdp
        )
        val fullPrec = ExplPrec.of(smdp.getAllVars())
        val initStates = initFunc.getInitStates(fullPrec)
        if(initStates.size != 1)
            throw RuntimeException("initial state must be deterministic")

        val smdpLts = SmdpCommandLts<ExplState>(smdp)
        fun commandsWithPrecondition(state: SMDPState<ExplState>) =
            smdpLts.getCommandsFor(state).map {
                it.withPrecondition(smdpReachabilityTask.constraint)
                    .extendWith(
                        smdpReachabilityTask.preStepAdditions,
                        smdpReachabilityTask.postStepAdditions
                    )
            }

        val transFunc = SMDPTransFunc(ExplStmtTransFunc.create(solver, 0))

        return DirectChecker<SMDPState<ExplState>, SMDPCommandAction>(
            ::commandsWithPrecondition,
            this::isEnabled,
            { s -> smdpReachabilityTask.targetExpr.eval(s.domainState) == True() },
            null,
            false,
            false,
            initStates.first(),
            transFunc,
            fullPrec,
            quantSolver,
            useQualitativePreprocessing,
            verboseLogging
        )
    }

    private fun isEnabled(state: SMDPState<ExplState>, cmd: ProbabilisticCommand<SMDPCommandAction>): Boolean {
        return cmd.guard.eval(state.domainState) == True()
    }
}