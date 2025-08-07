package hu.bme.mit.theta.prob.cli

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.parameters.options.default
import com.github.ajalt.clikt.parameters.options.flag
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.options.required
import com.github.ajalt.clikt.parameters.types.double
import com.github.ajalt.clikt.parameters.types.enum
import com.github.ajalt.clikt.parameters.types.int
import com.github.ajalt.clikt.parameters.types.restrictTo
import hu.bme.mit.theta.analysis.InitFunc
import hu.bme.mit.theta.analysis.PartialOrd
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.expl.ExplInitFunc
import hu.bme.mit.theta.analysis.expl.ExplOrd
import hu.bme.mit.theta.analysis.expl.ExplPrec
import hu.bme.mit.theta.analysis.expl.ItpRefToExplPrec
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.refinement.*
import hu.bme.mit.theta.analysis.pred.*
import hu.bme.mit.theta.analysis.pred.ExprSplitters.ExprSplitter
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.prob.analysis.Algorithm
import hu.bme.mit.theta.prob.analysis.ProbabilisticCommand
import hu.bme.mit.theta.prob.analysis.asglazy.SMDPLazyChecker
import hu.bme.mit.theta.prob.analysis.asglazy.SMDPLazyChecker.BRTDPStrategy.*
import hu.bme.mit.theta.prob.analysis.besttransformer.*
import hu.bme.mit.theta.prob.analysis.besttransformer.PivotSelectionStrategy
import hu.bme.mit.theta.prob.analysis.blast2.SMDPBLASTCheckerConfigs
import hu.bme.mit.theta.prob.analysis.direct.SMDPDirectChecker
import hu.bme.mit.theta.prob.analysis.direct.SMDPDirectCheckerGame
import hu.bme.mit.theta.prob.analysis.jani.*
import hu.bme.mit.theta.prob.analysis.jani.model.Model
import hu.bme.mit.theta.prob.analysis.jani.model.json.JaniModelMapper
import hu.bme.mit.theta.prob.analysis.linkedtransfuncs.ExplLinkedTransFunc
import hu.bme.mit.theta.prob.analysis.linkedtransfuncs.LinkedTransFunc
import hu.bme.mit.theta.prob.analysis.linkedtransfuncs.PredLinkedTransFunc
import hu.bme.mit.theta.prob.analysis.linkedtransfuncs.SMDPLinkedTransFunc
import hu.bme.mit.theta.prob.analysis.menuabstraction.*
import hu.bme.mit.theta.prob.analysis.menuabstraction.firstRefinable
import hu.bme.mit.theta.prob.cli.JaniCLI.Domain.*
import hu.bme.mit.theta.probabilistic.Goal
import hu.bme.mit.theta.probabilistic.StochasticGameSolver
import hu.bme.mit.theta.probabilistic.gamesolvers.*
import hu.bme.mit.theta.solver.ItpSolver
import hu.bme.mit.theta.solver.Solver
import hu.bme.mit.theta.solver.UCSolver
import hu.bme.mit.theta.solver.utils.WithPushPop
import hu.bme.mit.theta.solver.z3.Z3SolverFactory
import kotlin.io.path.Path

class JaniCLI : CliktCommand() {

    enum class Domain {
        PRED, EXPL, NONE
    }
    enum class Approximation(
        val useMayStandard: Boolean,
        val useMustStandard: Boolean,
        val useMayTarget: (Goal)->Boolean,
        val useMustTarget: (Goal)->Boolean
    ) {
        /**
         * Lower approximation of the possible behaviors, leading to lower power of the non-determinism.
         * Maximal values are approximated from below, minimal values from above.
         */
        LOWER(
            false,
            true,
            { when(it) {Goal.MAX -> false; Goal.MIN -> true } },
            { when(it) {Goal.MAX -> true; Goal.MIN -> false } }
        ),
        /**
         * Upper approximation of the possible behaviors, leading to higher power of the non-determinism.
         * Maximal values are approximated from above, minimal values from below.
         */
        UPPER(
            true,
            false,
            { when(it) {Goal.MAX -> true; Goal.MIN -> false } },
            { when(it) {Goal.MAX -> false; Goal.MIN -> true } }
            ),

        /**
         * Computes exact values for both minimal and maximal values.
         */
        EXACT(true, true, {true}, {true})
    }
    enum class AbstractionMethod() {
        LAZY, MENU_LAZY, MENU, BT,
        MENU_BLAST, BT_BLAST
    }
    enum class ExprSplitting(val exprSplitter: ExprSplitter) {
        WHOLE(ExprSplitters.whole()),
        CONJUNCTS(ExprSplitters.conjuncts()),
        ATOMS(ExprSplitters.atoms()),
    }

    val model: String by option("-m", "--model", "-i", "--input",
        help = "Path to the input JANI file."
    ).required()
    val visualize by option("--visualize", "-viz").flag()
    val analyze by option("--analyze").flag("--dontanalyze", default = true)
    val visoutput by option("--visoutput", "-vout")
    val parameters by option( "-p", "--parameters",
        help = "Specifies model parameters - constants which do not have values defined in the model."
    )
    val threshold by option(
        help = "Threshold used for convergence checking."
    ).double().default(1e-6)
    val algorithm by option(
        help = "MDP solver algorithm to use."
    ).enum<Algorithm>().default(Algorithm.BVI)
    val abstraction by option(
        help = "Abstraction method to use. Defaults to ASG-based lazy abstraction for backwards compatibility."
    ).enum<AbstractionMethod>().default(AbstractionMethod.LAZY)
    val domain by option(
        help = "Abstract domain to use. NONE means direct model checking without abstraction."
    ).enum<Domain>().required()
    val approximation by option(
        help = "Approximation direction to use."
    ).enum<Approximation>().required()
    val exactTarget by option("--exactTarget").flag(default = false)
    val property: String? by option(
        help = "Name of the JANI property to check. All properties are checked in sequence if not given."
    )
    val strategy by option(
        help = "Successor computation strategy for BRTDP."
    ).enum<SMDPLazyChecker.BRTDPStrategy>().default(DIFF_BASED)
    val verbose by option().flag()
    val preproc by option("--preproc",
        help = "Use qualitative preprocessing, i.e. precompute almost sure reachability and avoidance."
    ).flag("--nopreproc", default = true)
    val sequenceInterpolation by option("--seq",
        help = "Use sequence interpolation for refinement in lazy abstraction."
    ).flag("--noseq", default = true)
    val exprSplitting by option("--expr-splitting", "--split").enum<ExprSplitting>().default(ExprSplitting.ATOMS)
    val gameMultiRefinement by option("--multiref").int().restrictTo(min =1).default(1)
    val merge by option("--merge").flag("--nomerge", default = false)
    val eliminateSpurious by option("--elim",
        help = "Use interpolation to eliminate (almost-)spurious pivot nodes during game refinement." +
                "Only used for best transformer abstraction for now."
    ).flag("--no-elim", default = false)
    val resultOnly by option("--resultonly", "-res").flag("--allinfo", default = false)

    val debug by option("--debug").flag(default = false)

    fun log(message: String, isResult: Boolean = false) {
        if(isResult || !resultOnly)
            println(message)
    }

    override fun run() {

        val modelPath = Path(model)
        val parameters =
            parameters
                ?.split(",")
                ?.filter { it.isNotEmpty() }
                ?.map { it.split("=") }
                ?.associate { it[0] to it[1] }
                ?: mapOf()
        val model =
            JaniModelMapper()
                .readValue(modelPath.toFile(), Model::class.java)
                .toSMDP(parameters)
        val solver = Z3SolverFactory.getInstance().createSolver()
        val itpSolver = Z3SolverFactory.getInstance().createItpSolver()
        val ucSolver = Z3SolverFactory.getInstance().createUCSolver()

        if(visualize) {
            val g = model.visualize()
            if(visoutput?.isEmpty() ?: true) {
                val dot = GraphvizWriter.getInstance().writeString(g)
                println(dot)
            } else {
                GraphvizWriter.getInstance().writeFile(g, visoutput)
            }
        }
        if(!analyze) return

        for (prop in model.properties) {
            if(this.property != null && this.property != prop.name)
                continue
            if (prop is SMDPProperty.ProbabilityProperty || prop is SMDPProperty.ProbabilityThresholdProperty) {
                val (task, modifiedSMDP) =
                    try {
                        extractSMDPReachabilityTask(prop, model)
                    } catch (e: UnsupportedOperationException) {
                        if (this.property != null)
                            throw RuntimeException("Error: property ${prop.name} unsupported")
                        log("Error: property ${prop.name} unsupported, moving on")
                        continue
                    }
                val smdp = modifiedSMDP ?: model

                // TODO: correct config of may/must separately for standard and target commands should make approximate
                //  MIN computation correct, but this has not been sufficiently tested yet
                //if (task.goal == Goal.MIN && (domain != NONE && approximation != Approximation.EXACT))
                //    throw RuntimeException("Error: Approximate computation for MIN property ${prop.name} unsupported")

                val result = when (abstraction) {
                    AbstractionMethod.LAZY, AbstractionMethod.MENU_LAZY -> lazy(solver, itpSolver, ucSolver, task, smdp)
                    AbstractionMethod.MENU, AbstractionMethod.MENU_BLAST -> menu(solver, itpSolver, ucSolver, task, smdp)
                    AbstractionMethod.BT, AbstractionMethod.BT_BLAST -> bestTransformer(solver, itpSolver, ucSolver, task, smdp)
                }
                log("result: ${prop.name}: $result", true)
            } else if(prop is SMDPProperty.ExpectationProperty && domain == NONE) {
                val task = extractSMDPExpectedRewardTask(prop)
                val directChecker = SMDPDirectChecker(solver, verbose, preproc)
                val successorSelection = when (strategy) {
                    DIFF_BASED -> SMDPDirectCheckerGame::diffBasedSelection
                    RANDOM -> SMDPDirectCheckerGame::randomSelection
                    ROUND_ROBIN -> TODO()
                    WEIGHTED_RANDOM -> SMDPDirectCheckerGame::weightedRandomSelection
                }
                val quantSolver = when (algorithm) {
                    Algorithm.BVI -> MDPBVISolver(threshold)
                    Algorithm.VI -> VISolver(threshold)
                    Algorithm.BRTDP -> MDPBRTDPSolver(
                        successorSelection,
                        threshold
                    ) { iteration, reachedSet, linit, uinit ->
                        if (verbose) {
                            if(iteration % 1000 == 0) log("Iteration $iteration: [$linit, $uinit], ${reachedSet.size} nodes")
                        }
                    }
                }
                val result = directChecker.check(model, task, quantSolver)

                log("${prop.name}: $result")
            } else {
                if(this.property != null)
                    throw RuntimeException("Error: Non-probability property ${prop.name} unsupported")
                log("Non-probability property found")
            }
        }
    }

    private fun menu(
        solver: Solver,
        itpSolver: ItpSolver,
        ucSolver: UCSolver,
        task: SMDPReachabilityTask,
        model: SMDP
    ) : Double {
        val traceChecker =
            if(sequenceInterpolation) ExprTraceSeqItpChecker.create(model.getFullInitExpr(), BoolExprs.True(), itpSolver)
            else ExprTraceBwBinItpChecker.create(model.getFullInitExpr(), BoolExprs.True(), itpSolver)
        return when(domain) {
            PRED -> {
                val exprSplitter = ExprSplitters.atoms()
                return menuHelper(
                    solver,
                    itpSolver,
                    ucSolver,
                    task,
                    model,
                    PredInitFunc.create(
                        PredAbstractors.booleanSplitAbstractor(solver),
                        model.getFullInitExpr()
                    ),
                    PredLinkedTransFunc(solver),
                    smdpCanBeDisabled(predCanBeDisabled(solver)),
                    smdpMaySatisfy(predMaySatisfy(solver)),
                    smdpMustSatisfy(predMustSatisfy(solver)),
                    PredPrec.of(task.targetExpr),
                    {
                        this.join(PredPrec.of(exprSplitter.apply(it)))
                    },
                    eliminateSpurious,
                    traceChecker,
                    ItpRefToPredPrec(exprSplitter),
                    abstraction == AbstractionMethod.MENU_BLAST,
                    { p: PredPrec, e: Expr<BoolType> -> p.join(PredPrec.of(exprSplitter.apply(e))) },
                    PredOrd.create(solver),
                    SMDPBLASTCheckerConfigs.smdpPredRefute(itpSolver)
                )
            }
            EXPL -> menuHelper(
                solver,
                itpSolver,
                ucSolver,
                task,
                model,
                ExplInitFunc.create(
                    solver,
                    model.getFullInitExpr()
                ),
                ExplLinkedTransFunc(0, solver),
                smdpCanBeDisabled(::explCanBeDisabled),
                smdpMaySatisfy(::explMaySatisfy),
                smdpMustSatisfy(::explMustSatisfy),
                ExplPrec.of(ExprUtils.getVars(task.targetExpr)),
                {this.join(ExplPrec.of(ExprUtils.getVars(it)))},
                eliminateSpurious,
                traceChecker,
                ItpRefToExplPrec(),
                abstraction == AbstractionMethod.MENU_BLAST,
                { p: ExplPrec, e: Expr<BoolType> -> p.join(ExplPrec.of(ExprUtils.getVars(e))) },
                ExplOrd.getInstance(),
                SMDPBLASTCheckerConfigs::smdpExplRefute
            )
            NONE -> throw IllegalArgumentException("Domain must be selected for menu game abstraction")
        }
    }

    fun <N, A> createMDPSolver(algorithm: Algorithm, tolerance: Double): StochasticGameSolver<N, A> {
        return when (algorithm) {
            Algorithm.BRTDP -> TODO("Not yet implemented")
            Algorithm.VI -> VISolver<N, A>(tolerance)
            Algorithm.BVI -> MDPBVISolver<N, A>(tolerance)
        }
    }

    fun <N, A> createSGSolver(algorithm: Algorithm, tolerance: Double): StochasticGameSolver<N, A> {
        return when (algorithm) {
            Algorithm.BRTDP -> TODO("Not yet implemented")
            Algorithm.VI -> VISolver<N, A>(tolerance)
            Algorithm.BVI -> SGBVISolver<N, A>(tolerance)
        }
    }

    fun getFullInit(model: SMDP, solver: Solver): Valuation {
        val fullInit = model.getFullInitExpr().let { expr ->
            WithPushPop(solver).use {
                solver.add(PathUtils.unfold(expr, 0))
                solver.check()
                solver.model
            }
        }
        return fullInit
    }

    private fun <D: ExprState, P: Prec, R: Refutation> menuHelper(
        solver: Solver,
        itpSolver: ItpSolver,
        ucSolver: UCSolver,
        task: SMDPReachabilityTask,
        model: SMDP,
        domainInitFunc: InitFunc<D, P>,
        domainTransFunc: LinkedTransFunc<D, SMDPCommandAction, P>,
        canBeDisabled: (SMDPState<D>, Expr<BoolType>) -> Boolean,
        maySatisfy: (SMDPState<D>, Expr<BoolType>) -> Boolean,
        mustSatisfy: (SMDPState<D>, Expr<BoolType>) -> Boolean,
        initPrec: P,
        extend: P.(basedOn: Expr<BoolType>) -> P,
        eliminateSpurious: Boolean,
        traceChecker: ExprTraceChecker<R>,
        refToPrec: RefutationToPrec<P, R>,
        useBLAST: Boolean = false,
        refinePrec: (P, Expr<BoolType>) -> P,
        domainPartialOrd: PartialOrd<D>,
        refute: (SMDPState<D>, Expr<BoolType>) -> Expr<BoolType>
    ): Double {
        val lts = SmdpCommandLts<D>(model)
        val initFunc = SmdpInitFunc<D, P>(domainInitFunc, model)
        val transFunc = BasicMenuGameTransFunc(SMDPLinkedTransFunc(domainTransFunc), canBeDisabled)
        val abstractor = MenuGameAbstractor(
            lts,
            initFunc,
            transFunc,
            task.targetExpr,
            maySatisfy,
            mustSatisfy,
            eliminateSpurious
        )

        val refiner = MenuGameRefiner<SMDPState<D>, SMDPCommandAction, P, R>(
            solver,
            extend,
            firstRefinable,
            eliminateSpurious,
            traceChecker,
            refToPrec
        )


        if(useBLAST) {
            val smdpOrd = SmdpOrd(domainPartialOrd)
            val checker = SMDPBLASTCheckerConfigs.MENU_GENERIC(
                task.goal,  getFullInit(model, solver), initFunc, smdpOrd, lts,
                transFunc, maySatisfy, task.targetExpr, refute,
                refinePrec, createSGSolver(algorithm, threshold)
            )
            return checker.check(initPrec, task.goal, threshold).first
        }
        else {
            val checker = MenuGameCegarChecker(
                abstractor,
                refiner,
                createSGSolver(algorithm, threshold)
            )
            return checker.check(initPrec, task.goal, threshold).finalUpperInitValue
        }
    }

    private fun bestTransformer(
        solver: Solver,
        itpSolver: ItpSolver,
        ucSolver: UCSolver,
        task: SMDPReachabilityTask,
        model: SMDP
    ): Double {
        val traceChecker =
            if(sequenceInterpolation) ExprTraceSeqItpChecker.create(model.getFullInitExpr(), BoolExprs.True(), itpSolver)
            else ExprTraceBwBinItpChecker.create(model.getFullInitExpr(), BoolExprs.True(), itpSolver)
        return when(domain) {
            PRED -> {
                val exprSplitter = ExprSplitters.atoms()
                bestTransformerHelper(
                    solver, itpSolver, ucSolver, task, model,
                    PredInitFunc.create(
                        PredAbstractors.booleanSplitAbstractor(solver),
                        model.getFullInitExpr()
                    ),
                    PredLinkedTransFunc(solver),
                    smdpGetGuardSatisfactionConfigs(predGetGuardSatisfactionConfigs(solver)),
                    smdpMaySatisfy(predMaySatisfy(solver)),
                    smdpMustSatisfy(predMustSatisfy(solver)),
                    PredPrec.of(task.targetExpr),
                    { this.join(PredPrec.of(exprSplitter.apply(it))) },
                    ReachableMostUncertain(),
                    eliminateSpurious,
                    traceChecker,
                    ItpRefToPredPrec(exprSplitter),
                    abstraction == AbstractionMethod.BT_BLAST,
                    { p: PredPrec, e: Expr<BoolType> -> p.join(PredPrec.of(exprSplitter.apply(e))) },
                    PredOrd.create(solver),
                    SMDPBLASTCheckerConfigs.smdpPredRefute(itpSolver)
                )
            }
            EXPL -> bestTransformerHelper(
                solver, itpSolver, ucSolver, task, model,
                ExplInitFunc.create(
                    solver,
                    model.getFullInitExpr()
                ),
                ExplLinkedTransFunc(0, solver),
                smdpGetGuardSatisfactionConfigs(explGetGuardSatisfactionConfigs(solver)),
                smdpMaySatisfy(::explMaySatisfy),
                smdpMustSatisfy(::explMustSatisfy),
                ExplPrec.of(ExprUtils.getVars(task.targetExpr)),
                {this.join(ExplPrec.of(ExprUtils.getVars(it)))},
                ReachableMostUncertain(),
                eliminateSpurious,
                traceChecker,
                ItpRefToExplPrec(),
                abstraction == AbstractionMethod.BT_BLAST,
                { p: ExplPrec, e: Expr<BoolType> -> p.join(ExplPrec.of(ExprUtils.getVars(e))) },
                ExplOrd.getInstance(),
                SMDPBLASTCheckerConfigs::smdpExplRefute
            )

            NONE -> throw IllegalArgumentException("Domain must be selected for best transformer game abstraction")
        }
    }

    private fun <D: ExprState, P: Prec, R: Refutation> bestTransformerHelper(
        solver: Solver,
        itpSolver: ItpSolver,
        ucSolver: UCSolver,
        task: SMDPReachabilityTask,
        model: SMDP,
        domainInitFunc: InitFunc<D, P>,
        domainTransFunc: LinkedTransFunc<D, SMDPCommandAction, P>,
        getGuardSatisfactionConfigs: (SMDPState<D>, List<ProbabilisticCommand<SMDPCommandAction>>) -> List<List<ProbabilisticCommand<SMDPCommandAction>>>,
        maySatisfy: (SMDPState<D>, Expr<BoolType>) -> Boolean,
        mustSatisfy: (SMDPState<D>, Expr<BoolType>) -> Boolean,
        initPrec: P,
        extend: P.(basedOn: Expr<BoolType>) -> P,
        pivotSelectionStrategy: PivotSelectionStrategy,
        eliminateSpurious: Boolean,
        traceChecker: ExprTraceChecker<R>,
        refToPrec: RefutationToPrec<P, R>,
        useBLAST: Boolean = false,
        refinePrec: (P, Expr<BoolType>) -> P,
        domainPartialOrd: PartialOrd<D>,
        refute: (SMDPState<D>, Expr<BoolType>) -> Expr<BoolType>
    ): Double {
        val lts = SmdpCommandLts<D>(model)
        val initFunc = SmdpInitFunc<D, P>(domainInitFunc, model)
        val transFunc = BasicBestTransformerTransFunc(SMDPLinkedTransFunc(domainTransFunc), getGuardSatisfactionConfigs)
        val abstractor = BestTransformerAbstractor(
            lts,
            initFunc,
            transFunc,
            task.targetExpr,
            maySatisfy,
            mustSatisfy,
            eliminateSpurious
        )

        val refiner = BestTransformerRefiner<SMDPState<D>, SMDPCommandAction, P, R>(
            solver,
            extend,
            pivotSelectionStrategy,
            eliminateSpurious,
            traceChecker,
            refToPrec
        )

        if(useBLAST) {
            val smdpOrd = SmdpOrd(domainPartialOrd)
            val checker = SMDPBLASTCheckerConfigs.BT_GENERIC(
                task.goal,  getFullInit(model, solver), initFunc, smdpOrd, lts,
                transFunc, maySatisfy, task.targetExpr, refute,
                refinePrec, createSGSolver(algorithm, threshold)
            )
            return checker.check(initPrec, task.goal, threshold).first
        }
        else {
            val checker = BestTransformerCegarChecker(
                abstractor,
                refiner,
                createSGSolver(algorithm, threshold)
            )
            return checker.check(initPrec, task.goal, threshold).finalUpperInitValue
        }
    }

    private fun lazy(
        solver: Solver,
        itpSolver: ItpSolver,
        ucSolver: UCSolver,
        task: SMDPReachabilityTask,
        model: SMDP
    ): Double {
        val preproc = if (algorithm == Algorithm.BRTDP) false else preproc

        val lazyChecker = SMDPLazyChecker(
            solver,
            itpSolver,
            ucSolver,
            algorithm,
            verbose,
            strategy,
            approximation.useMayStandard,
            approximation.useMustStandard,
            exactTarget || approximation.useMayTarget(task.goal),
            exactTarget || approximation.useMustTarget(task.goal),
            threshold,
            sequenceInterpolation,
            this.abstraction == AbstractionMethod.MENU_LAZY,
            preproc,
            merge,
            exprSplitting.exprSplitter,
            gameMultiRefinement
        )

        if (model.getAllVars().size < 30) {
            ImmutableValuation.experimental = true
            ImmutableValuation.declOrder = model.getAllVars().toTypedArray()
        }

        val directChecker = SMDPDirectChecker(solver, verbose, preproc)
        val successorSelection = when (strategy) {
            DIFF_BASED -> SMDPDirectCheckerGame::diffBasedSelection
            RANDOM -> SMDPDirectCheckerGame::randomSelection
            ROUND_ROBIN -> TODO()
            WEIGHTED_RANDOM -> SMDPDirectCheckerGame::weightedRandomSelection
        }
        val quantSolverSupplier = when (algorithm) {
            Algorithm.BVI -> MDPBVISolver(threshold)
            Algorithm.VI -> VISolver(threshold)
            Algorithm.BRTDP -> MDPBRTDPSolver(
                successorSelection,
                threshold
            ) { iteration, reachedSet, linit, uinit ->
                if (verbose) {
                    if(iteration % 1000 == 0) log("Iteration $iteration: [$linit, $uinit], ${reachedSet.size} nodes")
                }
            }
        }

        val result = when (domain) {
            PRED -> lazyChecker.checkPred(model, task)
            EXPL -> lazyChecker.checkExpl(model, task)
            NONE -> directChecker.check(model, task, quantSolverSupplier)
        }
        return result
    }
}

fun main(args: Array<String>) = JaniCLI().main(args)