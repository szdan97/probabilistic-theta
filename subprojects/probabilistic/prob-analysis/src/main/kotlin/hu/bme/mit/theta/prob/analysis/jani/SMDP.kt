package hu.bme.mit.theta.prob.analysis.jani

import hu.bme.mit.theta.analysis.InitFunc
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.common.visualization.EdgeAttributes
import hu.bme.mit.theta.common.visualization.Graph
import hu.bme.mit.theta.common.visualization.NodeAttributes
import hu.bme.mit.theta.common.visualization.Shape
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.stmt.Stmts.SequenceStmt
import hu.bme.mit.theta.core.stmt.Stmts.SimultaneousStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs
import hu.bme.mit.theta.core.type.anytype.Exprs
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs
import hu.bme.mit.theta.core.type.inttype.IntExprs
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.type.rattype.RatExprs
import hu.bme.mit.theta.core.type.rattype.RatLitExpr
import hu.bme.mit.theta.core.type.rattype.RatType
import hu.bme.mit.theta.prob.analysis.ProbabilisticCommand
import hu.bme.mit.theta.prob.analysis.ProbabilisticCommandLTS
import hu.bme.mit.theta.prob.analysis.jani.SMDP.ActionLabel.InnerActionLabel
import hu.bme.mit.theta.prob.analysis.jani.SMDP.ActionLabel.StandardActionLabel
import hu.bme.mit.theta.probabilistic.FiniteDistribution
import hu.bme.mit.theta.probabilistic.Goal
import java.awt.Color

/**
 * A symbolic MDP class based on the MDP subset of JANI models.
 */
class SMDP(
    val globalVars: Collection<VarDecl<*>>,
    val automata: List<AutomatonInstance>,
    val syncVecs: List<List<StandardActionLabel?>>,
    val initExprs: Collection<Expr<BoolType>>,
    val properties: List<SMDPProperty>,
    val transientInitialValueMap: Map<VarDecl<*>, Expr<*>>,
    val constantsValuation: Valuation
) {
    class Location(
        val name: String,
        val outEdges: MutableList<Edge>,
        val parent: AutomatonInstance? = null,
        val transientMap: Map<VarDecl<*>, Expr<*>> = mapOf()
    ) {
        override fun toString(): String {
            return name
        }
    }
    sealed class ActionLabel(val name: String) {
        object InnerActionLabel : ActionLabel("<inner>")
        class StandardActionLabel(name: String) : ActionLabel(name)

        override fun toString(): String {
            return name
        }
    }
    class Assignment(val ref: VarDecl<*>, val expr: Expr<*>, val index: Int) {
        fun toStmt() =
            if(ref.type == expr.type)
                AssignStmt.create<Type>(ref, expr)
            // TODO: generalize this using castable
            else if(expr.type == IntType.getInstance() && ref.type == RatType.getInstance())
                AssignStmt.create<Type>(ref, IntExprs.ToRat(expr as Expr<IntType>) )
            else
                throw RuntimeException("$expr of type ${expr.type} cannot be assigned to $ref of type ${ref.type}")

        override fun toString(): String {
            return "($index) ${ref.name}=$expr"
        }

    }
    class Edge(
        val sourceLoc: Location,
        val guard: Expr<BoolType>,
        val action: ActionLabel?,
        val destinations: List<Destination>
    ) {
        init {sourceLoc.outEdges.add(this)}
    }
    class Destination(
        val probability: Expr<RatType>,
        val assignments: List<Assignment>,
        val loc: Location
    )
    data class ComposedDestination(
        val probability: Expr<RatType>,
        val assignments: List<Assignment>,
        val locs: List<Location>
    )

    class Automaton(
        val name: String,
        val locations: Collection<Location>,
        val initLocs: Collection<Location>,
        val actions: Collection<ActionLabel>,
        val localVars: Collection<VarDecl<*>>,
        val edges: Collection<Edge>,
        val initExprs: Collection<Expr<BoolType>>,
        val transientInitialValueMap: Map<VarDecl<*>, Expr<*>>
    ) { var numInstances = 0 }

    class AutomatonInstance(template: Automaton) {
        val id = template.numInstances++
        val name = "${template.name}_$id"

        private val varLUT = template.localVars.associateWith {
            Decls.Var(it.name+"_$id", it.type)
        }
        val localVars = varLUT.values.toList()

        val initExprs = template.initExprs.map(::replaceVars)

        val resetTransientsStmt: Stmt = SequenceStmt(
            template.transientInitialValueMap.entries.map {
                AssignStmt.create<Type>(varLUT[it.key]!!, replaceVars(it.value))
            }
        )

        private fun <T: Type> replaceVars(e: Expr<T>): Expr<T> =
            if (e is RefExpr) {
                val d = e.decl as Decl<T>
                if (d is VarDecl<T> && varLUT.containsKey(d)) Exprs.Ref(varLUT[d] as VarDecl<T>)
                else e
            } else {
                e.withOps(e.ops.map { replaceVars(it) })
            }

        private val locLUT = template.locations.associateWith {
            val replacedTransientMap = it.transientMap.entries.associate {
                if(varLUT.containsKey(it.key)) {
                    varLUT[it.key]!! to replaceVars(it.value)
                } else {
                    it.key to replaceVars(it.value)
                }
            }
            Location(it.name, arrayListOf(), this, replacedTransientMap)
        }

        val locs = locLUT.values.toList()
        val edges = template.edges.map { edge ->
            Edge(locLUT[edge.sourceLoc]!!, replaceVars(edge.guard), edge.action, edge.destinations.map { dest ->
                Destination(replaceVars(dest.probability), dest.assignments.map {
                    val newExpr = replaceVars(it.expr)
                    val newRef = if(varLUT.containsKey(it.ref)) varLUT[it.ref] else it.ref
                    Assignment(newRef as VarDecl<Type>, newExpr as Expr<Type>, it.index)
                }, locLUT[dest.loc]!!)
            })
        }

        val initLocs = template.initLocs.map { locLUT[it]!! }

        internal fun visualize(G: Graph) {
            var nextProbNodeId = 0
            val gid = this.name
            G.addCompositeNode(gid, NodeAttributes.builder()
                .shape(Shape.RECTANGLE)
                .label(this.name)
                .build()
            )
            val globalsid = gid+"_globals"
            G.addNode(gid+"_globals", NodeAttributes.builder()
                .shape(Shape.RECTANGLE)
                .label("vars: \n${localVars.map { "${it.name}: ${it.type}" }.joinToString("\n")}")
                .build())
            G.setChild(gid, globalsid)

            val locToId = hashMapOf<Location, String>()
            for (loc in locs) {
                val locid = gid+loc.name
                G.addNode(locid, NodeAttributes.builder()
                    .shape(Shape.CIRCLE).label(loc.name).build()
                )
                G.setChild(gid, gid+loc.name)
                locToId[loc] = locid
            }
            for (edge in edges) {
                val probNodeId = "${gid}_prob_${nextProbNodeId++}"
                G.addNode(probNodeId, NodeAttributes.builder()
                    .shape(Shape.RECTANGLE)
                    .fillColor(Color.GRAY)
                    .build())
                G.setChild(gid, probNodeId)
                G.addEdge(locToId[edge.sourceLoc]!!, probNodeId, EdgeAttributes.builder()
                    .label("[${edge.guard}]")
                    .build())
                for (destination in edge.destinations) {
                    G.addEdge(probNodeId, locToId[destination.loc]!!, EdgeAttributes.builder()
                        .label("${destination.probability}: ${destination.assignments}")
                        .build()
                    )
                }
            }
        }
    }

    fun resetTransientsStmt(): Stmt = SequenceStmt(transientInitialValueMap.entries.mapNotNull {
        AssignStmt.create<Type>(it.key, it.value)
    } + automata.map { it.resetTransientsStmt })

    fun getFullInitExpr(): Expr<BoolType> = SmartBoolExprs.And(
        (initExprs + automata.flatMap { it.initExprs }).ifEmpty { listOf(BoolExprs.True()) }
    )

    fun getAllVars() =
        globalVars + automata.flatMap(AutomatonInstance::localVars)

    fun visualize(): Graph {
        val G = Graph("Model", "Model")
        for (automaton in automata) {
            automaton.visualize(G)
        }
        val globalInfo = StringBuilder()
        globalInfo.appendLine("Global vars:")
        for (globalVar in globalVars) {
            globalInfo.appendLine("${globalVar.name}: ${globalVar.type}")
        }
        globalInfo.appendLine("Properties:")
        for (property in properties) {
            globalInfo.appendLine(property)
        }
        G.addNode("__global_info",
            NodeAttributes.builder()
                .shape(Shape.RECTANGLE)
                .label(globalInfo.toString())
                .build())
        return G
    }
}

data class SMDPState<D: ExprState>(
    val domainState: D,
    val locs: List<SMDP.Location>
): ExprState {
    override fun isBottom(): Boolean = domainState.isBottom

    override fun toExpr(): Expr<BoolType> {
        // TODO: maybe add the locs?
        return domainState.toExpr()
    }
}

data class SMDPExpectedRewardTask(
    val rewardExpr: Expr<RatType>,
    val goal: Goal,
    val negateResult: Boolean,
    val constraint: Expr<BoolType>,
    val accumulateOnExit: Boolean,
    val accumulateAfterStep: Boolean
)

data class SMDPReachabilityTask(
    val targetExpr: Expr<BoolType>,
    val goal: Goal,
    val negateResult: Boolean,
    val constraint: Expr<BoolType>,
    val preStepAdditions: List<Stmt>,
    val postStepAdditions: List<Stmt>
)

data class SMDPCommandAction(
    val destination: SMDP.ComposedDestination,
    val smdp: SMDP,
    val preActionStmts: List<Stmt> = listOf(),
    val postActionStmts: List<Stmt> = listOf()
) : StmtAction() {
    companion object {
        fun skipAt(locs: List<SMDP.Location>, smdp: SMDP) =
            SMDPCommandAction(
                SMDP.ComposedDestination(
                    RatExprs.Rat(1, 1),
                    listOf(),
                    locs
                ), smdp
            )
    }

    override fun getStmts() =
        preActionStmts +
        // Reset all transient variables
        listOf(smdp.resetTransientsStmt()) +
        // Then apply transition
        this.destination.assignments.groupBy { it.index }.toSortedMap().map {
            SimultaneousStmt(it.value.map(SMDP.Assignment::toStmt))
        } + postActionStmts +
        // then set all transient variables based on the target locations, if it gives them a value
        this.destination.locs.flatMap {
            it.transientMap.entries.map {
                AssignStmt.create<Type>(it.key, it.value)
            }
        }

    override fun toString(): String {
        return stmts.toString()
    }

    fun extendWith(
        newPreActionStmts: List<Stmt>,
        newPostActionStmts: List<Stmt>
    ) = SMDPCommandAction(
        destination, smdp,
        newPreActionStmts+this.preActionStmts,
        this.postActionStmts+newPostActionStmts
    )
}

fun ProbabilisticCommand<SMDPCommandAction>.extendWith(
    newPreActionStmts: List<Stmt>,
    newPostActionStmts: List<Stmt>
) = ProbabilisticCommand<SMDPCommandAction>(
    this.guard, this.result.transform {
        it.extendWith(newPreActionStmts, newPostActionStmts)
    }
)


class SmdpCommandLts<D: ExprState>(val smdp: SMDP): ProbabilisticCommandLTS<SMDPState<D>, SMDPCommandAction> {
    private val cache = hashMapOf<
            List<SMDP.Location>,
            List<ProbabilisticCommand<SMDPCommandAction>>
            >()

    private fun edgesToCommand(es: List<SMDP.Edge>, currState: SMDPState<*>): ProbabilisticCommand<SMDPCommandAction> {
        val fullGuard = SmartBoolExprs.And(es.map { it.guard })
        val resolutions = es.fold(listOf<List<SMDP.Destination>>(listOf())) { acc, curr ->
            acc.flatMap { prefix ->
                curr.destinations.map { new -> prefix + new  }
            }
        }
        val resultDistr = resolutions.associate {
            val probExpr = AbstractExprs.Mul(it.map(SMDP.Destination::probability)) as Expr<RatType>

            // TODO: replacing constant decls with their values should be done in the ModelToSMDP step
            val evaluated = probExpr.eval(smdp.constantsValuation) as RatLitExpr
            val prob = evaluated.num.toDouble() / evaluated.denom.toDouble()
            SMDPCommandAction(SMDP.ComposedDestination(
                probExpr,
                it.flatMap { it.assignments },
                nextLocs(currState.locs, it.map { it.loc })
            ), smdp) to prob
        }

        return ProbabilisticCommand(fullGuard, FiniteDistribution(resultDistr))
    }

    private fun computeCommands(state: SMDPState<D>): List<ProbabilisticCommand<SMDPCommandAction>> {
        val res = arrayListOf<ProbabilisticCommand<SMDPCommandAction>>()
        syncs@ for (syncVec in smdp.syncVecs) {
            var resolutions: List<List<SMDP.Edge>> = arrayListOf(listOf())
            parts@ for ((idx, action) in syncVec.withIndex()) {
                if(action == null) continue@parts

                val available = state.locs[idx].outEdges.filter { it.action == action }
                if(available.isEmpty()) continue@syncs
                resolutions = resolutions.flatMap { prev -> available.map { new -> prev + new } }
            }
            res.addAll(resolutions.map { edgesToCommand(it, state) })
        }

        val nonSyncEdges = state.locs.flatMapIndexed { idx, loc ->
            loc.outEdges.filter { it.action is InnerActionLabel }.map {
                edgesToCommand(listOf(it), state)
            }
        }
        res.addAll(nonSyncEdges)

        return res
    }

    fun getCommandsFor(state: SMDPState<D>): List<ProbabilisticCommand<SMDPCommandAction>> {
        return cache.computeIfAbsent(state.locs) { computeCommands(state) }
    }

    override fun getAvailableCommands(state: SMDPState<D>): Collection<ProbabilisticCommand<SMDPCommandAction>> {
        return getCommandsFor(state)
    }
}

class SmdpInitFunc<D: ExprState, P: Prec>(
    val subInitFunc: InitFunc<D, P>,
    val smdp: SMDP
): InitFunc<SMDPState<D>, P> {
    private fun computeLocConfigs(): List<List<SMDP.Location>> {
        val locLists = smdp.automata.map(SMDP.AutomatonInstance::initLocs)
        var res = listOf<List<SMDP.Location>>(listOf())
        for (locList in locLists) {
            val next = res.flatMap { prev -> locList.map { new -> prev+new } }
            res = next
        }
        return res
    }

    private val initLocConfigs = computeLocConfigs()

    override fun getInitStates(prec: P): Collection<SMDPState<D>> {
        return subInitFunc.getInitStates(prec).flatMap {
            initLocConfigs.map { initLocConfig -> SMDPState(it, initLocConfig) }
        }
    }
}

fun nextLocs(currLocs: List<SMDP.Location>, dest: SMDP.ComposedDestination): List<SMDP.Location> {
    return nextLocs(currLocs, dest.locs)
}


fun nextLocs(currLocs: List<SMDP.Location>, destLocs: List<SMDP.Location>): List<SMDP.Location> {
    val res = ArrayList(currLocs)
    for (loc in destLocs) {
        var i = -1
        for (currLoc in res) {
            i++
            if (currLoc.parent == loc.parent) break
        }
        res[i] = loc
    }
    return res
}

sealed class SMDPProperty(
    val name: String
) {
    class ProbabilityProperty(name: String, val optimType: Goal, val pathFormula: SMDPPathFormula) : SMDPProperty(name) {
        override fun toString(): String {
            return "$name: P_$optimType($pathFormula)=?"
        }
    }

    class ExpectationProperty(
        name: String, val optimType: Goal, val rewardExpr: Expr<RatType>, val until: Expr<BoolType>,
        val accumulateRewardOnExit: Boolean, val accumulateRewardAfterStep: Boolean
    ) : SMDPProperty(name) {
        override fun toString(): String {
            val acc = arrayListOf<String>()
            if(accumulateRewardOnExit) acc.add("exit")
            if(accumulateRewardAfterStep) acc.add("step")
            val U =
                if (until == BoolExprs.True()) ""
                else " U $until"
            return "$name: E_$optimType($rewardExpr$U)=? $acc"
        }
    }

    // TODO: accumulation?
    class SteadyStateProperty(name: String, val optimType: Goal, val rewardExpr: Expr<RatType>) : SMDPProperty(name) {
        override fun toString(): String {
            return "$name: S_$optimType($rewardExpr)=?"
        }
    }

    class PathQuantifierProperty(name: String, val type: SMDPPathFormula.Quantifier, val pathFormula: SMDPPathFormula) : SMDPProperty(name) {
        override fun toString(): String {
            return "$name: $type $pathFormula"
        }
    }

    enum class ComparisonOperator(val symbol: String) {
        GEQ(">="), LEQ("<="), LT("<"), GT(">")
    }
    class ProbabilityThresholdProperty(
        name: String, val optimType: Goal, val pathFormula: SMDPPathFormula, val threshold: Double, val comparison: ComparisonOperator
    ) : SMDPProperty(name) {
        override fun toString(): String {
            return "$name: P_$optimType($pathFormula) ${comparison.symbol} $threshold"
        }
    }

    class ExpectationThresholdProperty(
        name: String,
        val optimType: Goal, val rewardExpr: Expr<RatType>,
        val until: Expr<BoolType>,
        val accumulateRewardOnExit: Boolean, val accumulateRewardAfterStep: Boolean,
        val threshold: Double, val comparison: ComparisonOperator
    ) : SMDPProperty(name) {
        override fun toString(): String {
            val acc = arrayListOf<String>()
            if(accumulateRewardOnExit) acc.add("exit")
            if(accumulateRewardAfterStep) acc.add("step")
            val U =
                if (until == BoolExprs.True()) ""
                else " U $until"
            return "$name: E_$optimType($rewardExpr$U) ${comparison.symbol} $threshold $acc"
        }
    }
}

data class ThetaRewardBound(
    val rewardExpr: Expr<RatType>,
    val accumulateRewardOnExit: Boolean,
    val accumulateRewardAfterStep: Boolean,
    val lowerBound: Expr<RatType>?,
    val lowerExclusive: Boolean,
    val upperBound: Expr<RatType>?,
    val upperExclusive: Boolean
)

sealed class SMDPPathFormula() {
    enum class Quantifier() {
        EXISTS, FORALL
    }

    class Until(val left: SMDPPathFormula, val right: SMDPPathFormula, val rewardBounds: Collection<ThetaRewardBound>): SMDPPathFormula() {
        override fun toString(): String {
            return "($left) U ($right)"
        }
    }

    class WeakUntil(val left: SMDPPathFormula, val right: SMDPPathFormula, val rewardBounds: Collection<ThetaRewardBound>): SMDPPathFormula() {
        override fun toString(): String {
            return "($left) W ($right)"
        }
    }

    class Release(val left: SMDPPathFormula, val right: SMDPPathFormula, val rewardBounds: Collection<ThetaRewardBound>): SMDPPathFormula() {
        override fun toString(): String {
            return "($left) R ($right)"
        }
    }

    class Globally(val inner: SMDPPathFormula, val rewardBounds: Collection<ThetaRewardBound>): SMDPPathFormula() {
        override fun toString(): String {
            return if(rewardBounds.isEmpty()) "G($inner)" else "G^[$rewardBounds]($inner)"
        }
    }

    class Eventually(val inner: SMDPPathFormula, val rewardBounds: Collection<ThetaRewardBound>): SMDPPathFormula() {
        override fun toString(): String {
            return if(rewardBounds.isEmpty()) "F($inner)" else "F^[$rewardBounds]($inner)"
        }
    }

    class StateFormula(val expr: Expr<BoolType>): SMDPPathFormula() {
        override fun toString(): String {
            return "$expr"
        }
    }
}