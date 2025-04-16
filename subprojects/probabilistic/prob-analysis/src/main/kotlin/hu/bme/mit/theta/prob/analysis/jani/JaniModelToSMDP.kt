package hu.bme.mit.theta.prob.analysis.jani

import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.model.ImmutableValuation.empty
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.stmt.Stmts
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs
import hu.bme.mit.theta.core.type.abstracttype.EqExpr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs
import hu.bme.mit.theta.core.type.inttype.IntExprs
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.type.rattype.RatExprs
import hu.bme.mit.theta.core.type.rattype.RatExprs.Rat
import hu.bme.mit.theta.core.type.rattype.RatLitExpr
import hu.bme.mit.theta.core.type.rattype.RatType
import hu.bme.mit.theta.core.utils.ExprSimplifier
import hu.bme.mit.theta.prob.analysis.jani.SMDP.ActionLabel.StandardActionLabel
import hu.bme.mit.theta.prob.analysis.jani.SMDPPathFormula.Quantifier.EXISTS
import hu.bme.mit.theta.prob.analysis.jani.SMDPPathFormula.Quantifier.FORALL
import hu.bme.mit.theta.prob.analysis.jani.SMDPProperty.*
import hu.bme.mit.theta.prob.analysis.jani.model.*
import hu.bme.mit.theta.probabilistic.Goal
import hu.bme.mit.theta.prob.analysis.jani.model.BoolType as JaniBoolType
import hu.bme.mit.theta.prob.analysis.jani.model.IntType as JaniIntType
import hu.bme.mit.theta.prob.analysis.jani.model.RealType as JaniRealType

fun Model.toSMDP(modelParameterStrings: Map<String, String>): SMDP {
    require(this.type == ModelType.MDP || this.type == ModelType.DTMC) {
        "Only DTMC and MDP models are supported yet. "
    }

    val constantMap = this.constants.associate {
        it.name to it.toThetaVar()
    }
    val constantValueMap = this.constants.associate {
        val v = constantMap[it.name]!!
        v to if(it.value == null) {
            if(modelParameterStrings.containsKey(it.name)) {
                when(it.type) {
                    JaniIntType -> Int(modelParameterStrings[it.name]!!.toInt())
                    JaniBoolType -> BoolExprs.Bool(modelParameterStrings[it.name]!!.toBooleanStrict())
                    JaniRealType -> TODO()
                    else -> throw RuntimeException("Unsupported model parameter type for constant ${it.name}")
                }
            } else {
                throw RuntimeException("No value defined for constant ${it.name}")
            }
        } else it.value.toThetaExpr(constantMap, mapOf())
    }.toMutableMap()
    lateinit var constantsValuation: Valuation
    do {
        val B = ImmutableValuation.builder()
        val toReplace = arrayListOf<Pair<VarDecl<*>, Expr<*>>>()
        for ((k, v) in constantValueMap) {
            if(v is LitExpr<*>) {
                if(v.type == k.type)
                    B.put(k, v)
                else if(v.type == IntType.getInstance() && k.type == RatType.getInstance())
                    B.put(k, IntExprs.ToRat(v as Expr<IntType>).eval(empty()))
                else
                    throw RuntimeException("$v of type ${v.type} cannot be assigned to $k of type ${k.type}")
            }
            else
                toReplace.add(k to v)
        }
        constantsValuation = B.build()
        for ((k, v) in toReplace) {
            constantValueMap[k] = ExprSimplifier.simplify(v, constantsValuation)
        }
    } while (toReplace.isNotEmpty())


    // Translation of global model parts
    val globalVarMap = this.variables.associate {
        it.name to it.toThetaVar()
    } + constantMap
    val actionMap = this.actions.associate { it.name to it.toSMDPAction() }

    val functionMap = this.functions.map {
            val parameterMap = it.parameters.map {
                it.name to it.toThetaVar()
            }
            it.name to (parameterMap.map { it.second } to it.body.toThetaExpr(globalVarMap+parameterMap, mapOf()))
    }.toMap()

    // Translation of automaton instances
    val automatonMap = this.automata.associate { it.name to it.toSMDPAutomaton(
        actionMap, globalVarMap, functionMap
    ) }
    val instances = this.system.elements.map {
        SMDP.AutomatonInstance(automatonMap[it.automaton]!!)
    }

    // TODO: check how null actions in the sync vec work
    val syncVecs = this.system.syncs.map {
        it.synchronise.map {
            if(it == null) null
            else actionMap[it]!! as StandardActionLabel
        }
    }

    // TODO: add non-global vars
    val varMap = globalVarMap

    val props = this.properties.map { it.toSMDPProperty(varMap, functionMap, this.isInitDeterministic()) }

    val inits = (this.variables.mapNotNull {
        //TODO: make this work with multiple possible init locs
        require(instances.all { it.initLocs.size == 1 })
        it.getThetaInitExpr(globalVarMap, instances.flatMap { it.initLocs }, functionMap)
    } + this.constants.mapNotNull {
        it.getThetaInitExpr(varMap, modelParameterStrings, functionMap)
    }).toMutableList()
    inits.addAll(instances.flatMap(SMDP.AutomatonInstance::initExprs))

    return SMDP(
        globalVarMap.values,
        instances,
        syncVecs,
        inits,
        props,
        variables.mapNotNull { v ->
            if(v.transient) v.initialValue?.let {
                val ref = varMap[v.name]!!
                val expr = it.toThetaExpr(varMap, functionMap)
                if(expr.type == ref.type)
                    ref to expr
                else if(expr.type == IntType.getInstance() && ref.type == RatType.getInstance())
                    ref to IntExprs.ToRat(expr as Expr<IntType>)
                else
                    throw RuntimeException("$expr of type ${expr.type} cannot be assigned to $ref of type ${ref.type}")
            } else null
        }.toMap(),
        constantsValuation
    )
}

fun Model.isInitDeterministic(): Boolean {
    val singleInitLocs = this.automata.all { it.initialLocations.size == 1 }
    val initValuesDefined =
        this.variables.all { it.initialValue != null } &&
                this.automata.all { it.variables.all { it.initialValue != null } }
    return singleInitLocs && initValuesDefined
}

fun Property.toSMDPProperty(
    varMap: Map<String, VarDecl<*>>,
    functionMap: Map<String, Pair<List<VarDecl<*>>, Expr<*>>>,
    isInitDeterministic: Boolean
): SMDPProperty {
    require(this.expression is FilterExpression) {"Properties must be defined using an outer filter expression"}

    fun processExpression(propExpr: PropertyExpression): SMDPProperty =
        if(propExpr is UnaryPropertyExpression)
            when(propExpr.op) {
                ProbabilityOp.MIN ->
                    ProbabilityProperty(this.name, Goal.MIN, propExpr.exp.toThetaPathExpression(varMap, functionMap))
                ProbabilityOp.MAX ->
                    ProbabilityProperty(this.name, Goal.MAX, propExpr.exp.toThetaPathExpression(varMap, functionMap))
                SteadyStateOp.MIN ->
                    SteadyStateProperty(
                        this.name, Goal.MIN, propExpr.exp.toThetaExpr(varMap, functionMap) as Expr<RatType>)
                SteadyStateOp.MAX ->
                    SteadyStateProperty(this.name, Goal.MAX, propExpr.exp.toThetaExpr(varMap, functionMap) as Expr<RatType>)
                PathQuantifier.EXISTS ->
                    PathQuantifierProperty(this.name, EXISTS, propExpr.exp.toThetaPathExpression(varMap, functionMap))
                PathQuantifier.FORALL ->
                    PathQuantifierProperty(this.name, FORALL, propExpr.exp.toThetaPathExpression(varMap, functionMap))
                else -> throw IllegalArgumentException("Property expression with operator ${propExpr.op} unsupported")
            }
        else if(propExpr is Expectation) {
            val optimType = when(propExpr.op) {
                ExpectationOp.MIN -> Goal.MIN
                ExpectationOp.MAX -> Goal.MAX
            }
            ExpectationProperty(
                this.name,
                optimType,
                propExpr.exp.toThetaExpr(varMap, functionMap) as Expr<RatType>,
                propExpr.reach?.let {it.toThetaExpr(varMap, functionMap) as Expr<BoolType>} ?: BoolExprs.False(),
                RewardAccumulation.EXIT in propExpr.accumulate,
                RewardAccumulation.STEPS in propExpr.accumulate
            )
        } else if(propExpr is BinaryExpression) {
            when(propExpr.op) {
                BinaryOp.LEQ, DerivedBinaryOp.GEQ -> {
                    val inner = processExpression(propExpr.left)
                    val comparison =
                        if(propExpr.op == BinaryOp.LEQ) ComparisonOperator.LEQ
                        else ComparisonOperator.GEQ
                    val thresholdExpr =
                        propExpr.right.toThetaExpr(varMap, functionMap).eval(empty())
                    val threshold = when(thresholdExpr) {
                        is IntLitExpr -> thresholdExpr.value.toDouble()
                        is RatLitExpr -> thresholdExpr.num.toDouble() / thresholdExpr.denom.toDouble()
                        else -> throw RuntimeException("Unable to evaluate threshold $thresholdExpr in property $name")
                    }
                    when(inner) {
                        is ProbabilityProperty -> ProbabilityThresholdProperty(
                            this.name, inner.optimType, inner.pathFormula, threshold, comparison
                        )
                        is ExpectationProperty ->  ExpectationThresholdProperty(
                            this.name, inner.optimType, inner.rewardExpr, inner.until,
                            inner.accumulateRewardOnExit, inner.accumulateRewardAfterStep,
                            threshold, comparison,
                        )
                        else -> throw IllegalArgumentException()
                    }
                }
                else -> throw IllegalArgumentException("Property expression $propExpr unsupported")
            }
        } else throw IllegalArgumentException("Property expression $propExpr unsupported")


    val function = this.expression.function
    return if(function == Filter.VALUES) {
        require(isInitDeterministic) { "\"values\"-type properties are only supported for deterministic initial state" }
        val propExpr = this.expression.values
        processExpression(propExpr)
    } else if(function == Filter.MAX) {
        val propExpr = this.expression.values
        require(propExpr is UnaryPropertyExpression || propExpr is Expectation) {
            "Inner property expression $propExpr in property $name is no supported yet"
        }
        val processed = processExpression(propExpr)
        require(isInitDeterministic
                || (processed is ProbabilityProperty && processed.optimType == Goal.MAX )
                || (processed is ExpectationProperty && processed.optimType == Goal.MAX )
                || (processed is SteadyStateProperty && processed.optimType == Goal.MAX )) {
            "Inner and outer optimization goals of a property must be the same for non-deterministic initial state"
        }
        processed
    } else if(function == Filter.MIN) {
        val propExpr = this.expression.values
        require(propExpr is UnaryPropertyExpression || propExpr is Expectation) {
            "Inner property expression $propExpr in property $name is no supported yet"
        }
        val processed = processExpression(propExpr)
        require(isInitDeterministic
                || (processed is ProbabilityProperty && processed.optimType == Goal.MIN )
                || (processed is ExpectationProperty && processed.optimType == Goal.MIN )
                || (processed is SteadyStateProperty && processed.optimType == Goal.MIN )) {
            "Inner and outer optimization goals of a property must be the same for non-deterministic initial state"
        }
        processed
    } else {
        throw IllegalArgumentException("Property exceptions with root $function are not supported yet")
    }
}

fun Expression.toThetaPathExpression(varMap: Map<String, VarDecl<*>>, functionMap: Map<String, Pair<List<VarDecl<*>>, Expr<*>>>): SMDPPathFormula = when(this) {
    is BinaryPathExpression -> {
        val left = this.left.toThetaPathExpression(varMap, functionMap)
        val right = this.right.toThetaPathExpression(varMap, functionMap)
        val rewardBounds = this.rewardBounds.map {
            ThetaRewardBound(
                it.exp.toThetaExpr(varMap, functionMap) as Expr<RatType>,
                RewardAccumulation.EXIT in it.accumulate,
                RewardAccumulation.STEPS in it.accumulate,
                it.bounds.lower?.toThetaExpr(varMap, functionMap) as Expr<RatType>?,
                it.bounds.lowerExclusive,
                it.bounds.upper?.toThetaExpr(varMap, functionMap) as Expr<RatType>?,
                it.bounds.upperExclusive,
            )
        }
        when(this.op) {
            BinaryPathOp.U -> SMDPPathFormula.Until(left, right, rewardBounds)
            BinaryPathOp.W -> SMDPPathFormula.WeakUntil(left, right, rewardBounds)
            DerivedBinaryPathOp.R -> SMDPPathFormula.Release(left, right, rewardBounds)
            else -> throw UnsupportedOperationException("Unsupported path operator in $this")
        }
    }
    is UnaryPathExpression -> {
        val inner = this.exp.toThetaPathExpression(varMap, functionMap)
        val rewardBounds = this.rewardBounds.map {
            ThetaRewardBound(
                it.exp.toThetaExpr(varMap, functionMap) as Expr<RatType>,
                RewardAccumulation.EXIT in it.accumulate,
                RewardAccumulation.STEPS in it.accumulate,
                it.bounds.lower?.toThetaExpr(varMap, functionMap) as Expr<RatType>?,
                it.bounds.lowerExclusive,
                it.bounds.upper?.toThetaExpr(varMap, functionMap) as Expr<RatType>?,
                it.bounds.upperExclusive,
            )
        }
        when(this.op) {
            UnaryPathOp.F -> SMDPPathFormula.Eventually(inner, rewardBounds)
            UnaryPathOp.G -> SMDPPathFormula.Globally(inner, rewardBounds)
        }
    }
    is Call -> {
        throw UnsupportedOperationException("Function calls are not supported yet")
    }
    else -> {
        val expr = this.toThetaExpr(varMap, functionMap)
        require(expr.type is BoolType) {"Path expression must be boolean"}
        SMDPPathFormula.StateFormula(expr as Expr<BoolType>)
    }
}

fun ConstantDeclaration.getThetaInitExpr(
    varMap: Map<String, VarDecl<*>>,
    modelParameterStrings: Map<String, String>,
    functionMap: Map<String, Pair<List<VarDecl<*>>, Expr<*>>>
): EqExpr<*>? {
    val ref = varMap[name]!!.ref
    return if(value == null) {
        if(modelParameterStrings.containsKey(name)) {
            when(this.type) {
                JaniIntType -> IntExprs.Eq(ref as Expr<IntType>, Int(modelParameterStrings[name]!!.toInt()))
                JaniBoolType -> BoolExprs.Iff(ref as Expr<BoolType>, BoolExprs.Bool(modelParameterStrings[name]!!.toBooleanStrict()))
                JaniRealType -> TODO()
                else -> throw RuntimeException("Unsupported model parameter type for constant $name")
            }
        } else {
            throw RuntimeException("No value defined for constant $name")
        }
    } else AbstractExprs.Eq(ref, value.toThetaExpr(varMap, functionMap))
}

fun VariableDeclaration.getThetaInitExpr(
    varMap: Map<String, VarDecl<*>>,
    initialLocations: List<SMDP.Location>,
    functionMap: Map<String, Pair<List<VarDecl<*>>, Expr<*>>>
): Expr<BoolType>? {
    val ref = varMap[this.name]!!.ref
    return if (this.transient) {
        val l = initialLocations.find { it.transientMap.containsKey(varMap[this.name]) }
        if(l == null) {
            if(this.initialValue != null)
                AbstractExprs.Eq(ref, this.initialValue.toThetaExpr(varMap, functionMap))
            else
                throw IllegalArgumentException("Transient variables must have an initial value")
        } else {
            AbstractExprs.Eq(ref, l.transientMap[varMap[this.name]])
        }
    } else if (this.initialValue == null) {
        // The initial value of a bounded variable must be forced into its bounds if unspecified
        if (this.type is BoundedType) {
            val upperConstraint =
                if (this.type.upperBound == null) True()
                else AbstractExprs.Leq(ref, this.type.upperBound.toThetaExpr(varMap, functionMap))
            val lowerConstraint =
                if (this.type.lowerBound == null) True()
                else AbstractExprs.Leq(ref, this.type.lowerBound.toThetaExpr(varMap, functionMap))
            SmartBoolExprs.And(listOf(lowerConstraint, upperConstraint))
        } else null
    } else {
        AbstractExprs.Eq(ref, this.initialValue.toThetaExpr(varMap, functionMap))
    }
}

fun Automaton.toSMDPAutomaton(
    actionMap: Map<String, SMDP.ActionLabel>,
    globalVarMap: Map<String, VarDecl<*>>,
    functionMap: Map<String, Pair<List<VarDecl<*>>, Expr<*>>>
): SMDP.Automaton {
    val localVarMap = this.variables.associate { it.name to it.toThetaVar() }
    val fullVarMap = globalVarMap + localVarMap
    val locationMap = this.locations.associate { it.name to it.toSMDPLocation(fullVarMap, functionMap) }
    val edges = this.edges.map { it.toSMDPEdge(locationMap, actionMap, fullVarMap, functionMap) }

    val initLocs = this.initialLocations.map { locationMap[it]!! }
    require(initLocs.size == 1) {"Only deterministic initial locations are supported yet."}
    val inits = this.variables.mapNotNull {
        it.getThetaInitExpr(fullVarMap, initLocs, functionMap)
    }

    return SMDP.Automaton(
        this.name,
        locationMap.values,
        initLocs,
        actionMap.values,
        localVarMap.values,
        edges,
        inits,
        this.variables.mapNotNull { v ->
            if(v.transient) v.initialValue?.let { fullVarMap[v.name]!! to it.toThetaExpr(fullVarMap, functionMap) } else null
        }.toMap()
    )
}

fun Location.toSMDPLocation(varMap: Map<String, VarDecl<*>>, functionMap: Map<String, Pair<List<VarDecl<*>>, Expr<*>>>): SMDP.Location {
    val transientMap = this.transientValues.associate {
        require(it.reference is Identifier)
        val ref = varMap[it.reference.name]!!
        val expr = it.value.toThetaExpr(varMap, functionMap)
        if(ref.type == expr.type)
            ref to expr
        else if(ref.type == RatType.getInstance() && expr.type == IntType.getInstance())
            ref to IntExprs.ToRat(expr as Expr<IntType>)
        else
            throw RuntimeException("$expr of type ${expr.type} cannot be assigned to $ref of type ${ref.type}")
    }
    return SMDP.Location(name, arrayListOf(), null, transientMap)
}

fun Edge.toSMDPEdge(
    locationMap: Map<String, SMDP.Location>,
    actionMap: Map<String, SMDP.ActionLabel>,
    varMap: Map<String, VarDecl<*>>,
    functionMap: Map<String, Pair<List<VarDecl<*>>, Expr<*>>>
): SMDP.Edge {
    val sourceLoc = locationMap[this.location]!!
    val action = this.action?.let(actionMap::get) ?: SMDP.ActionLabel.InnerActionLabel
    val edge = SMDP.Edge(
        sourceLoc,
        this.guard?.exp?.toThetaExpr(varMap, functionMap) as? Expr<BoolType> ?: True(),
        action, this.destinations.map {
            it.toSMDPDestination(
                locationMap, varMap, functionMap
            )
        }
    )
    return edge
}

fun Expression.toThetaExpr(varMap: Map<String, VarDecl<*>>, functionMap: Map<String, Pair<List<VarDecl<*>>, Expr<*>>>): Expr<*> = when(this) {
    is BoolConstant -> BoolExprs.Bool(this.value)
    is IntConstant -> Int(this.value)
    is RealConstant -> { // TODO: real real type
        val d = this.value
        val pow = d.toString().indexOf('.')
        val denom = if(pow == -1) 1.0 else Math.pow(10.0, d.toString().length-pow.toDouble()-1)
        val num = d.toString().filterNot('.'::equals).removePrefix("0").ifEmpty { "0" }
        Rat(num, denom.toLong().toString())
    }
    is UnaryExpression -> this.toThetaExpr(varMap, functionMap)
    is BinaryExpression -> this.toThetaExpr(varMap, functionMap)
    is LValue -> this.toThetaExpr(varMap)
    is DistributionSampling -> throw RuntimeException("Distribution sampling not supported yet")
    is Ite -> AbstractExprs.Ite<Type>(
        this.condition.toThetaExpr(varMap, functionMap) as Expr<BoolType>,
        this.thenExp.toThetaExpr(varMap, functionMap),
        this.elseExp.toThetaExpr(varMap, functionMap)
    )
    is Call -> {
        if (functionMap.containsKey(this.function)) {
            val parameterMap: Map<Decl<*>, Expr<*>> = functionMap[this.function]!!.first.mapIndexed { index, varDecl ->
                varDecl to this.args[index].toThetaExpr(varMap, functionMap)
            }.toMap()
            val base = functionMap[this.function]!!.second

            fun inlineParams(expr: Expr<*>): Expr<*> {
                return if(expr is RefExpr<*>) {
                    parameterMap.getOrElse(expr.decl) {expr}
                } else {
                    expr.withOps(expr.ops.map { inlineParams(it) })
                }
            }

            val inlined = inlineParams(base)
            inlined
        }
        else throw RuntimeException("Function ${this.function} not found - if it has been declared, it might have unsupported features (see warnings)")
    }
    is Nondet -> throw RuntimeException("Nondet expressions not supported yet")
    else -> throw RuntimeException("The expression $this is not supported yet.")
}

fun Expr<*>.replaceRefs(replaceWith: Map<VarDecl<*>, Expr<*>>) {
}

fun LValue.toThetaExpr(varMap: Map<String, VarDecl<*>>): Expr<*> = when(this) {
    is Identifier -> varMap[this.name]!!.ref
    else -> throw RuntimeException("The expression $this is not supported yet.")
}

fun UnaryExpression.toThetaExpr(varMap: Map<String, VarDecl<*>>, functionMap: Map<String, Pair<List<VarDecl<*>>, Expr<*>>>): Expr<*> {
    val arg = this.exp.toThetaExpr(varMap, functionMap)
    return when(this.op) {
        is UnaryOp ->
            when(this.op) {
                UnaryOp.NOT ->
                    if(arg.type is BoolType) Not(arg as Expr<BoolType>)
                    else throw RuntimeException("Argument of NOT must be boolean")
                UnaryOp.FLOOR ->
                    when (arg.type) {
//                        is RatType -> RatFloorExpr(op as Expr<RatType>)
//                        is IntType -> IntFloorExpr(op as Expr<IntType>)
                        else -> throw RuntimeException("Floor not supported yet")
                    }
                UnaryOp.CEIL ->
                    when (arg.type) {
//                        is RatType -> RatCeilExpr(op as Expr<RatType>)
//                        is IntType -> IntCeilExpr(op as Expr<IntType>)
                        else -> throw RuntimeException("Ceil not supported yet")
                    }
                UnaryOp.DER -> throw UnsupportedOperationException("Derivation functions not supported yet")
            }
        is DerivedUnaryOp ->
            when(this.op) {
                DerivedUnaryOp.ABS -> AbstractExprs.Ite<IntType>(
                    IntExprs.Lt(arg as Expr<IntType>, Int(0)),
                    IntExprs.Neg(arg), arg
                )
                DerivedUnaryOp.SGN -> AbstractExprs.Ite<IntType>(
                    IntExprs.Lt(arg as Expr<IntType>, Int(0)),
                    IntExprs.Neg(arg), arg
                )
                // I don't even know what TRC stands for
                DerivedUnaryOp.TRC -> throw UnsupportedOperationException("TRC not supported yet")
            }
        is HyperbolicOp -> throw UnsupportedOperationException("Hyperbolic functions not supported yet")
        is TrigonometricOp -> throw UnsupportedOperationException("Trigonometric functions not supported yet")
        else -> throw UnsupportedOperationException("The unary operation $op is not supported yet")
    }
}

fun BinaryExpression.toThetaExpr(varMap: Map<String, VarDecl<*>>, functionMap: Map<String, Pair<List<VarDecl<*>>, Expr<*>>>): Expr<*> {
    val l = left.toThetaExpr(varMap, functionMap)
    val r = right.toThetaExpr(varMap, functionMap)

    @Suppress("UNCHECKED_CAST") //Checked through expr.type
    fun withBool(f: (l: Expr<BoolType>, r: Expr<BoolType>) -> Expr<BoolType>) =
        if(l.type is BoolType && r.type is BoolType)
            f(l as Expr<BoolType>, r as Expr<BoolType>)
        else throw RuntimeException("Operands of ${this.op} must be boolean")

    return when (this.op) {
        is BinaryOp -> when(this.op) {
            BinaryOp.AND -> withBool(BoolExprs::And)
            BinaryOp.OR -> withBool(BoolExprs::Or)
            BinaryOp.EQ -> AbstractExprs.Eq(l, r)
            BinaryOp.NEQ -> AbstractExprs.Neq(l, r)
            BinaryOp.ADD -> AbstractExprs.Add(l, r)
            BinaryOp.SUB -> AbstractExprs.Sub(l, r)
            BinaryOp.MUL -> AbstractExprs.Mul(l, r)
            BinaryOp.MOD -> AbstractExprs.Mod(l, r)
            BinaryOp.DIV -> {
                val l = if(l.type == Int()) IntExprs.ToRat(l as Expr<IntType>) else l
                val r = if(r.type == Int()) IntExprs.ToRat(r as Expr<IntType>) else r
                RatExprs.Div(l as Expr<RatType>, r as Expr<RatType>)
            }
            BinaryOp.POW -> throw UnsupportedOperationException("POW not implemented yet")
            BinaryOp.LOG -> throw UnsupportedOperationException("LOG not implemented yet")
            BinaryOp.LT -> AbstractExprs.Lt(l, r)
            BinaryOp.LEQ -> AbstractExprs.Leq(l, r)
        }
        is DerivedBinaryOp -> when(this.op) {
            DerivedBinaryOp.IMPLIES -> withBool(BoolExprs::Imply)
            DerivedBinaryOp.GT -> AbstractExprs.Gt(l, r)
            DerivedBinaryOp.GEQ -> AbstractExprs.Geq(l, r)
            //TODO: make these work with rats/reals
            DerivedBinaryOp.MIN -> AbstractExprs.Ite<IntType>(AbstractExprs.Lt(l, r), l, r)
            DerivedBinaryOp.MAX -> AbstractExprs.Ite<IntType>(AbstractExprs.Gt(l, r), l, r)
        }
        else -> throw UnsupportedOperationException("${this.op} not supported")
    }

}

fun Assignment.toSMDPAssignment(
    varMap: Map<String, VarDecl<*>>,
    functionMap: Map<String, Pair<List<VarDecl<*>>, Expr<*>>>
): SMDP.Assignment {
    val identifier = this.reference as? Identifier ?:
                    throw RuntimeException("Left-hand side of an assignment must be a reference.")
    val ref = varMap[identifier.name] ?:
        throw RuntimeException(
            "Variable declaration not found for identifier '$identifier' used in an assignment"
        )

    val expr = this.value.toThetaExpr(varMap, functionMap)

    return if(expr.type == ref.type) SMDP.Assignment(ref, expr, this.index)
    else if(expr.type == IntType.getInstance() && ref.type == RatType.getInstance())
        SMDP.Assignment(ref, IntExprs.ToRat(expr as Expr<IntType>), this.index)
    else
        throw RuntimeException("$expr of type ${expr.type} cannot be assigned to $ref of type ${ref.type}")
}

fun Destination.toSMDPDestination(
    locationMap: Map<String, SMDP.Location>,
    varMap: Map<String, VarDecl<*>>,
    functionMap: Map<String, Pair<List<VarDecl<*>>, Expr<*>>>
): SMDP.Destination {
    val expr = this.probability?.exp?.toThetaExpr(varMap, functionMap) ?: Rat(1, 1)
    require(expr.type == Int() || expr.type == Rat())
    return SMDP.Destination(
        (if (expr.type == Int()) IntExprs.ToRat(expr as Expr<IntType>) else expr) as Expr<RatType>,
        this.assignments.map { it.toSMDPAssignment(varMap, functionMap) },
        locationMap[this.location]!!
    )
}

fun ConstantDeclaration.toThetaVar(): VarDecl<*> = when (this.type) {
    is JaniBoolType -> Var(name, BoolType.getInstance())
    is JaniIntType -> Var(name, IntType.getInstance())
    is JaniRealType -> Var(name, RatType.getInstance())
    is BoundedType -> Var(name, IntType.getInstance()) //TODO: create a real bounded int type
    else -> throw UnsupportedOperationException("Unknown type $type for constant $name")
}

fun VariableDeclaration.toThetaVar(): VarDecl<*> = when (this.type) {
    is JaniBoolType -> Var(name, BoolType.getInstance())
    is JaniIntType -> Var(name, IntType.getInstance())
    is JaniRealType -> Var(name, RatType.getInstance())
    is BoundedType -> Var(name, IntType.getInstance()) //TODO: create a real bounded int type
    is ClockType -> throw UnsupportedOperationException("Timed automata are not supported yet")
    is ContinuousType -> throw UnsupportedOperationException("Hybrid automata (continuous variables) are not supported yet")
    else -> throw UnsupportedOperationException("Unknown variable type $type for variable $name")
}
fun FunctionParameter.toThetaVar(): VarDecl<*> = when (this.type) {
    is JaniBoolType -> Var(name, BoolType.getInstance())
    is JaniIntType -> Var(name, IntType.getInstance())
    is JaniRealType -> Var(name, RatType.getInstance())
    is BoundedType -> Var(name, IntType.getInstance()) //TODO: create a real bounded int type
    is ClockType -> throw UnsupportedOperationException("Timed automata are not supported yet")
    is ContinuousType -> throw UnsupportedOperationException("Hybrid automata (continuous variables) are not supported yet")
    else -> throw UnsupportedOperationException("Unknown variable type $type for variable $name")
}

fun extractSMDPExpectedRewardTask(prop: SMDPProperty): SMDPExpectedRewardTask {
    require(prop is ExpectationProperty || prop is ExpectationThresholdProperty)
    val optimType =
        when (prop) {
            is ExpectationProperty -> prop.optimType
            is ExpectationThresholdProperty -> prop.optimType
            else -> throw RuntimeException("Now this is unexpected")
        }
    val rewardExpr =
        when (prop) {
            is ExpectationProperty -> prop.rewardExpr
            is ExpectationThresholdProperty -> prop.rewardExpr
            else -> throw RuntimeException("Now this is unexpected")
        }
    val until =
        when (prop) {
            is ExpectationProperty -> prop.until
            is ExpectationThresholdProperty -> prop.until
            else -> throw RuntimeException("Now this is unexpected")
        }
    val accumulateRewardOnExit =
        when (prop) {
            is ExpectationProperty -> prop.accumulateRewardOnExit
            is ExpectationThresholdProperty -> prop.accumulateRewardOnExit
            else -> throw RuntimeException("Now this is unexpected")
        }
    val accumulateRewardAfterStep =
        when (prop) {
            is ExpectationProperty -> prop.accumulateRewardAfterStep
            is ExpectationThresholdProperty -> prop.accumulateRewardAfterStep
            else -> throw RuntimeException("Now this is unexpected")
        }

    return SMDPExpectedRewardTask(
        rewardExpr,
        optimType,
        false,
        Not(until),
        accumulateRewardOnExit,
        accumulateRewardAfterStep
    )
}

fun extractSMDPReachabilityTask(
    prop: SMDPProperty,
    smdp: SMDP? = null
): Pair<SMDPReachabilityTask, SMDP?> {
    require(prop is ProbabilityProperty || prop is ProbabilityThresholdProperty) {
        "Only probability properties (Pmax and Pmin) are supported yet"
    }

    val errorString = """
            Only reachability properties are supported yet, which must be in one of the following forms:
            F p, G p, q U p, p W ff
        """.trimIndent()
    val pathFormula =
        when (prop) {
            is ProbabilityProperty -> prop.pathFormula
            is ProbabilityThresholdProperty -> prop.pathFormula
            else -> throw RuntimeException("Now this is unexpected")
        }
    val optimType =
        when (prop) {
            is ProbabilityProperty -> prop.optimType
            is ProbabilityThresholdProperty -> prop.optimType
            else -> throw RuntimeException("Now this is unexpected")
        }

    data class RewardBoundAdditions(
        val upperBoundExprs: List<Expr<BoolType>>,
        val lowerBoundExprs: List<Expr<BoolType>>,
        val preStepAdditions: List<Stmt>,
        val postStepAdditions: List<Stmt>,
        val additionalVars: List<VarDecl<*>>,
        val additionalInitExprs: List<Expr<BoolType>>
    )
    fun processRewardBounds(rewardBounds: Collection<ThetaRewardBound>): RewardBoundAdditions {
        val upperBoundExprs = arrayListOf<Expr<BoolType>>()
        val lowerBoundExprs = arrayListOf<Expr<BoolType>>()
        val preStepAdditions = arrayListOf<Stmt>()
        val postStepAdditions = arrayListOf<Stmt>()
        val additionalVars = arrayListOf<VarDecl<*>>()
        val additionalInitExprs = arrayListOf<Expr<BoolType>>()
        var i = 0
        for (rewardBound in rewardBounds) {
            val decl = Var("__rewardbound_${i++}", Rat())
            additionalVars.add(decl)
            additionalInitExprs.add(RatExprs.Eq(decl.ref, Rat(0, 1)))
            val lower = if(rewardBound.lowerBound != null) {
                if(rewardBound.lowerExclusive) AbstractExprs.Lt(rewardBound.lowerBound, decl.ref)
                else AbstractExprs.Leq(rewardBound.lowerBound, decl.ref)
            } else True()
            lowerBoundExprs.add(lower)
            val upper = if(rewardBound.upperBound != null) {
                if(rewardBound.upperExclusive) AbstractExprs.Gt(rewardBound.upperBound, decl.ref)
                else AbstractExprs.Geq(rewardBound.upperBound, decl.ref)
            } else True()
            upperBoundExprs.add(upper)
            val accumulation = Stmts.Assign(decl, RatExprs.Add(decl.ref, rewardBound.rewardExpr))
            if(rewardBound.accumulateRewardOnExit)
                preStepAdditions.add(accumulation)
            if(rewardBound.accumulateRewardAfterStep)
                postStepAdditions.add(accumulation)
        }
        return RewardBoundAdditions(
            upperBoundExprs, lowerBoundExprs,
            preStepAdditions, postStepAdditions,
            additionalVars, additionalInitExprs,
        )
    }

    when (pathFormula) {
        is SMDPPathFormula.Until -> {
            val left = pathFormula.left
            val right = pathFormula.right

            require(pathFormula.rewardBounds.isEmpty() || smdp != null)
            val rba = processRewardBounds(pathFormula.rewardBounds)

            if (left is SMDPPathFormula.StateFormula && right is SMDPPathFormula.StateFormula) {
                return SMDPReachabilityTask(
                    SmartBoolExprs.And(rba.lowerBoundExprs + rba.upperBoundExprs + right.expr),
                    optimType, false,
                    SmartBoolExprs.And(rba.upperBoundExprs + left.expr),
                    rba.preStepAdditions, rba.postStepAdditions
                ) to smdp?.let {
                    SMDP(
                        it.globalVars + rba.additionalVars,
                        it.automata, it.syncVecs,
                        it.initExprs + rba.additionalInitExprs,
                        listOf(prop),
                        it.transientInitialValueMap, it.constantsValuation
                    )
                }
            } else {
                throw IllegalArgumentException(errorString)
            }
        }

        is SMDPPathFormula.WeakUntil -> {
            val left = pathFormula.left
            val right = pathFormula.right

            require(pathFormula.rewardBounds.isEmpty()) {"Semantics of a reward-bounded weak until are not clear yet"}
            //require(pathFormula.rewardBounds.isEmpty() || smdp != null)
            //val rba = processRewardBounds(pathFormula.rewardBounds)

            if (left is SMDPPathFormula.StateFormula && right is SMDPPathFormula.StateFormula) {
                // not(p W q) = not(q) U not(p)
                // TODO: reward bounds
                return SMDPReachabilityTask(Not(left.expr), optimType.opposite(), true, Not(right.expr),
                    listOf(), listOf()
                ) to null
            } else {
                throw IllegalArgumentException(errorString)
            }
        }

        is SMDPPathFormula.Eventually -> {
            val inner = pathFormula.inner
            if (inner !is SMDPPathFormula.StateFormula) throw IllegalArgumentException(errorString)
            // TODO: reward bounds?
            return SMDPReachabilityTask(inner.expr, optimType, false, True(), listOf(), listOf()
            ) to null
        }

        is SMDPPathFormula.Globally -> {
            require(pathFormula.rewardBounds.isEmpty()) {"Semantics of a reward-bounded globally are not clear yet"}
            //require(pathFormula.rewardBounds.isEmpty() || smdp != null)
            //val rba = processRewardBounds(pathFormula.rewardBounds)

            val inner = pathFormula.inner
            if (inner !is SMDPPathFormula.StateFormula) throw IllegalArgumentException(errorString)
            return SMDPReachabilityTask(Not(inner.expr), optimType.opposite(), true, True(), listOf(), listOf()
            ) to null
        }

        else -> throw IllegalArgumentException(errorString)
    }
}

fun ActionDefinition.toSMDPAction(): SMDP.ActionLabel = StandardActionLabel(name)