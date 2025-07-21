package hu.bme.mit.theta.prob.analysis

import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs
import hu.bme.mit.theta.probabilistic.FiniteDistribution

data class ProbabilisticCommand<A: Action>(
    val guard: Expr<BoolType>,
    val result: FiniteDistribution<A>
) {
    fun withPrecondition(condition: Expr<BoolType>) = ProbabilisticCommand(
        SmartBoolExprs.And(condition, this.guard),
        result
    )

    override fun toString(): String {
        return "guard: ${this.guard}\nresult: ${this.result.pmf.entries.joinToString(separator = "\n") { "${it.value}: ${it.key}" }}"
    }
}