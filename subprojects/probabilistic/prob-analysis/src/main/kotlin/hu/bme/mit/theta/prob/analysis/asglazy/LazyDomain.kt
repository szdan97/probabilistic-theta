package hu.bme.mit.theta.prob.analysis.asglazy

import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.prob.analysis.ProbabilisticCommand

interface LazyDomain<SC: ExprState, SA: ExprState, A: StmtAction> {
    fun checkContainment(state: SC, action: SA): Boolean
    fun isLeq(state1: SA, state2: SA): Boolean
    fun mayBeEnabled(state: SA, command: ProbabilisticCommand<A>): Boolean
    fun mustBeEnabled(state: SA, command: ProbabilisticCommand<A>): Boolean
    fun isEnabled(state: SC, command: ProbabilisticCommand<A>): Boolean
    fun concreteTransFunc(state: SC, action: A): SC
    fun block(abstrState: SA, expr: Expr<BoolType>, concrState: SC): SA

    fun blockSeq(
        nodes: List<ASGLazyChecker<SC, SA, A>.Node>,
        guards: List<Expr<BoolType>>,
        actions: List<A>,
        toBlockAtLast: Expr<BoolType>): List<SA>

    fun postImage(state: SA, action: A, guard: Expr<BoolType>): SA
    fun preImage(state: SA, action: A): Expr<BoolType>
    fun topAfter(state: SA, action: A): SA
}