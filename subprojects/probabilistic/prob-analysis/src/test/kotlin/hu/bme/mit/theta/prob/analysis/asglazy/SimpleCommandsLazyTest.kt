package hu.bme.mit.theta.prob.analysis.asglazy

import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.stmt.Stmts.Assign
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.inttype.IntExprs.*
import hu.bme.mit.theta.prob.analysis.ProbabilisticCommand
import hu.bme.mit.theta.prob.analysis.toAction
import hu.bme.mit.theta.probabilistic.FiniteDistribution
import hu.bme.mit.theta.probabilistic.FiniteDistribution.Companion.dirac
import hu.bme.mit.theta.probabilistic.Goal
import hu.bme.mit.theta.solver.z3.Z3SolverFactory
import org.junit.Test

class SimpleCommandsLazyTest {

    @Test
    fun checkExpl() {

        val A = Decls.Var("A", Int())
        val B = Decls.Var("B", Int())
        val C = Decls.Var("C", Int())
        val D = Decls.Var("D", Int())

        val commands = listOf(
            ProbabilisticCommand(
                Lt(A.ref, Int(6)),
                FiniteDistribution(
                    Assign(A, Add(A.ref, Int(1))).toAction() to 0.8,
                    Assign(A, Int(6)).toAction() to 0.2,
                )
            ),
            ProbabilisticCommand(
                True(),
                dirac(Assign(B, Add(B.ref, Int(1))).toAction())
            )
        )
        val invar = Neq(A.ref, Int(5))

        val init = ImmutableValuation.builder()
            .put(A, Int(0))
            .put(B, Int(0))
            .put(C, Int(0))
            .put(D, Int(0))
            .build()

        val solver = Z3SolverFactory.getInstance().createSolver()
        val itpSolver = Z3SolverFactory.getInstance().createItpSolver()
        val result = SimpleCommandsLazy(solver, itpSolver).checkExpl(
            commands, init, invar, Goal.MAX
        )
    }
}