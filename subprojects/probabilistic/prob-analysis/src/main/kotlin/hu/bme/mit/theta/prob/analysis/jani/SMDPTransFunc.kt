package hu.bme.mit.theta.prob.analysis.jani

import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.TransFunc
import hu.bme.mit.theta.analysis.expr.ExprState

class SMDPTransFunc<S: ExprState, P: Prec>(
    val domainTransFunc: TransFunc<S, in SMDPCommandAction, P>
): TransFunc<SMDPState<S>, SMDPCommandAction, P> {
    override fun getSuccStates(
        state: SMDPState<S>,
        action: SMDPCommandAction,
        prec: P
    ): Collection<SMDPState<S>> {
        val locs = nextLocs(state.locs, action.destination)
        val domainStates = domainTransFunc.getSuccStates(state.domainState, action, prec)

        return domainStates.map { SMDPState(it, locs) }
    }
}