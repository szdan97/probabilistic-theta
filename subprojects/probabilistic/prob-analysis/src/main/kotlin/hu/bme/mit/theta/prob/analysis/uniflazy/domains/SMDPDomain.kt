package hu.bme.mit.theta.prob.analysis.uniflazy.domains

import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.prob.analysis.besttransformer.smdpGetGuardSatisfactionConfigs
import hu.bme.mit.theta.prob.analysis.jani.*
import hu.bme.mit.theta.prob.analysis.linkedtransfuncs.SMDPLinkedTransFunc
import hu.bme.mit.theta.prob.analysis.uniflazy.Domain

class SMDPDomain<S : ExprState, P : Prec, R>(
    val innerDomain: Domain<S, SMDPCommandAction, P, R, Unit>
) : Domain<SMDPState<S>, SMDPCommandAction, P, R, List<SMDP.Location>>(
    stateOrd = SmdpOrd(innerDomain.stateOrd),
    extendPrec = innerDomain.extendPrec,
    refineState = { s, r -> SMDPState(innerDomain.refineState(s.domainState, r), s.locs) },
    abstractFromValuation = { v, l, p -> SMDPState(innerDomain.abstractFromValuation(v, Unit, p), l) },
    abstractFromExpr = { e, l, p -> SMDPState(innerDomain.abstractFromExpr(e, Unit, p), l) },
    extractStructure = SMDPState<S>::locs,
    transFunc = SMDPTransFunc(innerDomain.transFunc),
    linkedTransFunc = SMDPLinkedTransFunc(innerDomain.linkedTransFunc),
    maySats = { s, e -> innerDomain.maySats(s.domainState, e) },
    mustSats = { s, e -> innerDomain.mustSats(s.domainState, e) },
    getGuardSatisfactionConfigs = smdpGetGuardSatisfactionConfigs(
        innerDomain.getGuardSatisfactionConfigs
    )
) {

}