package hu.bme.mit.theta.prob.analysis.blast2

data class RemovedAndUnlabeledNodes<U>(
    val removedNodes: Collection<U>,
    val unmarkedNodes: Collection<U>
)