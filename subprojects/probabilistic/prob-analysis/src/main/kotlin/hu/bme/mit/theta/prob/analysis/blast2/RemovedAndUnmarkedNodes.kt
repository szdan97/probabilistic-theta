package hu.bme.mit.theta.prob.analysis.blast2

data class RemovedAndUnmarkedNodes<U>(
    val removedNodes: Collection<U>,
    val unmarkedNodes: Collection<U>
)