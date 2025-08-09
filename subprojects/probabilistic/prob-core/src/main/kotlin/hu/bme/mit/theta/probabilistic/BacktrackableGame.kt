package hu.bme.mit.theta.probabilistic

interface BacktrackableGame<N> {
    fun getPreviousNodes(n: N): Collection<N>
}