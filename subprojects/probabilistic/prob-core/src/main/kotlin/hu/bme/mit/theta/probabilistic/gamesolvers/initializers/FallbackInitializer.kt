package hu.bme.mit.theta.probabilistic.gamesolvers.initializers

import hu.bme.mit.theta.probabilistic.gamesolvers.SGSolutionInitializer

class FallbackInitializer<N, A>(
    val lowerBound: Map<N, Double>,
    val upperBound: Map<N, Double>,
    val fallback: SGSolutionInitializer<N,A>,
    val convergenceThreshold: Double,
    val strategy: Map<N, A>
): SGSolutionInitializer<N, A> {
    override fun initialLowerBound(n: N): Double {
        if(fallback.isKnown(n)) return fallback.initialLowerBound(n)
        return lowerBound[n] ?: fallback.initialLowerBound(n)
    }

    override fun initialUpperBound(n: N): Double {
        if(fallback.isKnown(n)) return fallback.initialUpperBound(n)
        return upperBound[n] ?: fallback.initialUpperBound(n)
    }

    override fun isKnown(n: N): Boolean {
        return fallback.isKnown(n) || initialUpperBound(n) - initialLowerBound(n) < convergenceThreshold
    }

    override fun initialStrategy(): Map<N, A> {
        val combinedStrategy = fallback.initialStrategy().toMutableMap()
        combinedStrategy.putAll(strategy)
        return combinedStrategy
    }
}