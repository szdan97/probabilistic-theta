package hu.bme.mit.theta.probabilistic

import kotlin.random.Random

class FiniteDistribution<D>(
    _pmf: Map<D, Double>
) {
    init {
        require(_pmf.entries.sumOf { it.value }.equals(1.0, 1e-10)) {
            "Probabilities must sum to 1.0. Violating distribution: $_pmf"
        }
        require(_pmf.entries.any { it.value >= 0.0 }) {
            "Probabilities must be non-negative. Violating distribution: $_pmf"
        }
    }

    /**
     * Probability Mass Function of the distribution mapping each choice with non-zero probability to its probability.
     */
    val pmf = _pmf.filter { it.value > 0.0 }
    constructor(vararg components: Pair<D, Double>): this(components.toMap())

    /**
     * Returns the probability of v.
     */
    operator fun get(v: D) = pmf.getOrDefault(v, 0.0)

    /**
     * Returns the list of all non-zero-probability outcomes.
     */
    val support get() = pmf.keys.toList()

    /**
     * Computes the expected value of the function f according to this distribution.
     */
    fun expectedValue(f: (D)->Double) = pmf.entries.sumOf { it.value * f(it.key) }

    /**
     * Returns the distribution of f(X), where X is distributed according to the receiver (this) distribution.
     */
    fun <E> transform(f: (D)->E): FiniteDistribution<E> {
        val result = hashMapOf<E, Double>()
        for ((k, v) in pmf) {
            val kk = f(k)
            result[kk] = result.getOrDefault(kk, 0.0) + v
        }
        return FiniteDistribution(result)
    }

    /**
     * Generates a random sample from this distribution.
     */
    fun sample(random: Random = Random.Default): D {
        val r = random.nextDouble()
        var cumsum = 0.0
        val pmfList = pmf.toList()
        // TODO: precomputed cumsum+bin search would be more efficient,
        //  if sampling from the same distribution is done frequently
        for ((element, prob) in pmfList) {
            cumsum += prob
            if(cumsum > r)
                return element
        }
        return pmfList.last().first // this should not happen
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as FiniteDistribution<*>

        if (pmf != other.pmf) return false

        return true
    }

    override fun hashCode(): Int {
        return pmf.hashCode()
    }

    override fun toString(): String {
        return "D$($pmf)"
    }

    companion object {
        fun <D> dirac(d: D) = FiniteDistribution(d to 1.0)
    }
}

fun <T> T.dirac() = FiniteDistribution.dirac(this)