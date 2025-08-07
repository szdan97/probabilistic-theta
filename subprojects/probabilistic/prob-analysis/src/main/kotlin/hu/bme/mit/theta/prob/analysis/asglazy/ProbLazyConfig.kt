package hu.bme.mit.theta.prob.analysis.asglazy

import hu.bme.mit.theta.common.logging.ConsoleLogger
import hu.bme.mit.theta.common.logging.Logger

data class ProbLazyConfig(
    val useMay: Boolean = true,
    val useMust: Boolean = false,
    val verboseLogging: Boolean = false,
    val logger: Logger = ConsoleLogger(Logger.Level.VERBOSE),
    val resetOnUncover: Boolean = true,
    val useMonotonicBellman: Boolean = false,
    val useSeq: Boolean = false,
    val useGameRefinement: Boolean = false,
    val useQualitativePreprocessing: Boolean = false,
    val mergeSameSCNodes: Boolean = true
)