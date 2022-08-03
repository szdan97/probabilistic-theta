/*
 *  Copyright 2022 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */

package hu.bme.mit.theta.xcfa.passes.procedure

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.Stmts.Assign
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.xcfa.model.*
import kotlin.collections.ArrayList

/**
 * Inlines all procedure invocations in the current procedure.
 * Requires the ProcedureBuilder to be `deterministic`.
 * Sets the `inlined` flag on the ProcedureBuilder.
 */
class InlineProceduresPass : ProcedurePass{
    override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
        checkNotNull(builder.metaData["deterministic"])
        check(builder.metaData["inlined"] == null) {"Recursive programs are not supported by inlining." }
        builder.metaData["inlined"] = Unit
        while(true) {
            var foundOne = false
            for (edge in ArrayList(builder.getEdges())) {
                val pred: (XcfaLabel) -> Boolean = { it -> it is InvokeLabel && builder.parent.getProcedures().any { p -> p.name == it.name } }
                val edges = edge.splitIf(pred)
                if(edges.size > 1 || (edges.size == 1 && pred((edges[0].label as SequenceLabel).labels[0]))) {
                    builder.removeEdge(edge)
                    edges.forEach {
                        if (pred((it.label as SequenceLabel).labels[0])) {
                            foundOne = true
                            val source = it.source
                            val target = it.target
                            val invokeLabel: InvokeLabel = it.label.labels[0] as InvokeLabel
                            val procedure = builder.parent.getProcedures().find { p -> p.name == invokeLabel.name }
                            checkNotNull(procedure)
                            procedure.optimize()

                            val newLocs: MutableMap<XcfaLocation, XcfaLocation> = LinkedHashMap()
                            procedure.getLocs().forEach { newLocs.put(it, it.inlinedCopy()) }
                            procedure.getEdges().forEach { builder.addEdge(it.withSource(newLocs.get(it.source)!!).withTarget(newLocs.get(it.target)!!)) }

                            val inStmts: MutableList<XcfaLabel> = ArrayList()
                            val outStmts: MutableList<XcfaLabel> = ArrayList()
                            for ((i, param) in procedure.getParams().withIndex()) {
                                if (param.second != ParamDirection.OUT) {
                                    val stmt = AssignStmt.of(cast(param.first, param.first.type), cast(invokeLabel.params[i], param.first.type))
                                    inStmts.add(StmtLabel(stmt))
                                }

                                if (param.second != ParamDirection.IN) {
                                    val stmt = AssignStmt.of(cast((invokeLabel.params[i] as RefExpr<*>).decl as VarDecl<*>, param.first.type), cast(param.first.ref, param.first.type))
                                    outStmts.add(StmtLabel(stmt))
                                }
                            }

                            val initLoc = procedure.initLoc
                            val finalLoc = procedure.finalLoc
                            val errorLoc = procedure.errorLoc

                            builder.addEdge(XcfaEdge(source, newLocs[initLoc]!!, SequenceLabel(inStmts)))
                            if (finalLoc.isPresent)
                                builder.addEdge(XcfaEdge(newLocs[finalLoc.get()]!!, target, SequenceLabel(outStmts)))
                            if (errorLoc.isPresent) {
                                if (builder.errorLoc.isEmpty) builder.createErrorLoc()
                                builder.addEdge(XcfaEdge(newLocs[errorLoc.get()]!!, builder.errorLoc.get(), SequenceLabel(listOf())))
                            }
                        } else {
                            builder.addEdge(it)
                        }

                    }
                }
            }
            if (!foundOne) {
                return builder
            }
        }
    }

    private fun XcfaLocation.inlinedCopy() : XcfaLocation {
        return copy(name + XcfaLocation.uniqueCounter(), initial = false, final = false, error = false)
    }
}