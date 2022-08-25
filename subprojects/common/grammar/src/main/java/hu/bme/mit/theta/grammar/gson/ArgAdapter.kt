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

package hu.bme.mit.theta.grammar.gson

import com.google.gson.Gson
import com.google.gson.TypeAdapter
import com.google.gson.stream.JsonReader
import com.google.gson.stream.JsonWriter
import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.analysis.PartialOrd
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.analysis.algorithm.ARG
import java.lang.reflect.Type

class ArgAdapter<S: State, A: Action>(val gsonSupplier: () -> Gson, private val partialOrd: PartialOrd<S>, private val argType: Type)  : TypeAdapter<ARG<S, A>>() {
    private lateinit var gson: Gson

    override fun write(writer: JsonWriter, value: ARG<S, A>) {
        initGson()
        gson.toJson(gson.toJsonTree(ArgAdapterHelper(value)), writer)
    }

    override fun read(reader: JsonReader): ARG<S, A> {
        initGson()
        val argAdapterHelper: ArgAdapterHelper<S, A> = gson.fromJson(reader, argType)
        return argAdapterHelper.instantiate(partialOrd)
    }

    private fun initGson() {
        if(!this::gson.isInitialized) gson = gsonSupplier()
    }
}