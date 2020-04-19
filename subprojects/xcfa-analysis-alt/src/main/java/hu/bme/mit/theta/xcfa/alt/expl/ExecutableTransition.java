/*
 * Copyright 2019 Budapest University of Technology and Economics
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package hu.bme.mit.theta.xcfa.alt.expl;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.xcfa.XCFA;

import java.util.Collection;
import java.util.Optional;
import java.util.logging.Logger;

/**
 * An enabled transition with the matching transition.
 */
public class ExecutableTransition implements Transition, TransitionExecutorInterface {
    private final Transition transition;
    private final TransitionExecutorInterface executor;

    protected ExecutableTransition(ExecutableTransition et) {
        this.transition = et.transition;
        this.executor = et.executor;
    }

    private ExecutableTransition(Transition transition, TransitionExecutorInterface executor) {
        this.transition = transition;
        this.executor = executor;
    }

    /**
     * Creates an ExecutableTransition if the transition is enabled.
     * Should only be called by {@link ExecutableTransitionUtils}.
      */
    static Optional<ExecutableTransition> from(ExplState state, Transition transition) {
        return transition.enabled(state).map(
                t->new ExecutableTransition(transition, t)
        );
    }

    /** Probably you won't use this. */
    @Override
    public Optional<TransitionExecutorInterface> enabled(ExplState state) {
        // The problem is we cannot check whether the same state was passed here as the time
        // where this.executor was created.
        Logger.getLogger(getClass().getName()).warning("Probably bad usage calling " +
                "ExecutableTransition::enabled. Proceed with caution.");
        return Optional.of(executor);
    }

    /** Fall-through */
    @Override
    public Collection<VarDecl<? extends Type>> getWVars() {
        return transition.getWVars();
    }

    /** Fall-through */
    @Override
    public Collection<VarDecl<? extends Type>> getRWVars() {
        return transition.getRWVars();
    }

    /** Fall-through */
    @Override
    public XCFA.Process getProcess() {
        return transition.getProcess();
    }

    /** Fall-through */
    @Override
    public boolean isLocal() {
        return transition.isLocal();
    }

    /** Fall-through.
     * This should only be used by ExecutableTransitionFor(Imm|M)utableExplState
     * or inside an {@link ExplStateMutatorInterface}. */
    @Override
    public void executeInternal(ExplStateMutatorInterface state) {
        executor.executeInternal(state);
    }

    @Override
    public String toString() {
        return transition.toString();
    }
}