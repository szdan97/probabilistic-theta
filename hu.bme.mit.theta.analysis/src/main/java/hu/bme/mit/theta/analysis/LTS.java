package hu.bme.mit.theta.analysis;

import java.util.Collection;

@FunctionalInterface
public interface LTS<S extends State, A extends Action> {

	public Collection<A> getEnabledActionsFor(S state);

}