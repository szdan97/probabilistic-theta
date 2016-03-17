package hu.bme.mit.inf.ttmc.constraint.z3.factory;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.HashMap;

import com.microsoft.z3.Context;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.constraint.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.constraint.factory.DeclFactory;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.z3.decl.Z3ConstDecl;
import hu.bme.mit.inf.ttmc.constraint.z3.decl.Z3ParamDecl;
import hu.bme.mit.inf.ttmc.constraint.z3.solver.Z3SymbolWrapper;

public final class Z3DeclFactory implements DeclFactory, Z3SymbolWrapper {

	private final ConstraintManager manager;

	private final Context context;

	private final HashMap<String, ConstDecl<?>> nameToConst;

	public Z3DeclFactory(final ConstraintManager manager, final Context context) {
		this.manager = manager;
		this.context = context;
		nameToConst = new HashMap<String, ConstDecl<?>>();
	}

	@Override
	public <T extends Type> ConstDecl<T> Const(final String name, final T type) {
		checkNotNull(name);
		checkNotNull(type);
		checkArgument(name.length() > 0);
		checkArgument(nameToConst.get(name) == null);

		final ConstDecl<T> constDecl = new Z3ConstDecl<>(manager, name, type, context);
		nameToConst.put(name, constDecl);
		return constDecl;
	}

	@Override
	public <T extends Type> ParamDecl<T> Param(final String name, final T type) {
		checkNotNull(name);
		checkNotNull(type);
		checkArgument(name.length() > 0);

		final ParamDecl<T> paramDecl = new Z3ParamDecl<>(manager, name, type, context);
		return paramDecl;
	}

	@Override
	public ConstDecl<?> wrap(final com.microsoft.z3.FuncDecl symbol) {
		checkNotNull(symbol);
		final String name = symbol.getName().toString();
		final ConstDecl<?> constDecl = nameToConst.get(name);
		checkNotNull(constDecl);
		return constDecl;
	}
}
