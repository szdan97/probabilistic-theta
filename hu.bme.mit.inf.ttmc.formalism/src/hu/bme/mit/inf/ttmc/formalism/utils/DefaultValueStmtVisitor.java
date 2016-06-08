package hu.bme.mit.inf.ttmc.formalism.utils;

import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.AssertStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.AssignStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.AssumeStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.BlockStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.DeclStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.DoStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.HavocStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.IfElseStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.IfStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.ReturnStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.SkipStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.WhileStmt;

public abstract class DefaultValueStmtVisitor<P, R> implements StmtVisitor<P, R> {

	protected abstract R defaultValue(final P param);

	@Override
	public R visit(final SkipStmt stmt, final P param) {
		return defaultValue(param);
	}

	@Override
	public <DeclType extends Type, ExprType extends DeclType> R visit(final DeclStmt<DeclType, ExprType> stmt,
			final P param) {
		return defaultValue(param);
	}

	@Override
	public R visit(final AssumeStmt stmt, final P param) {
		return defaultValue(param);
	}

	@Override
	public R visit(final AssertStmt stmt, final P param) {
		return defaultValue(param);
	}

	@Override
	public <DeclType extends Type, ExprType extends DeclType> R visit(final AssignStmt<DeclType, ExprType> stmt,
			final P param) {
		return defaultValue(param);
	}

	@Override
	public <DeclType extends Type> R visit(final HavocStmt<DeclType> stmt, final P param) {
		return defaultValue(param);
	}

	@Override
	public R visit(final BlockStmt stmt, final P param) {
		return defaultValue(param);
	}

	@Override
	public <ReturnType extends Type> R visit(final ReturnStmt<ReturnType> stmt, final P param) {
		return defaultValue(param);
	}

	@Override
	public R visit(final IfStmt stmt, final P param) {
		return defaultValue(param);
	}

	@Override
	public R visit(final IfElseStmt stmt, final P param) {
		return defaultValue(param);
	}

	@Override
	public R visit(final WhileStmt stmt, final P param) {
		return defaultValue(param);
	}

	@Override
	public R visit(final DoStmt stmt, final P param) {
		return defaultValue(param);
	}

}
