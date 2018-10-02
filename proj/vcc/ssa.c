#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include "util.h"
#include "func.h"
#include "sym.h"
#include "globals.h"
#include "stmt.h"
#include "error.h"

phi_t* new_phi(vertex_t* x)
{
	phi_t*		phi;

	phi		= calloc(1, sizeof(phi_t));
	phi->n		= length(x->pred);
	phi->rhs	= calloc(phi->n, sizeof(op_t));

	return phi;
}

void free_phi(phi_t* phi)
{
	free(phi->rhs);
	free(phi);
}

// static void print_index(void* vp, FILE* fp)
// {
// 	vertex_t*	v = vp;
//
// 	fprintf(fp, "%d", v->index);
// }

void printdf(func_t * func){
	pr("\n----------------------------\n");
	// pr("got call\n");
	vertex_t**	a;
	vertex_t*	w;
	size_t	n,i,k;
	for (k = 0; k < func->nvertex; k++) {
				w = func->vertex[k];
				a = set_to_array(w->df, &n);
				if (n > 0){
						pr("df(%d)", w->dfnum);
						if (w->dfnum < 10) {
							pr(" ");
						}
						pr(" : { %d", a[0]->dfnum);
						for (i = 1; i < n; i++) {
								pr(" , %d ", a[i]->dfnum);
						}
						pr(" } \n");
						free(a);
				}
	}
pr("----------------------------\n\n");
}


static void df(vertex_t* u)
{
	vertex_t**	a;
	size_t	n;
	int i;
	vertex_t *v = u->domchild;
	while (v != NULL){
		df(v);
		v = v->domsibling;
	}
	for (int i = 0; i < 2; i++){
			if (u->succ[i] != NULL){
					if(u->succ[i]->idom != u){
								join_set(&(u->df), u->succ[i]);
					}
			}
	}
	v = u->domchild;
	while (v != NULL){
			a = set_to_array(v->df, &n);
			for (i = 0; i < n; i++) {
					if(a[i]->idom != u){
							join_set(&(u->df), a[i]);
					}
			}
			v = v->domsibling;
			free(a);
	}
}

void modsets(func_t* func)
{
	int		i;
	stmt_t*		stmt;
	vertex_t*	v;
	sym_t*		sym;
	list_t*		p;
	list_t*		h;

	for (i = 0; i < func->nvertex; i += 1) {
		v = func->vertex[i];
		if (v->stmts == NULL)
			continue;
		p = h = v->stmts;
		do {
			stmt = p->data;
			p = p->succ;
			sym = defined_sym(stmt);
			if (sym != NULL)
				join_set(&sym->modset, v);
		} while (p != h);
	}
}

void insert_phi_stmt(func_t* func, vertex_t* vertex, sym_t* sym)
{
	int		i;
	unsigned	line;
	phi_t*		phi;
	stmt_t*		stmt;
	list_t*		p;

	if (vertex == func->exit)
		return;

	p = vertex->stmts;

	stmt = p->data;
	assert(stmt->type == LABEL);
	line = stmt->line;

	stmt = new_stmt(PHI, no_op, no_op, new_sym_op(sym), line);
	insert_after(&p, stmt);

	phi = new_phi(vertex);
	stmt->phi = phi;
	phi->stmt = stmt;
	insert_last(&vertex->phi_func_list, phi);

	for (i = 0; i < phi->n; i += 1)
		phi->rhs[i] = new_sym_op(sym);
}

unsigned which_pred(vertex_t* pred, vertex_t* vertex)
{
	int		i;
	list_t*		h;
	list_t*		p;

	i = 0;

	h = p = vertex->pred;

	assert(p != NULL);

	do {
		if (p->data == pred)
			return i;

		i += 1;

		p = p->succ;

	} while (p != h);

	error(FATAL, "pred not found in which_pred");

	/* We will never get here. */

	return 0;
}

sym_t* getOperandSym(stmt_t * st, int i){
	if (st->type == ST
		|| !is_sym(st->op[i])
		|| is_label(st->op[i]))
		return NULL;
	return st->op[i].u.sym;
}
bool copy_stmt(stmt_t *stmt){
			sym_t * op0, *op1;
			op0 = getOperandSym(stmt, 0);
			op1 = getOperandSym(stmt, 1);
			if (stmt->type == MOV && (op0 != NULL || op1 != NULL)) {
						if(op0 == NULL){
							op0 = op1;
						}
						push(defined_sym(stmt)->rename_stack, top(op0->rename_stack));
						stmt->type = NOP;
						return true;
			} else {
						return false;
			}
}
void rename_symbols(vertex_t* x)
{
	bool pr1 = false;
	if(pr1){pr("\n-----------------------------------------------------------------------------Start(%d)\n", x->dfnum);}

	  list_t *K = NULL;
	  op_t *op;

	  phi_t *phi;
	  stack_t *stack;
		list_t  *p,*h;
		stmt_t *stmt;
		sym_t *sym, *sym2;
		int i,j;
		vertex_t * w;
		p = h = x->stmts;
		if (p != NULL && !copy_stmt(p)){
				do {
							stmt = p->data;
							p = p->succ;
							if(pr1){pr("\n--------------------------------statment [%d]\n", stmt->index );}
							if(pr1){print_stmt(stmt, stdout);}
							for(i = 0; i < 2; i++){
										sym = getOperandSym(stmt, i);
										if(sym != NULL){
													add_use(sym, stmt);
													stmt->op[i].u.sym = top(sym->rename_stack);
													if(pr1){pr("OP[%d] = %s\n", i, sym->id);}
										} else {
													if(pr1){pr("OP[%d] = NULL\n", i);}
										}
							}
							sym = defined_sym(stmt);
							if(sym != NULL){
										// insert_last(&K, sym);
										// op_item = temp();
										// sym->ssa_version = sym->ssa_version +1;
										// op_item.u.sym->ssa_version = sym->ssa_version;
										// push(sym->rename_stack, op_item.u.sym);
										insert_last(&K, sym);
										sym2 = new_sym(sym->id, 0);
										stmt->op[2].u.sym = sym2;
										sym->ssa_version = sym->ssa_version +1;
										push(sym->rename_stack, sym2);
										if(pr1){pr("defin: \"%s\"\n", sym->id);}
							} else {
								if(pr1){pr("defin : NULL\n");}
							}
				} while(p != h);
		} else {
			if(pr1){pr("no statements in vertex %d\n", x->dfnum);}
		}
		for (i = 0 ; i < 2 ; i++){
					w = x->succ[i];
					if(w != NULL){
								if(pr1){pr("\n---------------------------------[%d]->succ[%d] = %d\n", x->dfnum,i, w->dfnum);}
								j = which_pred( x, w );
								if(pr1){pr("we are pred %d to node %d,\n", j, w->dfnum);}
								p = h = w->phi_func_list;
								if (p != NULL) {
											do{
														phi = p->data;
														p = p->succ;
														op = phi->rhs+j;
														sym = op->u.sym;
														stack = sym->rename_stack;
														op->u.sym = top(stack);
														add_use(sym, phi->stmt);
														if(pr1){pr("%s, ",sym->id);}
														}while(p != h);
											if(pr1){pr("\n");}
								} else {
											if(pr1){pr("no phi func\n");}
								}
					} else {
						if(pr1){pr("NULL\n");}
					}
		}
		w = x->domchild;
		while (w != NULL){
			if(pr1){pr("\ndomchild(%d): %d", x->dfnum, w->dfnum);}
						rename_symbols(w);
						w = w->domsibling;
		}
		p = h = K;
		if(pr1){pr("\n-------------------------\"-I keep it poppin\" [%d]\n",x->dfnum);}
		if(p != NULL){
					do{
								sym = p->data;
								p = p->succ;
								pop(sym->rename_stack);
								if(pr1){pr("%s, ", sym->id);}
					}while(p != h);
		} else {
					if(pr1){pr("No poppin...\n");}
		}
	if(pr1){pr("\n------------------------------------------------------------------------------END(%d)\n", x->dfnum);}
}

void insert_phi(func_t* func)
{
	/* Insert phi functions. Figure 11. */

	int		iter;		/* Itereration count of Figure 11. */
	sym_t*		sym;		/* Variable V of Figure 11. */
	vertex_t*	x;		/* Node X of Figure 11. */
	vertex_t*	y;		/* Node Y of Figure 11. */
	vertex_t**	a;		/* Node Y of Figure 11. */
	int		i;
	size_t		n;
	list_t*		p;
	list_t*		h;
	list_t*		worklist;

	iter = 0;

	if (func->var == NULL)
		return;

	for (i = 0; i < func->nvertex; i += 1)
		func->vertex[i]->work = func->vertex[i]->already = 0;

	p = h = func->var;

	worklist = NULL;

	do {

		sym = p->data;
		p = p->succ;
		iter += 1;

		/* Add all basic blocks where sym which have an assignment
		 * to sym to the basic block worklist.
		 *
		 */

		/* Create a temporary array for simplicity. */

		if (use_pr) {
		//	pr("modset(%s) = ", sym->id);
		//	print_set(sym->modset, print_index, stdout);
		}

		a = set_to_array(sym->modset, &n);
		for (i = 0; i < n; i += 1) {
			x = a[i];
			x->work = iter;
			insert_last(&worklist, x);
		}
		free(a);

		/* Now worklist contains all assignment nodes of sym. */

		while (worklist != NULL) {
			x = remove_first(&worklist);

			/* Create a temporary array for simplicity. */
			a = set_to_array(x->df, &n);
			for (i = 0; i < n; i += 1) {
				y = a[i];

				if (y->already >= iter)
					continue;

				assert(y != func->vertex[0]);
				insert_phi_stmt(func, y, sym);
				y->already = iter;
				if (y->work >= iter)
					continue;
				y->work = iter;
				insert_last(&worklist, y);
			}
			free(a);
		}

	} while (p != h);
}

void to_ssa(func_t* func)
{
	sym_t*		sym;
	list_t*		p;
	list_t*		h;


	if (func->var == NULL)
		return;

	df(func->vertex[0]);

//	printdf(func);//-----------------------------------------------

	p = h = func->var;
	do {
		sym = p->data;
		p = p->succ;
		join_set(&sym->modset, func->vertex[0]);
		sym->rename_stack = new_stack();
		push(sym->rename_stack, sym);
		// pr("sym %d , use ", sym->index);
		// if (sym->uses == NULL){
		// 	pr("NULL\n");
		// }else {
		// 	pr("other\n");
		// }
	} while (p != h);

	modsets(func);
	insert_phi(func);
	rename_symbols(func->vertex[0]);

	p = h = func->var;
	do {
		sym = p->data;
		p = p->succ;
		free_stack(&sym->rename_stack);
	} while (p != h);

	free_list(&func->var);
}

static void fix_move(phi_t* phi, list_t** moves)
{
	stmt_t*		move;
	sym_t*		phi_dest;
	op_t		t;

	t = temp();

	phi_dest = phi->stmt->op[2].u.sym;
	phi->stmt->op[2].u.sym = t.u.sym;

	/* Save the real destination operand of the PHI function in
	 * move->op[1] and also tell the move which PHI this was.
	 */

	move = new_stmt(MOV, t, no_op, new_sym_op(phi_dest), line);
	move->op[1] = new_sym_op(phi_dest);
	move->phi = phi;

	/* This move will be put after all the normal moves inserted by
	 * from_ssa.
	 */
	insert_last(moves, move);
}

static void check_later_use(phi_t* phi, list_t* link, list_t** moves, int k)
{
	stmt_t*		stmt;

	link = link->succ;
	stmt = link->data;

	/* If there is a later use as a PHI-operand of the destination,
	 * then we must save the value so that use can consume it.
	 */

	while (stmt->type == PHI || stmt->type == NOP) {

		if (stmt->type == PHI
			&& is_sym(stmt->phi->rhs[k])
			&& stmt->phi->rhs[k].u.sym == phi->stmt->op[2].u.sym)
			fix_move(phi, moves);

		link = link->succ;
		stmt = link->data;
	}

}

static void insert_move(
	vertex_t*		pred,
	phi_t*		phi,
	int		k,
	list_t*		link,
	list_t**	moves)
{
	list_t*		p;
	stmt_t*		last_stmt;
	stmt_t*		stmt;
	stmt_t*		move;
	unsigned	line;
	op_t		op;

	/* We take as line number of our new move statement, the line
	 * number of the last statement in the basic block.
	 *
	 */

	last_stmt = pred->stmts->pred->data;
	assert(last_stmt->type == BA);

	line = last_stmt->line;

	check_later_use(phi, link, moves, k);

	op = new_sym_op(phi->stmt->op[2].u.sym);
	move = new_stmt(MOV, phi->rhs[k], no_op, op, line);

	p = pred->stmts->pred->pred;
	stmt = p->data;

	if (is_branch(stmt))
		insert_before(&p, move);
	else
		insert_after(&p, move);

}

static void insert_move_before_branch(vertex_t* w, stmt_t* move)
{
	list_t*		p;
	stmt_t*		stmt;

	if (w->stmts == NULL)
		return;

	assert(move->op[1].type != NO_OP);

	/* Now restore the PHI function so that it has the correct
	 * destination operand.
	 */

	move->phi->stmt->op[2] = move->op[1];
	move->op[1] = no_op;
	move->phi = NULL;

	p = w->stmts->pred->pred;
	stmt = p->data;

	if (is_branch(stmt))
		insert_before(&p, move);
	else
		insert_after(&p, move);
}

static void insert_move_list(vertex_t* w, list_t* moves)
{
	list_t*		p;

	p = moves;

	do {
		insert_move_before_branch(w, p->data);
		p = p->succ;
	} while (p != moves);
}

void from_ssa(func_t* func)
{
	vertex_t*	x;
	vertex_t*	pred;
	int		i;
	int		k;
	phi_t*		phi;
	stmt_t*		stmt;
	list_t*		q;
	list_t*		p;
	list_t*		more_moves;

	// printf("LAB 2: Remove RETURN in \"%s\", line %d\n",
	// 	__FILE__, 1+(int)__LINE__);
	// return;

	for (i = 1; i < func->nvertex; i += 1) {
		x = func->vertex[i];

		if (x == func->exit)
			continue;

		assert(x->stmts != NULL);

		p = x->pred;

		do {
			// Next predecessor vertex.
			pred = p->data;
			p = p->succ;
			k = which_pred(pred, x);

			// Find link of first PHI.
			q = x->stmts;
			q = q->succ;

			// Reset stmt to first PHI (which might be a NOP now).
			stmt = q->data;

			more_moves = NULL;

			while (stmt->type == PHI || stmt->type == NOP) {

				if (stmt->type == PHI) {
					phi = stmt->phi;
					insert_move(pred, phi, k, q,
						&more_moves);
				}

				q = q->succ;
				stmt = q->data;

			}

			if (more_moves != NULL) {
				insert_move_list(pred, more_moves);
				free_list(&more_moves);
			}

			q = q->succ;
			stmt = q->data;
		} while (p != x->pred);

		// Finally change each PHI into a NOP.
		q = x->stmts;
		q = q->succ;
		stmt = q->data;

		while (stmt->type == PHI || stmt->type == NOP) {
			stmt->type = NOP;
			q = q->succ;
			stmt = q->data;
		}
	}
}
