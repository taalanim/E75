#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include "util.h"
#include "func.h"
#include "cfg.h"
#include "globals.h"
#include "error.h"
#include "list.h"

func_t*	func;	/* our only function to parse, optimise, and run. */


bool confirmNumOfPredsIsOnlyTwo(func_t *func){
	vertex_t *w;
	int i;
	for (i = 0; i < func->nvertex; i++) {
		w = func->vertex[i];
		if (length(w->pred) > 2){
			return false;
		}
	}
	return true;
}


func_t* makeACopyVersionOfFunc(func_t *func){
	vertex_t *w, *u, *v;
	list_t *p,*h;
	int i, j;
	func_t *copy = calloc(1, sizeof(func_t));
	copy->nvertex = func->nvertex;
	copy->vertex = malloc(sizeof(func->vertex));
	for (i = 0; i < func->nvertex; i++) {// set up a set of copies
		w = func->vertex[i];
		u = copy->vertex[i] = malloc(sizeof(vertex_t));
		memcpy(u, w, sizeof(vertex_t));
		w->copy = u;
		u->copy = w;
	}
	for (i = 0; i < func->nvertex; i++) {// reverse the order of the copies;
		j = 0;
		w = func->vertex[i];
		u = copy->vertex[i];
		p = h = w->pred;
		if(p != NULL){ // set new succs
			do{
				v = p->data;
				p = p->succ;
				u->succ[j] = v->copy;
				j++;
			}while(p != h);
		}
		for(j = 0; j < 2; j++){// set new preds
			if(w->succ[j] != NULL){
				insert_last(&u->pred, w->succ[j]->copy);
			}
		}
	}
	copy->start = func->exit->copy;
	copy->exit = func->start->copy;
	return copy;
}

void free_workcopy(func_t* copy){
	int		i;
	for (i = 0; i < copy->nvertex; ++i){
		free_vertex(copy->vertex[i]);
	}
	free(copy->vertex);
	free(func);
}


bool postDomFront(func_t *func){
	if (!confirmNumOfPredsIsOnlyTwo(func)){
		pr("\ntoo many preds\n");
		return false;
	}
	func_t * workCopy = makeACopyVersionOfFunc(func);
	pr("\ngaffel 5\n");
	dominance(workCopy);
	pr("\ngaffel 6\n");
	free_workcopy(workCopy);
	return true;
}





void init_func()
{
	func = calloc(1, sizeof(func_t));
}

void free_func()
{
	int		i;

	for (i = 0; i < func->nvertex; ++i)
		free_vertex(func->vertex[i]);
	free(func->vertex);
	free_list(&func->var);
	free_list(&func->stmts);
	free(func);
}

void add_stmt(stmt_t* stmt)
{
	/* Add a stmt to the function. */
	insert_last(&func->stmts, stmt);
}

void add_sym(sym_t* sym)
{
	/* Add a variable to the function. */
	insert_last(&func->var, sym);
}

static void clean_stmt_list(list_t* h)
{
	stmt_t*		stmt;
	list_t*		p;

	if (h == NULL)
		return;

	p = h;

	do {
		stmt = p->data;
		p = p->succ;
		if (stmt->type == NOP) {
			free_stmt(stmt);
			delete_list(p->pred);
		}
	} while (p != h);
}

void clean_nop(func_t* func)
{
	int		i;

	if (func->stmts != NULL)
		clean_stmt_list(func->stmts);
	else {
		for (i = 0; i < func->nvertex; ++i)
			clean_stmt_list(func->vertex[i]->stmts);
	}
}

void opt(void)
{
	print_func("before opt");

	to_cfg(func);
	assert(func->exit->pred != NULL);
	use_pr = false;
	dominance(func);

	if (cfg_fp != NULL)
		return;

	to_ssa(func);
	clean_nop(func);
	print_func("after to ssa");

	use_pr = true;

	if(postDomFront(func)){
		print_func("postDomFront was successfull");
	} else{
		print_func("postDomFront was not succ");
	}
	from_ssa(func);
	print_func("after from ssa");

	fix_const_operand(func);

	print_func("before alloc regs");
	alloc_regs(func);
	print_func("after alloc regs");

	from_cfg(func);
}

void print_stmt_list(list_t* h, FILE* fp)
{
	list_t*		p;
	stmt_t*		stmt;

	if (h == NULL)
		return;

	p = h;

	do {
		stmt = p->data;
		print_stmt(stmt, fp);
		p = p->succ;

	} while (p != h);
}

void print_func(char* header)
{
	int		i;
	static int	print_count;
	char		buf[BUFSIZ];
	FILE*		fp;

	if (cfg_fp != NULL)
		return;

	sprintf(buf, "%s:%d", source, print_count);
	fp = fopen(buf, "w");
	print_count += 1;

	if (fp == NULL)
		error(SYSERR, "cannot open %s for writing", buf);

	fprintf(fp, "%s\n", header);

	if (func->stmts != NULL)
		print_stmt_list(func->stmts, fp);
	else {
		for (i = 0; i < func->nvertex; i += 1)
			print_stmt_list(func->vertex[i]->stmts, fp);
	}

	fclose(fp);
}

instr_t* stmt2instr(int* size)
{
	unsigned	addr;
	unsigned	k;
	stmt_t*		stmt;
	instr_t*	v;
	list_t*		h;
	list_t*		p;

	/* Convert the stmts list of func into an array of instr
	 * which can then be used as the program memory when running
	 * the program.
	 *
	 */

	addr = 0;

	assert(func->stmts != NULL);

	p = h = func->stmts;

	/* Count the number of instructions we will need, and
	 * and set the address of each stmt.
	 *
	 */

	do {
		stmt = p->data;

		set_stmt_addr(stmt, addr);

		/* Skip LABEL and NOP (former PHIs) */
		if (is_real(stmt))
			addr += 1;

		p = p->succ;

	} while (p != h);

	v = calloc(addr, sizeof(instr_t));

	k = 0;
	p = h = func->stmts;
	do {
		stmt = p->data;

		if (is_branch(stmt)) {
			/* Branch instructions are PC-relative, that is
			 * we now figure out how many instructions forward
			 * or backward the branch should jump (if it is taken).
			 *
			 * This is the essence of what a link-editor does.
			 *
			 */

			relocate(stmt);
		}

		if (is_real(stmt)) {
			v[k] = make_instr(stmt);
			k += 1;
		}

		p = p->succ;

	} while (p != h);

	do {
		stmt = p->data;
		free_stmt(stmt);
		p = p->succ;
	} while (p != h);

//	print_func("after to instr");

	assert(k == addr);

	*size = addr;

	return v;
}
