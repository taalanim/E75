#include <assert.h>
#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <limits.h>
#include "util.h"
#include "cfg.h"
#include "func.h"
#include "sym.h"
#include "globals.h"
#include "error.h"

static bool visited(vertex_t* v)
{
	return v->dfnum != -1;
}

static void dfs(vertex_t* v, int* dfnum, vertex_t** vertex)
{
	/* MAKE COMPLETE DURING LAB 1 */
	v->dfnum = *dfnum;
	vertex[*dfnum] = v;
	v->sdom = v;
	v->ancestor = NULL;
	*dfnum = *dfnum + 1;
	int i = 0;
	vertex_t *w;
		for ( ; i<2 ; i++){
			w = v->succ[i];
			if((w != NULL) && !visited(w)){
				w->parent = v;
				dfs(w, dfnum, vertex);
			}
		}
	// v = v;
	// dfnum = dfnum;
	// vertex = vertex;

	/* succ[0] corresponds to the target of a conditional branch.
	 * succ[0] is NULL for an unconditional branch (BA).
	 * succ[1] corresponds to the target of an unconditional branch.
	 *
	 */
}

static void link(vertex_t* parent, vertex_t* child)
{
	child->ancestor = parent;
	// pr("ancestor(%d) = %d\n", child->dfnum, parent->dfnum);
}

static vertex_t* eval(vertex_t* v)
{
	vertex_t*		u;

	u = v;

	/* Find the ancestor of V with least semi-dominator. */

	while (v->ancestor != NULL) {

		if (v->sdom->dfnum < u->sdom->dfnum)
			u = v;

		v = v->ancestor;
	}

	return u;
}

static void remove_from_preds(vertex_t* w)
{
	int		i;

	for (i = 0; i < MAX_SUCC; ++i)
		if (w->succ[i] != NULL)
			remove_from_list(&w->succ[i]->pred, w);
}

static void free_stmts(vertex_t* w)
{
	list_t*		p;
	list_t*		h;

	p = h = w->stmts;

	do {
		free_stmt(p->data);
		p = p->succ;
	} while (p != h);
}

connectToSibling(vertex_t *u,vertex_t *w){
	if (u->domsibling == NULL){
		u->domsibling = w;
	} else {
		connectToSibling(u->domsibling, w);
	}

}
void connectDomTree(func_t* func){
		int i;
		vertex_t	*w;
		for (i = 0; i < func->nvertex; i++)	{
			// pr("running for vertex %d", w->dfnum);
				w = func->vertex[i];
				if (w->idom != NULL){
						if (w->idom->domchild == NULL){
							w->idom->domchild = w;
						} else{
							connectToSibling(w->idom->domchild, w);
						}
				}	else{
					// pr("idom(%d) = NULL", w->dfnum);
				}
		}
}


void dominance(func_t* func)
{

	int		i;
	int		dfnum;
	vertex_t*	u;
	vertex_t*	v;
	vertex_t*	w;
	list_t*		p;
	list_t*		h;
	vertex_t*	original[func->nvertex];

	// printf("LAB 1: Remove RETURN in \"%s\", line %d\n",
	// 	__FILE__, 1+(int)__LINE__);
	// return;

	if (0) visited(NULL);	/* For silencing GCC. */

	/* Construct the immediate-dominator tree. */

	memcpy(original, func->vertex, sizeof original);



	/* Step 1. */

	/* Initialise sdom of each vertex to itself. */
	for (i = 0; i < func->nvertex; i++)	{
		func->vertex[i]->dfnum		= -1;
		func->vertex[i]->sdom		= func->vertex[i];
		func->vertex[i]->idom		= NULL;
		func->vertex[i]->ancestor	= NULL;
		func->vertex[i]->parent		= NULL;
		func->vertex[i]->domchild	= NULL;
		func->vertex[i]->domsibling	= NULL;

		if (func->vertex[i] == func->start) {
			u = func->vertex[0];
			func->vertex[0] = func->start;
			func->vertex[i] = u;
		}
	}

	dfnum = 0;

	assert(func->vertex[0] == func->start);

	dfs(func->vertex[0], &dfnum, func->vertex);

	// dead code elim??
	for (i = 0; i < func->nvertex; ++i) {
		if (original[i]->dfnum == -1) {
			remove_from_preds(original[i]);
			free_stmts(original[i]);
			free_vertex(original[i]);
		}
	}
	func->nvertex = dfnum;
	print_cfg(func);
	for (i = func->nvertex - 1; i > 0; i--) {
			w = func->vertex[i];
			/* Step 2. */
			assert(w->pred != NULL);
			p = h = w->pred;
			do {
						v = p->data;
						p = p->succ;
						u = eval(v);
		if(u->sdom->dfnum < w->sdom->dfnum){
								w->sdom = u->sdom;
						}
			} while (p != h);
			link(w->parent, w);
			/* Step 3. */
			insert_first(&w->sdom->bucket, w);
			p = h = w->parent->bucket;
			if (p == NULL){
						continue;
			} else {
						do {
									v = p->data;
									p = p->succ;
						} while (p != h);
					}
			p = h = w->parent->bucket;
			do {
						v = p->data;
						p = p->succ;
						u = eval(v);
						if(u->sdom->dfnum < v->sdom->dfnum){
								v->idom = u;
						} else {
								v->idom = w->parent;
						}
					} while (p != h);

			free_list(&w->parent->bucket);
		}

	pr("\ngaffel 1\n");
	/* Step 4. */
	for (i = 1; i < func->nvertex; i++) {
				w = func->vertex[i];
				pr("\ngaffel 1.2\n");
				pr("\nsdom(%d) = %d\n", w->dfnum, w->sdom->dfnum);
				pr("\nidom(%d) = %d\n", w->dfnum, w->idom->dfnum);
				if(w->idom != w->sdom){
							pr("\ngaffel 1.3\n");
							w->idom = w->idom->idom;
							pr("\ngaffel 1.4\n");
				}
				pr("\ngaffel 1.5\n");
		}
		pr("\ngaffel 2\n");
	connectDomTree(func);
	print_dt(func);
}
