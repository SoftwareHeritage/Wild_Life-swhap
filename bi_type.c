/*									tab:4
 *
 * bi_type.c - builtins for doing type heierachy stuff
 *
 * Copyright (c) 1992 Digital Equipment Corporation
 * All Rights Reserved.
 *
 * The standard digital prl copyrights exist and where compatible
 * the below also exists.
 * Permission to use, copy, modify, and distribute this
 * software and its documentation for any purpose and without
 * fee is hereby granted, provided that the above copyright
 * notice appear in all copies.  Copyright holder(s) make no
 * representation about the suitability of this software for
 * any purpose. It is provided "as is" without express or
 * implied warranty.
 *
 * Author: 			Seth Copen Goldstein
 * Version:			48
 * Creation Date:	Tue May 26 13:55:47 1992
 * Filename:		bi_type.c
 * History:
 */
static char _version_string_[] = "\nVersion:1:bi_type.c\0\n";

#include "extern.h"
#include "trees.h"
#include "login.h"
#include "parser.h"
#include "copy.h"
#include "token.h"
#include "print.h"
#include "lefun.h"
#include "memory.h"
#include "built_ins.h"
#include "error.h"

#ifdef X11
#include "xpred.h"
#endif

/******** C_CHILDREN
  Return a list of roots of the children types of T (except bottom).
*/
static int c_children()
{
  int success=TRUE;
  ptr_psi_term funct,result,arg1,arg2,t,tmp,p1;
  ptr_list l;
  ptr_int_list p;

  funct=aim->a;
  deref_ptr(funct);
  result=aim->b;
  get_two_args(funct->attr_list,&arg1,&arg2);
  if (!arg1)
  {
	  curry();
	  return success;
  }

  deref(arg1);
  deref_args(funct,set_1);
  resid_aim=NULL;
  t = stack_psi_term(0);
  t->type = alist;
  t->value = (GENERIC) (l=STACK_ALLOC(list));
  l->car = NULL;
  l->cdr = NULL;
  if (arg1->type==top)
  {
      ptr_psi_term *tail;
      collect_symbols(greatest_sel, symbol_table, &t, &tail);
      *tail=NULL;
  }
  else
  {
	  p = arg1->type->children;
      while (p)
	  {
		  ptr_definition ptype;
		  
		  ptype = (ptr_definition) p->value;
		  if (hidden_type(ptype)) { p=p->next; continue; }
		  p1 = stack_psi_term(0);
		  p1->type = ptype;
		  l = STACK_ALLOC(list);
		  l->car = p1;
		  l->cdr = (tmp=stack_psi_term(0));
		  tmp->type = alist;
		  tmp->value = t->value;
		  t->value = (GENERIC) l;
		  p = p->next;
      }
  }
  push_goal(unify,result,t,NULL);

  return success;
}



/******** C_PARENTS
  Return a list of roots of the parent types of T.
*/
static int c_parents()
{
  int success=TRUE;
  ptr_psi_term funct,result,arg1,arg2,t,tmp,p1;
  ptr_list l;
  ptr_int_list p;

  funct=aim->a;
  deref_ptr(funct);
  result=aim->b;
  get_two_args(funct->attr_list,&arg1,&arg2);
  if (arg1) {
    deref(arg1);
    deref_args(funct,set_1);
    resid_aim=NULL;
    t = stack_psi_term(4);
    t->type = alist;
    t->value = (GENERIC) (l=STACK_ALLOC(list));
    l->car = NULL;
    l->cdr = NULL;
    p = arg1->type->parents;
    if (arg1->type!=top && p==NULL) {
      /* Top is the only parent */
      p1 = stack_psi_term(4);
      p1->type = (ptr_definition) top;
      l = STACK_ALLOC(list);
      l->car = p1;
      l->cdr = (tmp=stack_psi_term(4));
      tmp->type = alist;
      tmp->value = t->value;
      t->value = (GENERIC) l;
    }
    else {
      if ((arg1->type==quoted_string || arg1->type==integer ||
          arg1->type==real) && arg1->value!=NULL) {
        /* arg1 is a string, int or real: return a list with arg1 as
           argument, where arg1->value = NULL, MH */
        p1 = stack_psi_term(4);
        p1->type = arg1->type;
        l = STACK_ALLOC(list);
        l->car = p1;
        l->cdr = (tmp=stack_psi_term(4));
        tmp->type = alist;
        tmp->value = t->value;
        t->value = (GENERIC) l;
      }
      else {
        /* Look at the parents list */
        while (p) {
          ptr_definition ptype;

          ptype = (ptr_definition) p->value;
          if (hidden_type(ptype)) { p=p->next; continue; }
          p1 = stack_psi_term(4);
          p1->type = ptype;
          l = STACK_ALLOC(list);
          l->car = p1;
          l->cdr = (tmp=stack_psi_term(4));
          tmp->type = alist;
          tmp->value = t->value;
          t->value = (GENERIC) l;
          p = p->next;
        }
      }
    }
    push_goal(unify,result,t,NULL);
  }
  else
    curry();

  return success;
}


/******** C_SMALLEST
  Return the parents of bottom.
  This function has no arguments.
*/
static int c_smallest()
{
  int success=TRUE;
  ptr_psi_term result, g, t, *tail;

  g=aim->a;
  deref_args(g,set_empty);
  result=aim->b;
  collect_symbols(least_sel, symbol_table, &t, &tail);
  *tail=NULL;
  push_goal(unify,result,t,NULL);

  return success;
}

isSubTypeValue(arg1, arg2)
ptr_psi_term arg1, arg2;
{
  int ans=TRUE;
  
  /* we already know that either arg1->type == arg2->type or that at both
   * of the two are either int or real
   */
  
  if (arg2->value) {
    if (arg1->value) {
      if (arg1->type==real || arg1->type==integer) {
        ans=( *(REAL *)arg1->value == *(REAL *)arg2->value);
      }
      else if (arg1->type==quoted_string) {
        ans=strcmp((char *)arg1->value,(char *)arg2->value)==0;
      }
      else if (arg1->type==alist) {
        /* [] isa [] and [_|_] isa [_|_] */
        ans = (((ptr_list)arg1->value)->car==NULL) ==
          (((ptr_list)arg2->value)->car==NULL);
      }
    }
    else
      ans=FALSE;
  }
  else {
    if (arg1->value && (arg1->type==real || arg1->type==integer)) {
      if (arg2->type==integer)
        ans=(*(REAL *)arg1->value == floor(*(REAL *)arg1->value));
      else
        ans=TRUE;
    }
  }
  return ans;
}

/* Boolean utility function that implements isa */
static int isa(arg1,arg2)
ptr_psi_term arg1, arg2;
{
  int ans;
  
  if (  arg1->type==arg2->type
     || (  (arg1->type==real || arg1->type==integer)
        && (arg2->type==real || arg2->type==integer)
        && (arg1->value || arg2->value)
        )
     ) {
    ans=isSubTypeValue(arg1, arg2);
  }
  else {
    matches(arg1->type, arg2->type, &ans);
  }
  return ans;
}

#define isa_le_sel 0
#define isa_lt_sel 1
#define isa_ge_sel 2
#define isa_gt_sel 3
#define isa_eq_sel 4
#define isa_nle_sel 5
#define isa_nlt_sel 6
#define isa_nge_sel 7
#define isa_ngt_sel 8
#define isa_neq_sel 9
#define isa_cmp_sel 10
#define isa_ncmp_sel 11

/* Utility that selects one of several isa functions */
static int isa_select(arg1,arg2,sel)
ptr_psi_term arg1,arg2;
int sel;
{
  int ans;

  switch (sel) {
  case isa_le_sel: ans=isa(arg1,arg2);
    break;
  case isa_lt_sel: ans=isa(arg1,arg2) && !isa(arg2,arg1);
    break;
  case isa_ge_sel: ans=isa(arg2,arg1);
    break;
  case isa_gt_sel: ans=isa(arg2,arg1) && !isa(arg1,arg2);
    break;
  case isa_eq_sel: ans=isa(arg1,arg2) && isa(arg2,arg1);
    break;

  case isa_nle_sel: ans= !isa(arg1,arg2);
    break;
  case isa_nlt_sel: ans= !(isa(arg1,arg2) && !isa(arg2,arg1));
    break;
  case isa_nge_sel: ans= !isa(arg2,arg1);
    break;
  case isa_ngt_sel: ans= !(isa(arg2,arg1) && !isa(arg1,arg2));
    break;
  case isa_neq_sel: ans= !(isa(arg1,arg2) && isa(arg2,arg1));
    break;

  case isa_cmp_sel: ans=isa(arg1,arg2) || isa(arg2,arg1);
    break;
  case isa_ncmp_sel: ans= !(isa(arg1,arg2) || isa(arg2,arg1));
    break;
  }
  return ans;
}

/******** C_ISA_MAIN
  Main routine to handle all the isa built-in functions.
*/
static int c_isa_main(sel)
int sel;
{
  int success=TRUE,ans;
  ptr_psi_term arg1,arg2,funct,result;

  funct=aim->a;
  deref_ptr(funct);
  result=aim->b;
  get_two_args(funct->attr_list,&arg1,&arg2);
  if (arg1 && arg2) {
    deref(arg1);
    deref(arg2);
    deref_args(funct,set_1_2);
    ans=isa_select(arg1,arg2,sel);
    unify_bool_result(result,ans);
  }
  else curry();

  return success;
}

/******** C_ISA_LE
  Type t1 isa t2 in the hierarchy, i.e. t1 is less than or equal to t2.
  This boolean function requires two arguments and never residuates.
  It will curry if insufficient arguments are given.
  It works correctly on the 'value' types, i.e. on integers, reals, strings,
  and lists.  For lists, it looks only at the top level, i.e. whether the
  object is nil or a cons cell.
*/
static int c_isa_le()
{
  return c_isa_main(isa_le_sel);
}

static int c_isa_lt()
{
  return c_isa_main(isa_lt_sel);
}

static int c_isa_ge()
{
  return c_isa_main(isa_ge_sel);
}

static int c_isa_gt()
{
  return c_isa_main(isa_gt_sel);
}

static int c_isa_eq()
{
  return c_isa_main(isa_eq_sel);
}

static int c_isa_nle()
{
  return c_isa_main(isa_nle_sel);
}

static int c_isa_nlt()
{
  return c_isa_main(isa_nlt_sel);
}

static int c_isa_nge()
{
  return c_isa_main(isa_nge_sel);
}

static int c_isa_ngt()
{
  return c_isa_main(isa_ngt_sel);
}

static int c_isa_neq()
{
  return c_isa_main(isa_neq_sel);
}

static int c_isa_cmp()
{
  return c_isa_main(isa_cmp_sel);
}

static int c_isa_ncmp()
{
  return c_isa_main(isa_ncmp_sel);
}



/******** C_IS_VALUE
  Return true iff argument has a value, i.e. if it is implemented in
  a quirky way in Wild_Life.  This is true for integers, reals,
  strings (which are potentially infinite sets of objects), and list objects.
*/
static int c_is_value()
{
  int success=TRUE,ans;
  ptr_psi_term arg1,arg2,funct,result;

  funct=aim->a;
  deref_ptr(funct);
  result=aim->b;
  get_two_args(funct->attr_list,&arg1,&arg2);
  if (arg1) {
    deref(arg1);
    deref_args(funct,set_1);
    ans=(arg1->value!=NULL);
    unify_bool_result(result,ans);
  }
  else curry();

  return success;
}



/******** C_IS_NUMBER
  Return true iff argument is an actual number.
*/
static int c_is_number()
{
  int success=TRUE,ans;
  ptr_psi_term arg1,arg2,funct,result;

  funct=aim->a;
  deref_ptr(funct);
  result=aim->b;
  get_two_args(funct->attr_list,&arg1,&arg2);
  if (arg1) {
    deref(arg1);
    deref_args(funct,set_1);
    ans=sub_type(arg1->type,real) && (arg1->value!=NULL);
    unify_bool_result(result,ans);
  }
  else curry();

  return success;
}


/******** C_ISA_SUBSORT(A,B)
  if A is a subsort of B => succeed and residuate on B
  else			 => fail
*/
c_isa_subsort()
{
  ptr_psi_term pred,arg1,arg2;

  pred=aim->a;
  deref_ptr(pred);
  get_two_args(pred->attr_list,&arg1,&arg2);

  if (!arg1) reportAndAbort(pred,"no first argument");
  deref(arg1);
  
  if (!arg2) reportAndAbort(pred,"no second argument");
  deref(arg2);

  deref_args(pred, set_1_2);

  if (isa(arg1, arg2))
  {
	  residuate(arg2);
	  return TRUE;
  }
  return FALSE;
}



isValue(p)
ptr_psi_term p;
{
	return (p->value != NULL);
}



/******** C_GLB(A,B)
  Return glb(A,B).  Continued calls will return each following type in
  the disjunction of the glb of A,B.
*/
c_glb()
{
  ptr_psi_term func,arg1,arg2, result, other;
  ptr_definition ans;
  ptr_int_list complexType;
  ptr_int_list decodedType = NULL;
  int ret;
  
  func=aim->a;
  deref_ptr(func);
  get_two_args(func->attr_list,&arg1,&arg2);

  if ((!arg1) || (!arg2)) {
    curry();
    return TRUE;
  }
  result = aim->b;
  deref(result);
  deref(arg1);
  deref(arg2);
  deref_args(func, set_1_2);

  if ((ret=glb(arg1->type, arg2->type, &ans, &complexType)) == 0)
    return FALSE;

  if ((ret != 4)&&(isValue(arg1)||isValue(arg2))) {
    /* glb is one of arg1->type or arg2->type AND at least one is a value */
    if (!isSubTypeValue(arg1, arg2) && !isSubTypeValue(arg2, arg1))
      return FALSE;
  }
  if (!ans) {
    decodedType = decode(complexType);
    ans = (ptr_definition)decodedType->value;
    decodedType = decodedType->next;
  }
  other=makePsiTerm(ans);

  if (isValue(arg1)) other->value=arg1->value;
  if (isValue(arg2)) other->value=arg2->value;

  /* Handle lists "correctly" */
  if (sub_type(ans,list_object) && other->value) {
    ptr_list l=(ptr_list)other->value;
    if (l->car || l->cdr) { /* non-nil list value */
      l->car=stack_psi_term(4);
      l->cdr=stack_psi_term(4);
    }
  }
    
  if (isValue(arg1) || isValue(arg2)) {
    if (decodedType) {
      Errorline("glb of multiple-inheritance value sorts not yet implemented.\n");
      return FALSE;
    }
  }
    
  if (decodedType)
    push_choice_point(type_disj, result, decodedType, NULL);

  resid_aim = NULL;
  push_goal(unify,result,other,NULL);
  return TRUE;
}



/******** C_LUB(A,B)
  Return lub(A,B).  Continued calls will return each following type in
  the disjunction of the lub of A,B.
*/
c_lub()
{
  ptr_psi_term func,arg1,arg2, result, other;
  ptr_definition ans=NULL;
  ptr_int_list complexType;
  ptr_int_list decodedType = NULL;
  
  func=aim->a;
  deref_ptr(func);
  get_two_args(func->attr_list,&arg1,&arg2);

  if ((!arg1) || (!arg2))
  {
    curry();
    return TRUE;
  }
  result = aim->b;
  deref(result);
  deref(arg1);
  deref(arg2);
  deref_args(func, set_1_2);

  /* now lets find the list of types that is the lub */
  
  decodedType = lub(arg1, arg2, &other);

  if (decodedType) {
    ans = (ptr_definition)decodedType->value;
    decodedType = decodedType->next;
    other = makePsiTerm(ans);
  }

  if (sub_type(other->type,list_object) && other->value) {
    ptr_list l=(ptr_list)other->value;
    if (l->car || l->cdr) { /* non-nil list value */
      l->car=stack_psi_term(4);
      l->cdr=stack_psi_term(4);
    }
    if (decodedType) {
      Errorline("lub of multiple-inheritance value sorts not yet implemented.\n");
      return FALSE;
    }

  }

  if (decodedType)
    push_choice_point(type_disj, result, decodedType, NULL);
    
  resid_aim = NULL;
  push_goal(unify,result,other,NULL);
  return TRUE;
}



insert_type_builtins()
{
  new_built_in("children",function,c_children);
  new_built_in("parents",function,c_parents);
  new_built_in("least_sorts",function,c_smallest);
  new_built_in(":=<",function,c_isa_le);
  new_built_in(":<",function,c_isa_lt);
  new_built_in(":>=",function,c_isa_ge);
  new_built_in(":>",function,c_isa_gt);
  new_built_in(":==",function,c_isa_eq);
  new_built_in(":><",function,c_isa_cmp);
  new_built_in(":\\=<",function,c_isa_nle);
  new_built_in(":\\<",function,c_isa_nlt);
  new_built_in(":\\>=",function,c_isa_nge);
  new_built_in(":\\>",function,c_isa_ngt);
  new_built_in(":\\==",function,c_isa_neq);
  new_built_in(":\\><",function,c_isa_ncmp);
  new_built_in("is_value",function,c_is_value);
  new_built_in("is_number",function,c_is_number);
  new_built_in("subsort",predicate,c_isa_subsort);
  new_built_in("glb",function,c_glb);
  new_built_in("lub",function,c_lub);
}
