/* Copyright 1991 Digital Equipment Corporation.
** All Rights Reserved.
*****************************************************************/

#include "extern.h"
#include "trees.h"
#include "login.h"
#include "types.h"
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

int (* c_rule[MAX_BUILT_INS])();

ptr_definition and;
ptr_definition apply;
ptr_definition boolean;
ptr_definition boolsym;
ptr_definition built_in;
ptr_definition colonsym;
ptr_definition commasym;
ptr_definition comment;
/* ptr_definition conjunction; 19.8 */
ptr_definition constant;
ptr_definition cut;
ptr_definition disjunction;
ptr_definition eof;
ptr_definition eqsym;
ptr_definition false;
ptr_definition funcsym;
ptr_definition functor;
ptr_definition iff;
ptr_definition integer;
ptr_definition alist;
ptr_definition list_object;
ptr_definition nothing;
ptr_definition predsym;
ptr_definition quote;
ptr_definition quoted_string;
ptr_definition real;
ptr_definition stream;
ptr_definition succeed;
ptr_definition such_that;
ptr_definition top;
ptr_definition true;
ptr_definition timesym;
ptr_definition typesym;
ptr_definition variable;
ptr_definition opsym;
ptr_definition loadsym;
ptr_definition dynamicsym;
ptr_definition staticsym;
ptr_definition encodesym;
ptr_definition listingsym;
ptr_definition provesym;
ptr_definition delay_checksym;
ptr_definition eval_argsym;
ptr_definition inputfilesym;
ptr_definition call_handlersym;
ptr_definition xf_sym;
ptr_definition fx_sym;
ptr_definition yf_sym;
ptr_definition fy_sym;
ptr_definition xfx_sym;
ptr_definition xfy_sym;
ptr_definition yfx_sym;
ptr_definition nullsym;

ptr_psi_term null_psi_term;

char *one;
char *two;
char *year_attr;
char *month_attr;
char *day_attr;
char *hour_attr;
char *minute_attr;
char *second_attr;
char *weekday_attr;

static int built_in_index=0;




/********* PSI_TO_STRING(t,fn)
  Get the value of a Life string, or the name of a non-string psi-term.
  Return TRUE iff a valid string is found.
*/
int psi_to_string(t, fn)
ptr_psi_term t;
char **fn;
{
  if (equal_types(t->type,quoted_string)) {
    if (t->value) {
      *fn = (char *) t->value;
      return TRUE;
    }
    else {
      *fn = quoted_string->symbol;
      return TRUE;
    }
  }
  else {
    *fn = t->type->symbol;
    return TRUE;
  }
}



/******** MAKE_LIST(n)
  This constructs a list of feature names
  from the attribute tree N.
  This is used in the built-in features(T).
*/

static void make_list2(); /* Forward declaration */

static void make_list(st, head)
ptr_node st;
ptr_psi_term *head;
{
  ptr_psi_term t, *tail;

  make_list2(st,&t,&tail);
  *tail=NULL;

  if (t) {
    *head=t;
  }
  else {
    /* Insert dummy psi-term for empty list: */
    ptr_list l;

    l=STACK_ALLOC(list);
    l->car=NULL;
    l->cdr=NULL;

    *head=stack_psi_term(4);
    (*head)->type=alist;
    (*head)->value=(GENERIC)l;
  }
}

static void make_list2(st, head, tail)
ptr_node st;
ptr_psi_term *head;
ptr_psi_term **tail;
{
  ptr_psi_term *mid1, *mid2, t;
  ptr_list l;
  ptr_definition def;
  double d, strtod();
  
  if (st==NULL) {
    *tail = head;
  }
  else {
    char *eptr;
    /* Concatenate the lists of the two subtrees */
    make_list2(st->left, head, &mid1);

    /* Insert the feature name into the list */
    t=stack_psi_term(4);
    d=str_to_int(st->key);
    /* d=strtod(st->key,&eptr); 6.10 */
    if (d== -1 /* 6.10 *eptr */) { /* Feature is not a number */
      def=update_symbol(st->key);
      t->type=def;
    }
    else { /* Feature is a number */
      t->type=(d==floor(d))?integer:real;
      t->value=heap_alloc(sizeof(REAL)); /* 12.5 */
      *(REAL *)t->value=(REAL)d;
    }

    l=STACK_ALLOC(list);
    l->car=t;
    mid2 = &(l->cdr);

    *mid1 = stack_psi_term(4);
    (*mid1)->type=alist;
    (*mid1)->value=(GENERIC)l;

    make_list2(st->right, mid2, tail);
  }
}



/******** CHECK_REAL(t,v,n)
  Like get_real_value, but does not force the type of T to be real.
*/
int check_real(t,v,n)
ptr_psi_term t;
REAL *v;
int *n;
{
  int success=FALSE;
  int smaller;

  if (t) {
    success=matches(t->type,real,&smaller);
    if (success) {
      *n=FALSE;
      if (smaller && t->value) {
        *v= *(REAL *)t->value;
        *n=TRUE;
      }
    }
  }
  return success;
}



/******** GET_REAL_VALUE(t,v,n)
  Check if psi_term T is a real number.  Return N=TRUE iff T <| REAL.
  If T has a real value then set V to that value.
  Also force the type of T to REAL if REAL <| T.
  This is used in all the arithmetic built-in functions to get their arguments.
*/
int get_real_value(t,v,n)
ptr_psi_term t;
REAL *v;
int *n;
{
  int success=FALSE;
  int smaller;
  
  if (t) {
    success=matches(t->type,real,&smaller);
    if (success) {
      *n=FALSE;
      if (smaller) {
	if (t->value) {
	  *v= *(REAL *)t->value;
	  *n=TRUE;
	}
      }
      else {
	push_ptr_value(def_ptr,&(t->type));
	push_ptr_value(int_ptr,&(t->status));
	t->type=real;
	t->status=0;
	i_check_out(t);
      }      
    }
  }
  return success;
}



/******** GET_BOOL_VALUE(t,v,n)
  This is identical in nature to
  GET_REAL_VALUE. The values handled here have to be booleans.
  Check if psi_term T is a boolean. V <- TRUE or FALSE value of T.
*/
static int get_bool_value(t,v,n)
ptr_psi_term t;
REAL *v;
int *n;
{
  int success=FALSE;
  int smaller;
  
  
  if(t) {
    success=matches(t->type,boolean,&smaller);
    if(success) {
      *n=FALSE;
      if(smaller) {
	if(matches(t->type,false,&smaller) && smaller) {
	  *v= 0;
	  *n=TRUE;
	}
	else
	  if(matches(t->type,true,&smaller) && smaller) {
	    *v= 1;
	    *n=TRUE;
	  }
      }
      else {
	push_ptr_value(def_ptr,&(t->type));
	push_ptr_value(int_ptr,&(t->status));
	t->type=boolean;
	t->status=0;
	i_check_out(t);
      }      
    }
  }
  
  return success;
}



/******** UNIFY_BOOL_RESULT(t,v)
  Unify psi_term T to the boolean value V = TRUE or FALSE.
  This is used by built-in logical functions to return their result.
*/
void unify_bool_result(t,v)
ptr_psi_term t;
int v;
{
  push_ptr_value(def_ptr,&(t->type));
  if (v) {
    t->type=true;
    t->status=0;
  }
  else {
    t->type=false;
    t->status=0;
  }
  
  i_check_out(t);
  if (t->resid)
    release_resid(t);
}




/******** UNIFY_REAL_RESULT(t,v)
  Unify psi_term T to the real value V.
  This is used by built-in arithmetic functions to return their result.
*/
int unify_real_result(t,v)
ptr_psi_term t;
REAL v;
{
  int smaller;
  int success=TRUE;

#ifdef prlDEBUG
  if (t->value) {
    printf("*** BUG: value already present in UNIFY_REAL_RESULT\n");
  }
#endif

  deref_ptr(t);
  assert(t->value==NULL); /* 10.6 */
  push_ptr_value(int_ptr,&(t->value));
  t->value=heap_alloc(sizeof(REAL)); /* 12.5 */
  *(REAL *)t->value = v;
  
  matches(t->type,integer,&smaller);
  
  if (v==floor(v)){
    if (!smaller) {
      push_ptr_value(def_ptr,&(t->type));
      t->type=integer;
      t->status=0;
    }
  }
  else
    if (smaller)
      success=FALSE;
  
  if (success) {
    i_check_out(t);
    if (t->resid)
      release_resid(t);
  }
  
  return success;
}



/******** C_GT
  Greater than.
*/
static int c_gt()
{
  int success=TRUE;
  ptr_psi_term arg1,arg2,arg3,t;
  int num1,num2,num3;
  REAL val1,val2,val3;
  
  t=aim->a;
  deref_ptr(t);
  get_two_args(t->attr_list,&arg1,&arg2);
  arg3=aim->b;
  
  if (arg1) {
    deref(arg1);
    success=get_real_value(arg1,&val1,&num1);
    if(success && arg2) {
      deref(arg2);
      deref_args(t,set_1_2);
      success=get_real_value(arg2,&val2,&num2);
    }
  }
  
  if(success)
    if(arg1 && arg2) {
      deref(arg3);
      success=get_bool_value(arg3,&val3,&num3);
      if(success)
	switch(num1+num2*2+num3*4) {
	case 0:
	  residuate2(arg1,arg2);
	  break;
	case 1:
	  residuate(arg2);
	  break;
	case 2:
	  residuate(arg1);
	  break;
	case 3:
	  unify_bool_result(arg3,(val1>val2));
	  break;
	case 4:
	  residuate2(arg1,arg2);
	  break;
	case 5:
	  residuate(arg2);
	  break;
	case 6:
	  residuate(arg1);
	  break;
	case 7:
	  success=(val3==(REAL)(val1>val2));
	  break;
	} 
    }
    else
      curry();
  
  nonnum_warning(t,arg1,arg2);
  return success;
}



/******** C_EQUAL
  Arithmetic equality.
*/
static int c_equal()
{
  int success=TRUE;
  ptr_psi_term arg1,arg2,arg3,t;
  int num1,num2,num3;
  REAL val1,val2,val3;
  
  t=aim->a;
  deref_ptr(t);
  get_two_args(t->attr_list,&arg1,&arg2);
  arg3=aim->b;
  
  if(arg1) {
    deref(arg1);
    success=get_real_value(arg1,&val1,&num1);
    if(success && arg2) {
      deref(arg2);
      deref_args(t,set_1_2);
      success=get_real_value(arg2,&val2,&num2);
    }
  }
  
  if(success)
    if(arg1 && arg2) {
      deref(arg3);
      success=get_bool_value(arg3,&val3,&num3);
      if(success)
	switch(num1+2*num2+4*num3) {
	case 0:
	  if(arg1==arg2)
	    unify_bool_result(arg3,(REAL)1);
	  else
	    residuate2(arg1,arg2);
	  break;
	case 1:
	  residuate2(arg2,arg3);
	  break;
	case 2:
	  residuate2(arg1,arg3);
	  break;
	case 3:
	  unify_bool_result(arg3,(val1==val2));
	  break;
	case 4:
	  if(arg1==arg2 && !val3)
	    success=FALSE;
	  else
	    residuate2(arg1,arg2);
	  break;
	case 5:
	  if(!val3)
	    residuate(arg2);
	  else
	    success=unify_real_result(arg2,val1);
	  break;
	case 6:
	  if(!val3)
	    residuate(arg1);
	  else
	    success=unify_real_result(arg1,val2);
	  break;
	case 7:
	  success=(val3==(REAL)(val1==val2));
	  break;
	}
    }
    else
      curry();
  
  nonnum_warning(t,arg1,arg2);
  return success;
}



/******** C_LT
  Less than.
*/
static int c_lt()
{
  int success=TRUE;
  ptr_psi_term arg1,arg2,arg3,t;
  int num1,num2,num3;
  REAL val1,val2,val3;
  
  t=aim->a;
  deref_ptr(t);
  get_two_args(t->attr_list,&arg1,&arg2);
  arg3=aim->b;
  
  if(arg1) {
    deref(arg1);
    success=get_real_value(arg1,&val1,&num1);
    if(success && arg2) {
      deref(arg2);
      deref_args(t,set_1_2);
      success=get_real_value(arg2,&val2,&num2);
    }
  }
  
  if(success)
    if(arg1 && arg2) {
      deref(arg3);
      success=get_bool_value(arg3,&val3,&num3);
      if(success)
	switch(num1+num2*2+num3*4) {
	case 0:
	  residuate2(arg1,arg2);
	  break;
	case 1:
	  residuate(arg2);
	  break;
	case 2:
	  residuate(arg1);
	  break;
	case 3:
	  unify_bool_result(arg3,(val1<val2));
	  break;
	case 4:
	  residuate2(arg1,arg2);
	  break;
	case 5:
	  residuate(arg2);
	  break;
	case 6:
	  residuate(arg1);
	  break;
	case 7:
	  success=(val3==(REAL)(val1<val2));
	  break;
	}
    }
    else
      curry();
  
  nonnum_warning(t,arg1,arg2);
  return success;
}




/******** C_GTOE
  Greater than or equal.
*/
static int c_gtoe()
{
  int success=TRUE;
  ptr_psi_term arg1,arg2,arg3,t;
  int num1,num2,num3;
  REAL val1,val2,val3;
  
  t=aim->a;
  deref_ptr(t);
  get_two_args(t->attr_list,&arg1,&arg2);
  arg3=aim->b;
  
  if(arg1) {
    deref(arg1);
    success=get_real_value(arg1,&val1,&num1);
    if(success && arg2) {
      deref(arg2);
      deref_args(t,set_1_2);
      success=get_real_value(arg2,&val2,&num2);
    }
  }
  
  if(success)
    if(arg1 && arg2) {
      deref(arg3);
      success=get_bool_value(arg3,&val3,&num3);
      if(success)
	switch(num1+num2*2+num3*4) {
	case 0:
	  residuate2(arg1,arg2);
	  break;
	case 1:
	  residuate(arg2);
	  break;
	case 2:
	  residuate(arg1);
	  break;
	case 3:
	  unify_bool_result(arg3,(val1>=val2));
	  break;
	case 4:
	  residuate2(arg1,arg2);
	  break;
	case 5:
	  residuate(arg2);
	  break;
	case 6:
	  residuate(arg1);
	  break;
	case 7:
	  success=(val3==(REAL)(val1>=val2));
	  break;
	}      
    }
    else
      curry();
  
  nonnum_warning(t,arg1,arg2);
  return success;
}



/******** C_LTOE
  Less than or equal.
*/
static int c_ltoe()
{
  int success=TRUE;
  ptr_psi_term arg1,arg2,arg3,t;
  int num1,num2,num3;
  REAL val1,val2,val3;
  
  t=aim->a;
  deref_ptr(t);
  get_two_args(t->attr_list,&arg1,&arg2);
  arg3=aim->b;
  
  if(arg1) {
    deref(arg1);
    success=get_real_value(arg1,&val1,&num1);
    if(success && arg2) {
      deref(arg2);
      deref_args(t,set_1_2);
      success=get_real_value(arg2,&val2,&num2);
    }
  }
  
  if(success)
    if(arg1 && arg2) {
      deref(arg3);
      success=get_bool_value(arg3,&val3,&num3);
      if(success)
	switch(num1+num2*2+num3*4) {
	case 0:
	  residuate2(arg1,arg2);
	  break;
	case 1:
	  residuate(arg2);
	  break;
	case 2:
	  residuate(arg1);
	  break;
	case 3:
	  unify_bool_result(arg3,(val1<=val2));
	  break;
	case 4:
	  residuate2(arg1,arg2);
	  break;
	case 5:
	  residuate(arg2);
	  break;
	case 6:
	  residuate(arg1);
	  break;
	case 7:
	  success=(val3==(REAL)(val1<=val2));
	  break;
	}
    }
    else
      curry();
  
  nonnum_warning(t,arg1,arg2);
  return success;
}




/******** C_BOOLPRED
  Internal built-in predicate that handles functions in predicate positions.
  This predicate should never be called directly by the user.
*/
static int c_boolpred()
{
  int success=TRUE,succ,lesseq;
  ptr_psi_term t,arg1;

  t=aim->a;
  deref_ptr(t);
  get_one_arg(t->attr_list,&arg1);
  if (arg1) {
    deref(arg1);
    deref_args(t,set_1);
    succ=matches(arg1->type,true,&lesseq);
    if (succ) {
      if (lesseq) {
        /* Function returns true: success. */
      }
      else
        residuate(arg1);
    }
    else {
      succ=matches(arg1->type,false,&lesseq);
      if (succ) {
        if (lesseq) {
          /* Function returns false: failure. */
          success=FALSE;
        }
        else
          residuate(arg1);
      }
      else {
        /* Both true and false are disentailed. */
        if (arg1->type->type==predicate) {
          push_goal(prove,arg1,DEFRULES,NULL);
        }
        else {
          Errorline("function result '%P' should be\
 a boolean or a predicate.\n", arg1);
          return (c_abort());
        }
      }
    }
  }
  else {
    Errorline("missing argument to '*boolpred*'.\n");
    return (c_abort());
  }

  return success;
}



/* Main routine to handle the and & or functions. */
static int c_logical_main(sel,typ)
int sel;
ptr_definition typ;
{
  int success=TRUE,succ1,succ2;
  ptr_psi_term funct,arg1,arg2,result;
  int sm1,sm2;

  funct=aim->a;
  deref_ptr(funct);
  get_two_args(funct->attr_list,&arg1,&arg2);
  if (arg1 && arg2) {
    deref(arg1);
    deref(arg2);
    deref_args(funct,set_1_2);
    result=aim->b;
    deref(result);
    succ1=matches(arg1->type,typ,&sm1);
    succ2=matches(arg2->type,typ,&sm2);
    if (succ1 && succ2) {
      if (sm1 && sm2) {
        unify_bool_result(result,sel);
      }   
      else {
        if (!sm1) residuate(arg1);
        if (!sm2) residuate(arg2);
      }
    }
    else
      unify_bool_result(result,!sel);
  }
  else
    curry();

  return success;
}




/******** C_AND, C_OR
  Logical and & or.
  These functions execute as if defined by:

    and(true,true) -> true.
    and(_,_) -> false.
 
    or(false,false) -> false.
    or(_,_) -> true.
*/
static int c_and()
{
  return c_logical_main(TRUE,true);
}

static int c_or()
{
  return c_logical_main(FALSE,false);
}




/******** C_APPLY
  This evaluates "'*apply*'('*functor*' => F,Args)".  If F is
  a known function, then it builds the psi-term F(Args), and evaluates it.
*/
static int c_apply()
{
  int success=TRUE;
  ptr_psi_term funct,other;
  ptr_node n,fattr;
  
  funct=aim->a;
  deref_ptr(funct);
  n=find(featcmp,functor->symbol,funct->attr_list);
  if (n) {
    other=(ptr_psi_term )n->data;
    deref(other);
    if (other->type==top)
      residuate(other);
    else
      if(other->type && other->type->type!=function) {
	success=FALSE;
        Errorline("argument %P is not a function in '*apply*'.\n",other);
      }
      else {
        /* What we really want here is to merge all attributes in       */
        /* funct->attr_list, except '*functor*', into other->attr_list. */
	clear_copy();
	other=distinct_copy(other);
        fattr=distinct_tree(funct->attr_list); /* Make distinct copy: PVR */
	push_goal(eval,other,aim->b,other->type->rule);
	merge_unify(&(other->attr_list),fattr);
        /* We don't want to remove anything from funct->attr_list here. */
	delete_attr(functor->symbol,&(other->attr_list));
      }
  }
  else
    curry();
  
  return success;
}




/******** C_PROJECT
  Here we evaluate "project(Label,Psi-term)". This
  returns the psi-term associated to label Label in Psi-term.
*/
static int c_project()
{
  int success=TRUE,v;
  ptr_psi_term arg1,arg2,funct,result;
  ptr_node n;
  char *label;
  /* char *buffer="integer"; 18.5 */
  char buffer[20]; /* Maximum number of digits in an integer */
  
  funct=aim->a;
  deref_ptr(funct);
  result=aim->b;
  get_two_args(funct->attr_list,&arg1,&arg2);
  if (arg1 && arg2) {
    deref(arg1);
    deref(arg2);
    deref_args(funct,set_1_2);
    label=NULL;
    if (overlap_type(arg1->type,quoted_string)) /* 10.8 */
      label=(char *)arg1->value;
    else
      if (overlap_type(arg1->type,integer) && arg1->value) { /* 10.8 */
	v= *(REAL *)arg1->value;
	/* sprintf(buffer,"%d%c",v,0); */
	sprintf(buffer,"%d",v);
	label=heap_copy_string(buffer); /* A little voracious */
      }
      else
	label=arg1->type->symbol;

    if (label) {
      n=find(featcmp,label,arg2->attr_list);
      if (n)
	push_goal(unify,result,n->data,NULL);
      else {
	bk_stack_insert(featcmp,label,&(arg2->attr_list),result);
	if (result->resid)
	  release_resid(result);
      }	
    }
    else
      residuate(arg1);
  }
  else
    curry();
  
  return success;
}




/******** C_DIFF
  Arithmetic not-equal.
*/
static int c_diff()
{
  int success=TRUE;
  ptr_psi_term arg1,arg2,arg3,t;
  int num1,num2,num3;
  REAL val1,val2,val3;
  
  t=aim->a;
  deref_ptr(t);
  get_two_args(t->attr_list,&arg1,&arg2);
  arg3=aim->b;
  
  if(arg1) {
    deref(arg1);
    success=get_real_value(arg1,&val1,&num1);
    if(success && arg2) {
      deref(arg2);
      deref_args(t,set_1_2);
      success=get_real_value(arg2,&val2,&num2);
    }
  }
  
  if(success)
    if(arg1 && arg2) {
      deref(arg3);
      success=get_bool_value(arg3,&val3,&num3);
      if(success)
	switch(num1+2*num2+4*num3) {
	case 0:
	  if(arg1==arg2)
	    unify_bool_result(arg3,(REAL)0);
	  else
	    residuate2(arg1,arg2);
	  break;
	case 1:
	  residuate2(arg2,arg3);
	  break;
	case 2:
	  residuate2(arg1,arg3);
	  break;
	case 3:
	  unify_bool_result(arg3,(val1!=val2));
	  break;
	case 4:
	  if(arg1==arg2 && val3)
	    success=FALSE;
	  else
	    residuate2(arg1,arg2);
	  break;
	case 5:
	  if(val3)
	    residuate(arg2);
	  else
	    success=unify_real_result(arg2,val1);
	  break;
	case 6:
	  if(val3)
	    residuate(arg1);
	  else
	    success=unify_real_result(arg1,val2);
	  break;
	case 7:
	  success=(val3==(REAL)(val1!=val2));
	  break;
	}
    }
    else
      curry();
  
  nonnum_warning(t,arg1,arg2);
  return success;
}




/******** C_FAIL
  Always fail.
*/
static int c_fail()
{
  return FALSE;
}



/******** C_SUCCEED
  Always succeed.
*/
static int c_succeed()
{
  ptr_psi_term t;

  t=aim->a;
  deref_args(t,set_empty);
  return TRUE;
}



/******** C_REPEAT
  Succeed indefinitely on backtracking.
*/
static int c_repeat()
{
  ptr_psi_term t;

  t=aim->a;
  deref_args(t,set_empty);
  push_choice_point(prove,t,DEFRULES,NULL);
  return TRUE;
}


/******** C_VAR
  Succeed iff argument is '@' (top with no attributes).
*/
static int c_var()
{
  ptr_psi_term arg1,arg2,t;
  
  t=aim->a;
  deref_ptr(t);
  get_two_args(t->attr_list,&arg1,&arg2);
  if (arg1) {
    deref(arg1);
    deref_args(t,set_1);
    return ((arg1->type==top) && (arg1->attr_list==NULL));
  }
  else {
    Errorline("argument missing in %P.\n",t);
    return c_abort();
  }
}


/******** C_NONVAR
  Succeed iff argument is not '@' (top with no attributes).
*/
static int c_nonvar()
{
  ptr_psi_term arg1,arg2,t;
  
  t=aim->a;
  deref_ptr(t);
  get_two_args(t->attr_list,&arg1,&arg2);
  if (arg1) {
    deref(arg1);
    deref_args(t,set_1);
    return (!((arg1->type==top) && (arg1->attr_list==NULL)));
  }
  else {
    Errorline("argument missing in %P.\n",t);
    return c_abort();
  }
}


/******** C_IS_FUNCTION
  Succeed iff argument is a function (built-in or user-defined).
*/
static int c_is_function()
{
  ptr_psi_term arg1,arg2,t;
  
  t=aim->a;
  deref_ptr(t);
  get_two_args(t->attr_list,&arg1,&arg2);
  if (arg1) {
    deref_ptr(arg1); /* 18.6 */
    deref_args(t,set_1);
    return (arg1->type->type==function);
  }
  else {
    Errorline("argument missing in %P.\n",t);
    return c_abort();
  }
}


/******** C_IS_PREDICATE
  Succeed iff argument is a predicate (built-in or user-defined).
*/
static int c_is_predicate()
{
  ptr_psi_term arg1,arg2,t;
  
  t=aim->a;
  deref_ptr(t);
  get_two_args(t->attr_list,&arg1,&arg2);
  if (arg1) {
    deref(arg1);
    deref_args(t,set_1);
    return (arg1->type->type==predicate);
  }
  else {
    Errorline("argument missing in %P.\n",t);
    return c_abort();
  }
}


/******** C_IS_SORT
  Succeed iff argument is a sort (built-in or user-defined).
*/
static int c_is_sort()
{
  ptr_psi_term arg1,arg2,t;
  
  t=aim->a;
  deref_ptr(t);
  get_two_args(t->attr_list,&arg1,&arg2);
  if (arg1) {
    deref(arg1);
    deref_args(t,set_1);
    return (arg1->type->type==type);
  }
  else {
    Errorline("argument missing in %P.\n",t);
    return c_abort();
  }
}



/* Return TRUE iff t has only argument "1", and return the argument. */
int only_arg1(t, arg1)
ptr_psi_term t;
ptr_psi_term *arg1;
{
  ptr_node n=t->attr_list;

  if (n && n->left==NULL && n->right==NULL && !featcmp(n->key,one)) {
    *arg1=(ptr_psi_term)n->data;
    return TRUE;
  }
  else
    return FALSE;
}



/******** C_DYNAMIC()
  Mark all the arguments as 'unprotected', i.e. they may be changed
  by assert/retract/redefinition.
*/
static int c_dynamic()
{
  ptr_psi_term t=aim->a;
  deref_ptr(t);
  /* mark_quote(t); 14.9 */
  assert_protected(t->attr_list,FALSE);
  return TRUE;
}



/******** C_STATIC()
  Mark all the arguments as 'protected', i.e. they may not be changed
  by assert/retract/redefinition.
*/
static int c_static()
{
  ptr_psi_term t=aim->a;
  deref_ptr(t);
  /* mark_quote(t); 14.9 */
  assert_protected(t->attr_list,TRUE);
  return TRUE;
}



/******** C_DELAY_CHECK()
  Mark that the properties of the types in the arguments are delay checked
  during unification (i.e. they are only checked when the psi-term is
  given attributes, and they are not checked as long as the psi-term has
  no attributes.)
*/
static int c_delay_check()
{
  ptr_psi_term t=aim->a;

  deref_ptr(t);
  /* mark_quote(t); 14.9 */
  assert_delay_check(t->attr_list);
  inherit_always_check();
  return TRUE;
}



/******** C_NON_STRICT()
  Mark that the function or predicate's arguments are not evaluated when
  the function or predicate is called.
*/
static int c_non_strict()
{
  ptr_psi_term t=aim->a;

  deref_ptr(t);
  /* mark_quote(t); 14.9 */
  assert_args_not_eval(t->attr_list);
  return TRUE;
}



/******** C_OP()
  Declare an operator.
*/
static int c_op()
{
  int declare_operator();
  ptr_psi_term t=aim->a;

  return declare_operator(t);
}



int file_exists(s)
char *s;
{
  FILE *f;
  char *e;
  int success=FALSE;
  
  e=expand_file_name(s);
  if (f=fopen(e,"r")) {
    fclose(f);
    success=TRUE;
  }
  return success;
}



/******** C_EXISTS
  Succeed iff a file can be read in (i.e. if it exists).
*/
static int c_exists()
{
  ptr_psi_term g;
  ptr_node n;
  int success=TRUE;
  ptr_psi_term arg1; 
  char *c_arg1; 

  g=aim->a;
  deref_ptr(g);

  if (success) {
    n=find(featcmp,one,g->attr_list);
    if (n) {
      arg1= (ptr_psi_term )n->data;
      deref(arg1);
      deref_args(g,set_1);
      if (!psi_to_string(arg1,&c_arg1)) {
        success=FALSE;
        Errorline("bad argument in %P.\n",g);
      }
    }
    else {
      success=FALSE;
      Errorline("bad argument in %P.\n",g);
    }
  }

  if (success)
    success=file_exists(c_arg1);

  return success;
}



/******** C_LOAD
  Load a file.  This load accepts and executes any queries in the loaded
  file, including calls to user-defined predicates and other load predicates.
*/
static int c_load()
{
  int success=FALSE;
  ptr_psi_term arg1,arg2,t;
  ptr_goal top_goal,new,curr;
  ptr_definition fnsym;
  char *fn;

  t=aim->a;
  deref_ptr(t);
  get_two_args(t->attr_list,&arg1,&arg2);
  if(arg1) {
    deref(arg1);
    deref_args(t,set_1);
    if (psi_to_string(arg1,&fn)) {
      success=open_input_file(fn);
      if (success) {
        fnsym=update_symbol(fn);
        /* The load goal does all the work: */
        if (!fnsym->already_loaded) {
          file_date+=2;
          fnsym->already_loaded=TRUE;
          push_goal(load,input_state,file_date,fn);
          file_date+=2;
        }
        open_input_file("stdin");
      }
    }
    else {
      Errorline("bad file name in %P.\n",t);
      success=FALSE;
    }
  }
  else {
    Errorline("no file name in %P.\n",t);
    success=FALSE;
  }

  return success;
}



/******** C_GET_CHOICE()
  Return the current state of the choice point stack (i.e., the time stamp
  of the current choice point).
*/
static int c_get_choice()
{
  int gts,success=TRUE;
  ptr_psi_term funct,result,gts_term;

  funct=aim->a;
  deref_ptr(funct);
  result=aim->b;
  deref_args(funct,set_empty);
  if (choice_stack)
    gts=choice_stack->time_stamp;
  else
    gts=INIT_TIME_STAMP;
  push_goal(unify,result,real_stack_psi_term(4,(REAL)gts),NULL);

  return success;
}



/******** C_SET_CHOICE()
  Set the choice point stack to a state no later than (i.e. the same or earlier
  than) the state of the first argument (i.e., remove all choice points up to
  the first one whose time stamp is =< the first argument).  This predicate
  will remove zero or more choice points, never add them.  The first argument
  must come from a past call to get_choice.
  Together, get_choice and set_choice allow one to implement an "ancestor cut"
  that removes all choice points created between the current execution point
  and an execution point arbitarily remote in the past.
  The built-ins get_choice, set_choice, and exists_choice are implemented
  using the timestamping mechanism in the interpreter.  The two
  relevant properties of the timestamping mechanism are that each choice
  point is identified by an integer and that the integers are in increasing
  order (but not necessarily consecutive) from the bottom to the top of the
  choice point stack.
*/
static int c_set_choice()
{
  REAL gts_r;
  int gts,cut_gts;
  int num,success=TRUE;
  ptr_psi_term t,arg1;
  ptr_choice_point cutpt;

  t=aim->a;
  deref_ptr(t);
  get_one_arg(t->attr_list,&arg1);
  if (arg1) {
    deref(arg1);
    deref_args(t,set_1);
    success = get_real_value(arg1,&gts_r,&num);
    if (success) {
      if (num) {
        gts=(int)gts_r;
        if (choice_stack) {
          cutpt=choice_stack;
          while (cutpt && cutpt->time_stamp>gts) cutpt=cutpt->next;
          if (choice_stack!=cutpt) {
            choice_stack=cutpt;
#ifdef CLEAN_TRAIL
            clean_trail(choice_stack);
#endif
          }
        }
      }
      else {
        Errorline("bad argument to %P.\n",t);
	success=FALSE;
      }
    }
    else {
      Errorline("bad argument %P.\n",t);
      success=FALSE;
    }
  }
  else
    curry();

  return success;
}



/******** C_EXISTS_CHOICE()
  Return true iff there exists a choice point A such that arg1 < A <= arg2,
  i.e. A is more recent than the choice point marked by arg1 and no more
  recent than the choice point marked by arg2.  The two arguments to
  exists_choice must come from past calls to get_choice.
  This function allows one to check whether a choice point exists between
  any two arbitrary execution points of the program.
*/
static int c_exists_choice()
{
  REAL gts_r;
  int ans,gts1,gts2,num,success=TRUE;
  ptr_psi_term funct,result,arg1,arg2,ans_term;
  ptr_choice_point cp;

  funct=aim->a;
  deref_ptr(funct);
  result=aim->b;
  deref_args(funct,set_empty);
  get_two_args(funct->attr_list,&arg1,&arg2);
  if (arg1 && arg2) {
    deref(arg1);
    deref(arg2);
    deref_args(funct,set_1_2);
    success = get_real_value(arg1,&gts_r,&num);
    if (success && num) {
      gts1 = (int) gts_r;
      success = get_real_value(arg2,&gts_r,&num);
      if (success && num) {
        gts2 = (int) gts_r;
        cp = choice_stack;
        if (cp) {
          while (cp && cp->time_stamp>gts2) cp=cp->next;
          ans=(cp && cp->time_stamp>gts1);
        }
        else
          ans=FALSE;
        ans_term=stack_psi_term(4);
        ans_term->type=ans?true:false;
        push_goal(unify,result,ans_term,NULL);
      }
      else {
        Errorline("bad second argument to %P.\n",funct);
        success=FALSE;
      }
    }
    else {
      Errorline("bad first argument %P.\n",funct);
      success=FALSE;
    }
  }
  else
    curry();

  return success;
}



/******** C_PRINT_VARIABLES
  Print the global variables and their values,
  in the same way as is done in the user interface.
*/
static int c_print_variables()
{
  int success=TRUE;

  print_variables();

  return success;
}



static void set_parse_queryflag(alist, sort)
ptr_node alist;
int sort;
{
  ptr_node n;             /* node pointing to argument 2  */
  ptr_psi_term arg;       /* argumenrt 2 psi-term */
  ptr_psi_term queryflag; /* query term created by this function */

  n=find(featcmp,two,alist);
  if (n) {
    /* there was a second argument */
    arg=(ptr_psi_term)n->data;
    queryflag=stack_psi_term(4);
    queryflag->type =
    update_symbol(((sort==QUERY)?"query":
                  ((sort==FACT)?"declaration":"error")));
    push_goal(unify,queryflag,arg,NULL);
  }
}


/******** C_PARSE
  Parse a string and return a quoted psi-term.
  The global variable names are recognized (see the built-in
  print_variables).  All variables in the parsed string
  are added to the set of global variables.
*/
static int c_parse()
{
  int success=TRUE;
  ptr_psi_term arg1,arg2,arg3,funct,result;
  int smaller,sort,old_var_occurred;
  ptr_node n;
  parse_block pb;

  funct=aim->a;
  deref_ptr(funct);
  result=aim->b;
  get_one_arg(funct->attr_list,&arg1);
  if (arg1) {
    deref(arg1);
    deref_args(funct,set_1);
    success=matches(arg1->type,quoted_string,&smaller);
    if (success) {
      if (arg1->value) {
        ptr_psi_term t;

        /* Parse the string in its own state */
        save_parse_state(&pb);
        init_parse_state();
        stringparse=TRUE;
        stringinput=(char*)arg1->value;

        old_var_occurred=var_occurred;
        var_occurred=FALSE;
        t=stack_copy_psi_term(parse(&sort));
        
          /* Optional second argument returns 'query', 'declaration', or
          /* 'error'. */
          n=find(featcmp,two,funct->attr_list);
   	  if (n) {
            ptr_psi_term queryflag;
            arg2=(ptr_psi_term)n->data;
            queryflag=stack_psi_term(4);
            queryflag->type=
              update_symbol(
                ((sort==QUERY)?"query":((sort==FACT)?"declaration":"error"))
              );
            push_goal(unify,queryflag,arg2,NULL);
          }
  
          /* Optional third argument returns true or false if the psi-term
          /* contains a variable or not. */
          n=find(featcmp,"3",funct->attr_list);
          if (n) {
            ptr_psi_term varflag;
            arg3=(ptr_psi_term)n->data;
            varflag=stack_psi_term(4);
            varflag->type=var_occurred?true:false;
            push_goal(unify,varflag,arg3,NULL);
          }

        var_occurred = var_occurred || old_var_occurred;
        stringparse=FALSE;
        restore_parse_state(&pb);

        /* parse_ok flag says whether there was a syntax error. */
        if (TRUE /*parse_ok*/) {
          mark_quote(t);
          push_goal(unify,t,result,NULL);
        }
        else
          success=FALSE;
      }
      else
        residuate(arg1);
    }
    else
      success=FALSE;
  }
  else
   curry();

  return success;
}





/******** C_READ
  Read a psi_term or a token from the current input stream.
  The variables in the object read are not added to the set
  of global variables.
*/

static int c_read_psi() { return (c_read(TRUE)); }

static int c_read_token() { return (c_read(FALSE)); }

static int c_read(psi_flag)
int psi_flag;
{
  int success=TRUE;
  int sort,quot;
  ptr_psi_term arg1,g,t;
  ptr_node old_var_tree;
  
  g=aim->a;
  deref_ptr(g);
  get_one_arg(g->attr_list,&arg1);
  if (arg1) {
    deref_args(g,set_1);
    if (eof_flag) {
      Errorline("attempt to read past end of file (%E).\n");
      return (abort_life(TRUE));
    }
    else {
      prompt="";
      old_var_tree=var_tree;
      var_tree=NULL;
      if (psi_flag) {
        t=stack_copy_psi_term(parse(&sort));
      }
      else {
        t=stack_psi_term(0);
        read_token_b(t,&quot);
      }
      if (t->type==eof) eof_flag=TRUE;
      var_tree=old_var_tree;
    }
    
    if (success) {
      mark_quote(t);
      push_goal(unify,t,arg1,NULL);
      /* i_check_out(t); */
    }
  }
  else {
    Errorline("argument missing in %P.\n",g);
    success=FALSE;
  }
  
  return success;
}



/******** C_HALT
  Exit the Wild_Life interpreter.
*/
void c_halt()
{
  exit_life(TRUE);
}


void exit_life(nl_flag)
int nl_flag;
{
  open_input_file("stdin");
  times(&life_end);
  if (nl_flag) printf("\n");
  printf("*** Exiting Wild_Life  ");
  printf("[%1.3fs cpu, %1.3fs gc (%2.1f%%)]\n",
         (life_end.tms_utime-life_start.tms_utime)/60.0,
         garbage_time,
         garbage_time*100 / ((life_end.tms_utime-life_start.tms_utime)/60.0)
        );
  exit(1);
}



/******** C_ABORT
  Return to the top level of the interpreter.
*/
int c_abort()
{
  return (abort_life(TRUE));
}


int abort_life(nlflag)
int nlflag;
{
  main_loop_ok = FALSE;
  undo(NULL); /* 8.10 */
  printf("\n*** Abort");
  if (nlflag) printf("\n");
  return TRUE;
}



/******** C_NOT_IMPLEMENTED
  This function always fails, it is in fact identical to BOTTOM.
*/
static int c_not_implemented()
{
  ptr_psi_term t;
  
  t=aim->a;
  deref_ptr(t);
  Errorline("built-in %P is not implemented yet.\n",t);
  return FALSE;
}



/******** C_DECLARATION
  This function always fails, it is in fact identical to BOTTOM.
*/
static int c_declaration()
{
  ptr_psi_term t;
  
  t=aim->a;
  deref_ptr(t);
  Errorline("%P is a declaration, not a query.\n",t);
  return FALSE;
}



/******** C_SETQ
  Create a function with one rule F -> X, where F and X are
  the arguments of setq.  Setq quotes the second argument and
  is strict in (i.e. evaluates) the first argument.  Setq throws
  away any previous definition of F.
  F must be undefined or a function, there is an error if F is
  a sort or a predicate.
  This gives an error for a static function, but none for
  an undefined (i.e. uninterpreted) psi-term, which is made dynamic.
*/
static int c_setq()
{
  int success=FALSE;
  ptr_psi_term arg1,arg2,g;
  ptr_pair_list p;
  ptr_definition d;

  g=aim->a;
  get_two_args(g->attr_list,&arg1,&arg2);
  if (arg1 && arg2) {
    deref(arg2);
    deref_ptr(arg1);
    d=arg1->type;
    if (d->type==function || d->type==undef) {
      if (d->type==undef || !d->protected) {
        if (!arg1->attr_list) {
          d->type=function;
          d->protected=FALSE;
          p=HEAP_ALLOC(pair_list);
          p->a=heap_psi_term(4);
          p->a->type=d;
          clear_copy();
          p->b=quote_copy(arg2,HEAP);
          p->next=NULL;
          d->rule=p;
          success=TRUE;
        }
        else
         Errorline("%P may not have arguments in %P.\n",arg1,g);
      }
      else
        Errorline("%P should be dynamic in %P.\n",arg1,g);
    }
    else
      Errorline("%P should be a function or uninterpreted in %P.\n",arg1,g);
  }
  else
    Errorline("%P is missing one or both arguments.\n",g);

  return success;
}



/******** C_ASSERT_FIRST
  Assert a fact, inserting it as the first clause
  for that predicate or function.
*/
static int c_assert_first()
{
  int success=FALSE;
  ptr_psi_term arg1,g;
  
  g=aim->a;
  mark_quote(g); /* 14.9 */
  get_one_arg(g->attr_list,&arg1);
  assert_first=TRUE;
  if (arg1) {
    deref_ptr(arg1);
    assert_clause(arg1);
    encode_types();
    success=assert_ok;
  }
  else {
    success=FALSE;
    Errorline("bad clause in %P.\n",g);
  }
  
  return success;
}



/******** C_ASSERT_LAST
  Assert a fact, inserting as the last clause for that predicate or function.
*/
static int c_assert_last()
{
  int success=FALSE;
  ptr_psi_term arg1,g;
  
  g=aim->a;
  mark_quote(g); /* 14.9 */
  get_one_arg(g->attr_list,&arg1);
  assert_first=FALSE;
  if (arg1) {
    deref_ptr(arg1);
    assert_clause(arg1);
    encode_types();
    success=assert_ok;
  }
  else {
    success=FALSE;
    Errorline("bad clause in %P.\n",g);
  }
  
  return success;
}



/******** PRED_CLAUSE(t,r,g)
  Set about finding a clause that unifies with psi_term T.
  This routine is used both for CLAUSE and RETRACT.
  If R==TRUE then delete the first clause which unifies with T.
*/
int pred_clause(t,r,g)
ptr_psi_term t, g;
int r;
{
  int success=FALSE;
  ptr_psi_term head,body;
  
  mark_quote(g); /* 14.9 */
  if (t) {
    deref_ptr(t);
    
    if (!strcmp(t->type->symbol,"->")) {
      get_two_args(t->attr_list,&head,&body);
      if (head) {
	deref_ptr(head);
	if (head && body &&
            (head->type->type==function || head->type->type==undef))
	  success=TRUE;
      }
    }
    else if (!strcmp(t->type->symbol,":-")) {
      get_two_args(t->attr_list,&head,&body);
      if (head) {
        deref_ptr(head);
        if (head &&
            (head->type->type==predicate || head->type->type==undef)) {
          success=TRUE;
          if (!body) {
            body=stack_psi_term(4);
            body->type=succeed;
          }
        }
      }
    }
    /* There is no body, so t is a fact */
    else if (t->type->type==predicate || t->type->type==undef) {
      head=t;
      body=stack_psi_term(4);
      body->type=succeed;
      success=TRUE;
    }
  }
  
  if (success) {
    if (r) {
      if (redefine(head))
        push_goal(del_clause,head,body,&(head->type->rule));
      else
        success=FALSE;
    }
    else
      push_goal(clause,head,body,&(head->type->rule));
  }
  else
    Errorline("bad argument in %s.\n", (r?"retract":"clause"));
  
  return success;
}



/******** C_CLAUSE
  Find the clauses that unify with the argument in the rules.
  The argument must be a predicate or a function.
  Use PRED_CLAUSE to perform the search.
*/
static int c_clause()
{
  int success=FALSE;
  ptr_psi_term arg1,arg2,g;
  
  g=aim->a;
  get_two_args(g->attr_list,&arg1,&arg2);
  success=pred_clause(arg1,0,g);
  return success;
}



/******** C_RETRACT
  Retract the first clause that unifies with the argument.
  Use PRED_CLAUSE to perform the search.
*/
static int c_retract()
{
  int success=FALSE;
  ptr_psi_term arg1,arg2,g;
  
  g=aim->a;
  get_two_args(g->attr_list,&arg1,&arg2);
  success=pred_clause(arg1,1,g);
  
  return success;
}



/******** C_OPEN_IN
  Create a stream for input from the specified file.
*/
static int c_open_in()
{
  int success=FALSE;
  ptr_psi_term arg1,arg2,g;
  char *fn;
  
  g=aim->a;
  deref_ptr(g);
  get_two_args(g->attr_list,&arg1,&arg2);
  if(arg1) {
    deref(arg1);
    if (psi_to_string(arg1,&fn))
      if (arg2) {
	deref(arg2);
        deref_args(g,set_1_2);
	if (is_top(arg2)) {
	  if (open_input_file(fn)) {
	    /* push_ptr_value(psi_term_ptr,&(arg2->coref)); 9.6 */
	    push_psi_ptr_value(arg2,&(arg2->coref));
	    arg2->coref=input_state;
	    success=TRUE;
	  }
	  else
	    success=FALSE;
        }
	else
	  Errorline("bad input stream in %P.\n",g);
      }
      else
	Errorline("no stream in %P.\n",g);
    else
      Errorline("bad file name in %P.\n",g);
  }
  else
    Errorline("no file name in %P.\n",g);

  return success;
}



/******** C_OPEN_OUT
  Create a stream for output from the specified file.
*/
static int c_open_out()
{
  int success=FALSE;
  ptr_psi_term arg1,arg2,arg3,g;
  char *fn;
  
  g=aim->a;
  deref_ptr(g);
  get_two_args(g->attr_list,&arg1,&arg2);
  if(arg1) {
    deref(arg1);
    if (psi_to_string(arg1,&fn))
      if (arg2) {
	deref(arg2);
        deref(g);
	if (overlap_type(arg2->type,stream)) /* 10.8 */
	  if (open_output_file(fn)) {
            arg3=stack_psi_term(4);
	    arg3->type=stream;
	    arg3->value=(GENERIC)output_stream;
	    /* push_ptr_value(psi_term_ptr,&(arg2->coref)); 9.6 */
	    push_psi_ptr_value(arg2,&(arg2->coref));
	    arg2->coref=arg3;
	    success=TRUE;
	  }
	  else
	    success=FALSE;
	else
	  Errorline("bad stream in %P.\n",g);
      }
      else
	Errorline("no stream in %P.\n",g);
    else
      Errorline("bad file name in %P.\n",g);
  }
  else
    Errorline("no file name in %P.\n",g);
  
  return success;
}



/******** C_SET_INPUT
  Set the current input stream to a given stream.
  If the given stream is closed, then do nothing.
*/
static int c_set_input()
{
  int success=FALSE;
  ptr_psi_term arg1,arg2,g;
  FILE *thestream;
  
  g=aim->a;
  deref_ptr(g);
  get_two_args(g->attr_list,&arg1,&arg2);
  if (arg1) {
    deref(arg1);
    deref_args(g,set_1);
    if (equal_types(arg1->type,inputfilesym)) {
      success=TRUE;
      save_state(input_state);
      thestream=get_stream(arg1);
      if (thestream!=NULL) {
        input_state=arg1;
        restore_state(input_state);
      }
    }
    else
      Errorline("bad stream in %P.\n",g);
  }
  else
    Errorline("no stream in %P.\n",g);
  
  return success;
}



/******** C_SET_OUTPUT
  Set the current output stream.
*/
static int c_set_output()
{
  int success=FALSE;
  ptr_psi_term arg1,arg2,g;
  
  g=aim->a;
  deref_ptr(g);
  get_two_args(g->attr_list,&arg1,&arg2);
  if(arg1) {
    deref(arg1);
    deref_args(g,set_1);
    if(equal_types(arg1->type,stream) && arg1->value) {
      success=TRUE;
      output_stream=(FILE *)arg1->value;
    }
    else
      Errorline("bad stream in %P.\n",g);
  }
  else
    Errorline("no stream in %P.\n",g);
  
  return success;
}



/******** C_CLOSE
  Close a stream.
*/
static int c_close()
{
  int success=FALSE;
  int inclose,outclose;
  ptr_psi_term arg1,arg2,g,s;
  
  g=aim->a;
  deref_ptr(g);
  get_two_args(g->attr_list,&arg1,&arg2);
  if (arg1) {
    deref(arg1);
    deref_args(g,set_1);
    outclose=equal_types(arg1->type,stream) && arg1->value;
    inclose=FALSE;
    if (equal_types(arg1->type,inputfilesym)) {
      ptr_node n=find(featcmp,STREAM,arg1->attr_list);
      if (n) {
        arg1=(ptr_psi_term)n->data;
        inclose=(arg1->value!=NULL);
      }
    }

    if (inclose || outclose) {
      success=TRUE;
      fclose((FILE *)arg1->value);
      
      if (inclose && arg1->value==(GENERIC)input_stream)
	open_input_file("stdin");
      else if (outclose && arg1->value==(GENERIC)output_stream)
	open_output_file("stdout");
      
      arg1->value=NULL;
    }
    else
      Errorline("bad stream in %P.\n",g);
  }
  else
    Errorline("no stream in %P.\n",g);
  
  return success;
}


 

/******** C_GET
  Read the next character from the current input stream and return
  its Ascii code.  This includes blank characters, so this predicate
  differs slightly from Edinburgh Prolog's get(X).
  At end of file, return the psi-term 'end_of_file'.
*/
static int c_get()
{
  int success=TRUE;
  ptr_psi_term arg1,arg2,g,t;
  char c;
  
  g=aim->a;
  deref_ptr(g);
  get_two_args(g->attr_list,&arg1,&arg2);
  if (arg1) {
    deref(arg1);
    deref_args(g,set_1);

    if (eof_flag) {
      success=FALSE;
    }
    else {
      prompt="";
      c=read_char();
      t=stack_psi_term(0);
      if (c==EOF) {
        t->type=eof;
        eof_flag=TRUE;
      }
      else {
        t->type=integer;
        t->value=heap_alloc(sizeof(REAL)); /* 12.5 */
        * (REAL *)t->value = (REAL) c;
      }
    }
    
    if (success) {
      push_goal(unify,t,arg1,NULL);
      i_check_out(t);
    }
  }
  else {
    Errorline("argument missing in %P.\n",g);
    success=FALSE;
  }
 
  return success;
}



/******** C_PUT, C_PUT_ERR
  Write the root of a psi-term to the current output stream or to stderr.
  This routine accepts the string type (which is written without quotes),
  a number type (whose integer part is considered an Ascii code if it is
  in the range 0..255), and any other psi-term (in which case its name is
  written).
*/
static int c_put_main(); /* Forward declaration */

static int c_put()
{
  return c_put_main(FALSE);
}

static int c_put_err()
{
  return c_put_main(TRUE);
}

static int c_put_main(to_stderr)
int to_stderr;
{
  int i,success=FALSE;
  ptr_psi_term arg1,arg2,g;
  char *str="?";
  
  g=aim->a;
  deref_ptr(g);
  get_two_args(g->attr_list,&arg1,&arg2);
  if (arg1) {
    deref(arg1);
    deref_args(g,set_1);
    if ((equal_types(arg1->type,integer) || equal_types(arg1->type,real))
        && arg1->value) {
      i = (int) floor(*(REAL *) arg1->value);
      if (i==(int)(unsigned char)i) {
        sprintf(str,"%c",i);
        success=TRUE;
      }
      else {
        Errorline("out-of-range character value in %P.\n",g);
      }
    }
    else if (psi_to_string(arg1,&str)) {
      success=TRUE;
    }
    if (success)
      fprintf((to_stderr?stderr:output_stream),"%s",str);
  }
  else
    Errorline("argument missing in %P.\n",g);
  
  return success;
}



/******** GENERIC_WRITE
  Implements write, writeq, pretty_write, pretty_writeq.
*/
static int generic_write()
{
  ptr_psi_term g;

  g=aim->a;
  /* deref_rec(g); */
  deref_args(g,set_empty);
  pred_write(g->attr_list);
  /* fflush(output_stream); */
  return TRUE;
}

/******** C_WRITE_ERR
  Write a list of arguments to stderr.  Print cyclical terms
  correctly, but don't use the pretty printer indentation.
*/
static int c_write_err()
{
  indent=FALSE;
  const_quote=FALSE;
  write_stderr=TRUE;
  write_corefs=FALSE;
  write_resids=FALSE;
  return generic_write();
}

/******** C_WRITEQ_ERR
  Write a list of arguments to stderr in a form that allows them to be
  read in again.  Print cyclical terms correctly, but don't use the pretty
  printer indentation.
*/
static int c_writeq_err()
{
  indent=FALSE;
  const_quote=TRUE;
  write_stderr=TRUE;
  write_corefs=FALSE;
  write_resids=FALSE;
  /* write_corefs=TRUE; */
  return generic_write();
}

/******** C_WRITE
  Write a list of arguments. Print cyclical terms
  correctly, but don't use the pretty printer indentation.
*/
static int c_write()
{
  indent=FALSE;
  const_quote=FALSE;
  write_stderr=FALSE;
  write_corefs=FALSE;
  write_resids=FALSE;
  return generic_write();
}

/******** C_WRITEQ
  Write a list of arguments in a form that allows them to be read in
  again.  Print cyclical terms correctly, but don't use the pretty
  printer indentation.
*/
static int c_writeq()
{
  indent=FALSE;
  const_quote=TRUE;
  write_stderr=FALSE;
  write_corefs=FALSE;
  write_resids=FALSE;
  /* write_corefs=TRUE; */
  return generic_write();
}

/******** C_PRETTY_WRITE
  The same as write, only indenting if output is wider than PAGEWIDTH.
*/
static int c_pwrite()
{
  indent=TRUE;
  const_quote=FALSE;
  write_stderr=FALSE;
  write_corefs=FALSE;
  write_resids=FALSE;
  return generic_write();
}

/******** C_PRETTY_WRITEQ
  The same as writeq, only indenting if output is wider than PAGEWIDTH.
*/
static int c_pwriteq()
{
  indent=TRUE;
  const_quote=TRUE;
  write_stderr=FALSE;
  write_corefs=FALSE;
  write_resids=FALSE;
  /* write_corefs=TRUE; */
  return generic_write();
}



/******** C_PAGE_WIDTH
  Set the page width.
*/
static int c_page_width()
{
  int success=FALSE;
  ptr_psi_term arg1,arg2,g;
  int pw;
  
  g=aim->a;
  deref_ptr(g);
  get_two_args(g->attr_list,&arg1,&arg2);
  if(arg1) {
    deref(arg1);
    deref_args(g,set_1);
    if (equal_types(arg1->type,integer) && arg1->value) {
      pw = *(REAL *)arg1->value;
      if (pw>0)
        page_width=pw;
      else
        Errorline("argument in %P must be positive.\n",g);
      success=TRUE;
    }
    else if (sub_type(integer,arg1->type)) {
      push_goal(unify,arg1,real_stack_psi_term(4,(REAL)page_width),NULL);
      success=TRUE;
    }
    else
      Errorline("bad argument in %P.\n",g);
  }
  else
    Errorline("argument missing in %P.\n",g);
  
  return success;
}



/******** C_PRINT_DEPTH
  Set the depth limit of printing.
*/
static int c_print_depth()
{
  int success=FALSE;
  ptr_psi_term arg1,arg2,g;
  int dl;
  
  g=aim->a;
  deref_ptr(g);
  get_two_args(g->attr_list,&arg1,&arg2);
  if (arg1) {
    deref(arg1);
    deref_args(g,set_1);
    if (equal_types(arg1->type,integer) && arg1->value) {
      dl = *(REAL *)arg1->value;
      if (dl>=0)
        print_depth=dl;
      else
        Errorline("argument in %P must be positive or zero.\n",g);
      success=TRUE;
    }
    else if (sub_type(integer,arg1->type)) {
      push_goal(unify,arg1,real_stack_psi_term(4,(REAL)print_depth),NULL);
      success=TRUE;
    }
    else
      Errorline("bad argument in %P.\n",g);
  }
  else {
    /* No arguments: reset print depth to default value */
    print_depth=PRINT_DEPTH;
    success=TRUE;
  }
  
  return success;
}



/******** C_ROOTSORT
  Return the principal sort of the argument == create a copy with the
  attributes detached.
*/
static int c_rootsort()
{
  int success=TRUE;
  ptr_psi_term arg1,arg2,arg3,g,other;
  
  g=aim->a;
  deref_ptr(g);
  arg3=aim->b;
  deref(arg3);
  get_two_args(g->attr_list,&arg1,&arg2);
  if(arg1) {
    deref(arg1);
    deref_args(g,set_1);
    other=stack_psi_term(4); /* 19.11 */
    other->type=arg1->type;    
    other->value=arg1->value;
    resid_aim=NULL;
    push_goal(unify,arg3,other,NULL);
  }
  else
    curry();
  
  return success;
}




/******** C_DISJ
  This implements disjunctions (A;B).
  A nonexistent A or B is taken to mean 'fail'.
  Disjunctions should not be implemented in Life, because doing so results in
  both A and B being evaluated before the disjunction is.
  Disjunctions could be implemented in Life if there were a 'melt' predicate.
*/
static int c_disj()
{
  int success=TRUE;
  ptr_psi_term arg1,arg2,g;

  g=aim->a;
  resid_aim=NULL;
  deref_ptr(g);
  get_two_args(g->attr_list,&arg1,&arg2);
  deref_args(g,set_1_2);
  Traceline("pushing predicate disjunction choice point for %P\n",g);
  if (arg2) push_choice_point(prove,arg2,DEFRULES,NULL);
  if (arg1) push_goal(prove,arg1,DEFRULES,NULL);
  if (!arg1 && !arg2) {
    success=FALSE;
    Errorline("neither first nor second arguments exist in %P.\n",g);
  }

  return success;
}



/******** C_COND
  This implements COND(Condition,Then,Else).
  First Condition is evaluated.  If it returns true, return the Then value.
  If it returns false, return the Else value.  Either the Then or the Else
  values may be omitted, in which case they are considered to be true.
*/
static int c_cond()
{
  int success=TRUE;
  ptr_psi_term arg1,arg2,result,g;
  REAL val1;
  int num1;
  ptr_node n;
  
  g=aim->a;
  deref_ptr(g);
  result=aim->b;
  deref(result);
  
  get_one_arg(g->attr_list,&arg1);
  /* n=find(featcmp,"1",g->attr_list); 18.5 */
  /* if (n) */
  if (arg1) {
    /* arg1=(ptr_psi_term)n->data; */
    /* mark_eval(arg1); 24.8 XXX */
    deref(arg1);
    deref_args(g,set_1_2_3);
    success=get_bool_value(arg1,&val1,&num1);
    if (success) {
      if (num1) {
	resid_aim=NULL;
        n=find(featcmp,(val1?"2":"3"),g->attr_list);
        if (n) {
          arg2=(ptr_psi_term)n->data;
	  /* mark_eval(arg2); XXX 24.8 */
	  push_goal(unify,result,arg2,NULL);
	  i_check_out(arg2);
        }
        else {
          ptr_psi_term trueterm;
          trueterm=stack_psi_term(4);
          trueterm->type=true;
          push_goal(unify,result,trueterm,NULL);
        }
      }
      else
        residuate(arg1);
    }
  }
  else
    curry();
  
  return success;
}



/******** C_FEATURES
  Convert the feature names of a psi_term into a list of psi-terms.
  This uses the MAKE_LIST routine.
*/
static int c_features()
{
  int success=TRUE;
  ptr_psi_term arg1,arg2,funct,result;
  ptr_psi_term t;
  
  funct=aim->a;
  deref_ptr(funct);
  result=aim->b;
  get_two_args(funct->attr_list,&arg1,&arg2);
  if(arg1) {
    deref(arg1);
    deref_args(funct,set_1);
    resid_aim=NULL;
    make_list(arg1->attr_list,&t);
    push_goal(unify,result,t,NULL);
  }
  else
    curry();
  
  return success;
}


/* Return TRUE iff T is a type that should not show up as part of the
   type hierarchy, i.e. it is an internal hidden type. */
int hidden_type(t)
ptr_definition t;
{
   return (/* (t==conjunction) || 19.8 */ (t==disjunction) ||
           (t==constant) || (t==variable) ||
           (t==comment) || (t==functor));
}


insert_element(mid1, mid2, t)
ptr_psi_term *mid1, **mid2, t;
{
  ptr_list l;

  l=STACK_ALLOC(list);
  l->car=t;
  *mid2 = &(l->cdr);
 
  *mid1 = stack_psi_term(4);
  (*mid1)->type=alist;
  (*mid1)->value=(GENERIC)l;
}


/* Collect properties of the symbols in the symbol table, and make a
   psi-term list of them.
   This routine is parameterized (by sel) to collect three properties:
   1. All symbols that are types with no parents.
   2. All symbols that are of 'undef' type.
   3. The operator triples of all operators.

   Note the similarity between this routine and a tree-to-list
   routine in Prolog.  The pointer manipulations are simpler in
   Prolog, though.

   If the number of symbols is very large, this routine may run out of space
   before garbage collection.
*/
void collect_symbols(sel, st, head, tail)
int sel;
ptr_node st;
ptr_psi_term *head;
ptr_psi_term **tail;
{
  ptr_psi_term *mid1, *mid2, t;
  ptr_definition def;
  int botflag;
  
  /* Count the number of symbols; if not enough space remains,
     then push the eval goal back and return (?) */

  if (st==NULL) {
    *tail = head;
  }
  else {
    /* Concatenate the lists of the two subtrees */
    collect_symbols(sel, st->left, head, &mid1);

    def = (ptr_definition) st->data;

    if (sel==least_sel || sel==greatest_sel) {
      botflag=(sel==least_sel);

      /* Insert the node if it's a good one */
      if (((botflag?def->children:def->parents)==NULL &&
           def!=top && def!=nothing &&
           def->type==type ||
           def->type==undef)
          && !hidden_type(def)) {
        /* Create the node that will be inserted */
        t=stack_psi_term(4);
        t->type=def;
        insert_element(mid1, &mid2, t);
      }
      else {
        mid2=mid1;
      }
    }
    else if (sel==op_sel) {
      ptr_operator_data od=def->op_data;
      mid2=mid1;
      while (od) {
        ptr_psi_term name,type;

	t=stack_psi_term(4);
        t->type=opsym;

        stack_add_int_attr(t,one,od->precedence);

        type=stack_psi_term(4);
        switch (od->type) {
        case xf:
          type->type=xf_sym;
          break;
        case yf:
          type->type=yf_sym;
          break;
        case fx:
          type->type=fx_sym;
          break;
        case fy:
          type->type=fy_sym;
          break;
        case xfx:
          type->type=xfx_sym;
          break;
        case xfy:
          type->type=xfy_sym;
          break;
        case yfx:
          type->type=yfx_sym;
          break;
        }
        stack_add_psi_attr(t,"2",type);

        name=stack_psi_term(4);
        name->type=def;
        stack_add_psi_attr(t,"3",name);

        insert_element(mid1, &mid2, t);
        mid1=mid2;
        od=od->next;
      }
    }

    collect_symbols(sel, st->right, mid2, tail);
  }
}



/******** C_OPS
  Return a list of all operators (represented as 3-tuples op(prec,type,atom)).
  This function has no arguments.
*/
static int c_ops()
{
  int success=TRUE;
  ptr_psi_term result, g, t, *tail;

  g=aim->a;
  deref_args(g,set_empty);
  result=aim->b;
  collect_symbols(op_sel, symbol_table, &t, &tail);
  *tail=NULL;
  push_goal(unify,result,t,NULL);

  return success;
}




/******** C_STRIP
  Return the attributes of a psi-term, that is, a psi-term of type @ but with
  all the attributes of the argument.
*/
static int c_strip()
{
  int success=TRUE;
  ptr_psi_term arg1,arg2,funct,result;
  
  funct=aim->a;
  deref_ptr(funct);
  result=aim->b;
  get_two_args(funct->attr_list,&arg1,&arg2);
  if(arg1) {
    deref(arg1);
    deref_args(funct,set_1);
    resid_aim=NULL;
    merge_unify(&(result->attr_list),arg1->attr_list);
  }
  else
    curry();
  
  return success;
}




/******** C_SAME_ADDRESS
  Return TRUE if two arguments share the same address.
*/
static int c_same_address()
{
  int success=TRUE;
  ptr_psi_term arg1,arg2,funct,result;
  REAL val3;
  int num3;
  
  funct=aim->a;
  deref_ptr(funct);
  result=aim->b;
  get_two_args(funct->attr_list,&arg1,&arg2);
  
  if (arg1 && arg2) {
    success=get_bool_value(result,&val3,&num3);
    resid_aim=NULL;
    deref(arg1);
    deref(arg2);
    deref_args(funct,set_1_2);
    
    if (num3) {
      if (val3)
	push_goal(unify,arg1,arg2,NULL);
      else
	success=(arg1!=arg2);
    }
    else
      if (arg1==arg2)
	unify_bool_result(result,TRUE);
      else
	unify_bool_result(result,FALSE);
  }
  else
    curry();
  
  return success;
}




/******** C_EVAL
  Evaluate an expression and return its value.
*/
static int c_eval()
{
  int success=TRUE;
  ptr_psi_term arg1, copy_arg1, arg2, funct, result;

  funct = aim->a;
  deref_ptr(funct);
  result = aim->b;
  deref(result);
  get_two_args(funct->attr_list, &arg1, &arg2);
  if (arg1) {
    deref(arg1);
    deref_args(funct,set_1);
    assert((int)(arg1->type)!=4);
    clear_copy();
    copy_arg1 = eval_copy(arg1,STACK);
    resid_aim = NULL;
    push_goal(unify,copy_arg1,result,NULL);
    i_check_out(copy_arg1);
  } else
    curry();

  return success;
}




/******** C_EVAL_INPLACE
  Evaluate an expression and return its value.
*/
static int c_eval_inplace()
{
  int success=TRUE;
  ptr_psi_term arg1, copy_arg1, arg2, funct, result;

  funct = aim->a;
  deref_ptr(funct);
  result = aim->b;
  deref(result);
  get_two_args(funct->attr_list, &arg1, &arg2);
  if (arg1) {
    deref(arg1);
    deref_args(funct,set_1);
    resid_aim = NULL;
    mark_eval(arg1);
    push_goal(unify,arg1,result,NULL);
    i_check_out(arg1);
  } else
    curry();

  return success;
}




/******** C_QUOTE
  Quote an expression, i.e. do not evaluate it but mark it as completely
  evaluated.
  This works if the function is declared as non_strict.
*/
static int c_quote()
{
  int success=TRUE;
  ptr_psi_term arg1,arg2,funct,result;

  funct = aim->a;
  deref_ptr(funct);
  result = aim->b;
  deref(result);
  get_two_args(funct->attr_list, &arg1, &arg2);
  if (arg1) {
    push_goal(unify,arg1,result,NULL);
  } else
    curry();

  return success;
}




/******** C_PROVE
  Prove a predicate, return true or false if it succeeds or fails.
  An implicit cut is performed: only only solution is given.
*/
static int c_prove()
{
  int success=TRUE;
  ptr_psi_term arg1,arg2,funct,result,other;
  ptr_choice_point cutpt; 

  funct=aim->a;
  deref_ptr(funct);
  result=aim->b;
  get_two_args(funct->attr_list,&arg1,&arg2);
  if (arg1) {
    deref_ptr(arg1);
    deref_args(funct,set_1);
    if(arg1->type==top)
      residuate(arg1);
    else
      if(FALSE /*arg1->type->type!=predicate*/) {
        success=FALSE;
        Errorline("argument of %P should be a predicate.\n",funct);
      }
      else {
        resid_aim=NULL;
        cutpt=choice_stack;

        /* Result is FALSE */
        other=stack_psi_term(0);
        other->type=false;

        push_choice_point(unify,result,other,NULL);

        /* Result is TRUE */
        other=stack_psi_term(0);
        other->type=true;

        push_goal(unify,result,other,NULL);
        push_goal(eval_cut,other,cutpt,NULL); /* 13.6 */
        push_goal(prove,arg1,DEFRULES,NULL);
      }
  }
  else
    curry();

  return success;
}




/******** C_BK_ASSIGN()
  This implements backtrackable assignment.
*/
static int c_bk_assign()
{
  int success=FALSE;
  ptr_psi_term arg1,arg2,g;
  
  g=aim->a;
  deref_ptr(g);
  get_two_args(g->attr_list,&arg1,&arg2);
  if (arg1 && arg2) {
    success=TRUE;
    deref(arg1);
    deref_rec(arg2); /* 17.9 */
    /* deref(arg2); 17.9 */
    deref_args(g,set_1_2);
    if (arg1 != arg2) {
#ifdef TS
      if (!TRAIL_CONDITION(arg1)) {
        /* If no trail, then can safely overwrite the psi-term */
        release_resid_notrail(arg1);
        *arg1 = *arg2;
      }
      else {
        push_psi_ptr_value(arg1,&(arg1->coref));
        arg1->coref=arg2;
        release_resid(arg1);
      }
#else
      /* push_ptr_value(psi_term_ptr,&(arg1->coref)); 9.6 */
      push_psi_ptr_value(arg1,&(arg1->coref));
      arg1->coref=arg2;
      release_resid(arg1);
#endif
    }
  }
  else
    Errorline("argument missing in %P.\n",g);
  
  return success;
}




/******** C_ASSIGN()
  This implements non-backtrackable assignment.
  It doesn't work because backtrackable unifications can have been made before
  this assignment was reached. It is complicated by the fact that the assigned
  term has to be copied into the heap as it becomes a permanent object.
*/
static int c_assign()
{
  int success=FALSE;
  ptr_psi_term arg1,arg2,g,perm,smallest;
  
  g=aim->a;
  deref_ptr(g);
  get_two_args(g->attr_list,&arg1,&arg2);
  if (arg1 && arg2) {
    success=TRUE;
    deref_ptr(arg1);
    deref_rec(arg2); /* 17.9 */
    /* deref(arg2); 17.9 */
    deref_args(g,set_1_2);
    if (arg1!=arg2) {
      clear_copy();
      *arg1 = *exact_copy(arg2,HEAP);
    }
  }
  else
    Errorline("argument missing in %P.\n",g);
  
  return success;
}




/******** C_UNIFY_FUNC
  An explicit unify function that curries on its two arguments.
*/
static int c_unify_func()
{
  int success=TRUE;
  ptr_psi_term funct,arg1,arg2,result;

  funct=aim->a;
  deref_ptr(funct);
  get_two_args(funct->attr_list,&arg1,&arg2);
  if (arg1 && arg2) {
    deref(arg1);
    deref(arg2);
    deref_args(funct,set_1_2);
    result=aim->b;
    push_goal(unify,arg1,result,NULL);
    push_goal(unify,arg1,arg2,NULL);
  }
  else
    curry();

  return success;
}




/******** C_UNIFY_PRED()
  This unifies its two arguments (i.e. implements the predicate A=B).
*/
static int c_unify_pred()
{
  int success=FALSE;
  ptr_psi_term arg1,arg2,g;
  
  g=aim->a;
  deref_ptr(g);
  get_two_args(g->attr_list,&arg1,&arg2);
  if (arg1 && arg2) {
    deref_args(g,set_1_2);
    success=TRUE;
    push_goal(unify,arg1,arg2,NULL);
  }
  else
    Errorline("argument missing in %P.\n",g);
  
  return success;
}




/******** C_COPY_TERM
  Make a fresh copy of the input argument, keeping its structure
  but with no connections to the input.
*/
static int c_copy_term()
{
  int success=TRUE;
  ptr_psi_term funct,arg1,copy_arg1,result;

  funct=aim->a;
  deref_ptr(funct);
  get_one_arg(funct->attr_list,&arg1);
  if (arg1) {
    deref(arg1);
    deref_args(funct,set_1);
    result=aim->b;
    clear_copy();
    copy_arg1=exact_copy(arg1,STACK);
    push_goal(unify,copy_arg1,result,NULL);
  }
  else
    curry();

  return success;
}




/******** C_UNDO
  This will prove a goal on backtracking.
  This is a completely uninteresting implmentation which is equivalent to:

  undo.
  undo(G) :- G.

  The problem is that it can be affected by CUT.
  A correct implementation would be very simple:
  stack the pair (ADDRESS=NULL, VALUE=GOAL) onto the trail and when undoing
  push the goal onto the goal-stack.
*/
static int c_undo()
{
  int success=TRUE;
  ptr_psi_term arg1,arg2,g;
  
  g=aim->a;
  deref_ptr(g);
  get_two_args(g->attr_list,&arg1,&arg2);
  if (arg1) {
    deref_args(g,set_1);
    push_choice_point(prove,arg1,DEFRULES,NULL);
  }
  else {
    success=FALSE;
    Errorline("argument missing in %P.\n",g);
  }
  
  return success;
}




/******** C_FREEZE_INNER
  This implements the freeze and implies predicates.
  For example:

    freeze(g)

  The proof will use matching on the heads of g's definition rather than
  unification to prove Goal.  An implicit cut is put at the beginning
  of each clause body.  Body goals are executed in the same way as
  without freeze.  Essentially, the predicate is called as if it were
  a function.

    implies(g)

  The proof will use matching as for freeze, but there is no cut at the
  beginning of the clause body & no residuation is done (the clause
  fails if its head is not implied by the caller).  Essentially, the
  predicate is called as before except that matching is used instead
  of unification to decide whether to enter a clause.
*/
static int c_freeze_inner(freeze_flag)
int freeze_flag;
{
  int success=TRUE;
  ptr_psi_term arg1,g;
  ptr_psi_term head, body;
  ptr_pair_list rule;
  /* RESID */ ptr_resid_block rb;
  ptr_choice_point cutpt;
  ptr_psi_term match_date;
  
  g=aim->a;
  deref_ptr(g);
  get_one_arg(g->attr_list,&arg1);
  
  if (arg1) {
    deref_ptr(arg1);
    /* if (!arg1->type->evaluate_args) mark_quote(arg1); 8.9 */ /* 18.2 PVR */
    deref_args(g,set_1);
    deref_ptr(arg1);
    
    if (arg1->type->type!=predicate) {
      success=FALSE;
      Errorline("the argument %P of freeze must be a predicate.\n",arg1);
      /* main_loop_ok=FALSE; 8.9 */
      return success;
    }
    resid_aim=aim;
    match_date=(ptr_psi_term)stack_pointer;
    cutpt=choice_stack; /* 13.6 */
    /* Third argument of freeze's aim is used to keep track of which */
    /* clause is being tried in the frozen goal. */
    rule=(ptr_pair_list)aim->c; /* 8.9 */ /* Isn't aim->c always NULL? */
    resid_vars=NULL;
    curried=FALSE;
    can_curry=TRUE; /* 8.9 */

    if (!rule) rule=arg1->type->rule; /* 8.9 */
    /* if ((int)rule==DEFRULES) rule=arg1->type->rule; 8.9 */

    if (rule) {
      Traceline("evaluate frozen predicate %P\n",g);
      /* resid_limit=(ptr_goal )stack_pointer; 12.6 */
      
      if ((int)rule<=MAX_BUILT_INS) {
        success=FALSE; /* 8.9 */
        Errorline("the argument %P of freeze must be user-defined.\n",arg1); /* 8.9 */
        return success; /* 8.9 */
	/* Removed obsolete stuff here 11.9 */
      }
      else {
        while (rule && (rule->a==NULL || rule->b==NULL)) {
          rule=rule->next;
	  Traceline("alternative clause has been retracted\n");
        }
        if (rule) {
          /* RESID */ rb = STACK_ALLOC(resid_block);
          /* RESID */ save_resid(rb,match_date);
          /* RESID */ /* resid_aim = NULL; */

	  clear_copy();
          if (TRUE /*arg1->type->evaluate_args 8.9 */)
	    head=eval_copy(rule->a,STACK);
          else
	    head=quote_copy(rule->a,STACK);
	  body=eval_copy(rule->b,STACK);
	  head->status=4;

	  if (rule->next)
	    /* push_choice_point(prove,g,rule->next,NULL); 8.9 */
	    push_choice_point(prove,g,DEFRULES,rule->next);
	
	  push_goal(prove,body,DEFRULES,NULL);
	  if (freeze_flag) /* 12.10 */
	    push_goal(freeze_cut,body,cutpt,rb); /* 13.6 */
	  else
	    push_goal(implies_cut,body,cutpt,rb);
	  /* RESID */ push_goal(match,arg1,head,rb);
	  /* eval_args(head->attr_list); */
        }
        else {
          success=FALSE;
          /* resid_aim=NULL; */
        }
      }
    }
    else {
      success=FALSE;
      /* resid_aim=NULL; */
    }
    resid_aim=NULL;
    resid_vars=NULL; /* 22.9 */
  }
  else {
    success=FALSE;
    Errorline("goal missing in %P.\n",g);
  }
  
  /* match_date=NULL; */ /* 13.6 */
  return success;
}


/******** C_FREEZE()
  See c_freeze_inner.
*/
static int c_freeze()
{
  return c_freeze_inner(TRUE);
}


/******** C_IMPLIES()
  See c_freeze_inner.
*/
static int c_implies()
{
  return c_freeze_inner(FALSE);
}


/******** C_CHAR
  Return a one-character psi-term with an Ascii code equal to the integer
  argument.
*/
static int c_char()
{
  int success=TRUE;
  ptr_psi_term arg1,arg2,funct,result;
  int smaller;
  int num1;
  REAL val1;
  char c,*str="?";
  
  funct=aim->a;
  deref_ptr(funct);
  result=aim->b;
  deref(result);

  get_two_args(funct->attr_list,&arg1,&arg2);
  if (arg1) {
    deref(arg1);
    deref_args(funct,set_1);
    success=matches(arg1->type,real,&smaller);
    if (success) {
      if (arg1->value) {
        ptr_psi_term t;

        *str = c = (unsigned char) floor(*(REAL *) arg1->value);
        t=stack_psi_term(4);
        t->type=update_symbol(str);

        push_goal(unify,t,result,NULL);
      }
      else
        residuate(arg1);
    }
    else
      Errorline("argument of %P must be a number.\n",funct);
  }
  else
    curry();
  
  return success;
}




/******** C_ASCII
  Return the Ascii code of the first character of a string or of a
  psi-term's name.
*/
static int c_ascii()
{
  int success=TRUE;
  ptr_psi_term arg1,arg2,funct,result;
  int smaller;
  int num1;
  REAL val1;
  
  funct=aim->a;
  deref_ptr(funct);
  result=aim->b;
  deref(result);

  /* success=get_real_value(result,&val1,&num1); */
  /* if (success) { */
    get_two_args(funct->attr_list,&arg1,&arg2);
    if (arg1) {
      deref(arg1);
      deref_args(funct,set_1);
      success=matches(arg1->type,quoted_string,&smaller);
      if (success) {
	if (arg1->value) {
	  unify_real_result(result,(REAL)(*((char *)arg1->value)));
	}
	else
	  residuate(arg1);
      }
      else {
        success=TRUE;
        unify_real_result(result,(REAL)(*((char *)arg1->type->symbol)));
      }
    }
    else
      curry();
  /* } */
  
  return success;
}



/******** C_STRING2PSI(P)
  Convert a string to a psi-term whose name is the string's value.
*/
static int c_string2psi()
{
  int success=TRUE;
  ptr_psi_term arg1,arg3,funct,result,t;
  int smaller;

  funct=aim->a;
  deref_ptr(funct);
  result=aim->b;
  deref(result);

  get_one_arg(funct->attr_list,&arg1);
  if (arg1) {
    deref(arg1);
    deref_args(funct,set_1);
    success=matches(arg1->type,quoted_string,&smaller);
    if (success) {
      if (arg1->value) {
        t=stack_psi_term(4);
        t->type=update_symbol((char *)arg1->value);
        push_goal(unify,t,result,NULL);
      }
      else
        residuate(arg1);
    }
    else {
      success=FALSE;
      Warningline("argument of '%P' is not a string.\n",funct);
      /* report_warning(funct,"argument is not a string"); 9.9 */
    }
  }
  else
    curry();

  return success;
}



/******** C_PSI2STRING(P)
  Convert a psi-term's name into a string with the name as value.
*/
static int c_psi2string()
{
  int success=TRUE;
  ptr_psi_term arg1,arg3,funct,result,t;

  funct=aim->a;
  deref_ptr(funct);
  result=aim->b;
  deref(result);

  get_one_arg(funct->attr_list,&arg1);
  if (arg1) {
    deref(arg1);
    deref_args(funct,set_1);
    t=stack_psi_term(0);
    t->type=quoted_string;
    t->value=(GENERIC)heap_copy_string(arg1->type->symbol);
    push_goal(unify,t,result,NULL);
  }
  else
    curry();

  return success;
}



/******** C_INT2STRING(P)
  Convert an integer psi-term into a string representing its value.
*/
static int c_int2string()
{
  char val[STRLEN]; /* Big enough for a long number */
  int success=TRUE,i;
  ptr_psi_term arg1,arg3,funct,result,t;
  REAL the_int,next,neg;

  funct=aim->a;
  deref_ptr(funct);
  result=aim->b;
  deref(result);

  get_one_arg(funct->attr_list,&arg1);
  if (arg1) {
    deref(arg1);
    deref_args(funct,set_1);
    if (overlap_type(arg1->type,integer)) {
      if (arg1->value) {
        the_int = *(REAL *)arg1->value;

        if (the_int!=floor(the_int)) return FALSE;

        neg = (the_int<0.0);
        if (neg) the_int = -the_int;
        i=STRLEN;
        i--;
        val[i]=0;
        do {
          i--;
          if (i<=0) {
            Errorline("internal buffer too small for int2str(%P).\n",arg1);
            return FALSE;
          }
          next = floor(the_int/10);
          val[i]= '0' + (int) (the_int-next*10);
          the_int = next;
        } while (the_int);

        if (neg) { i--; val[i]='-'; }
        t=stack_psi_term(0);
        t->type=quoted_string;
        t->value=(GENERIC)heap_copy_string(&val[i]);
        push_goal(unify,t,result,NULL);
      }
      else
        residuate(arg1);
    }
    else
      success=FALSE;
  }
  else
    curry();

  return success;
}



/******** C_SUCH_THAT
  This implements 'Value | Goal'.
  First it unifies Value with the result, then it proves Goal.

  This routine is different than the straight forward implementation in Life
  which would have been: "V|G => cond(G,V,undefined)" because
  V is evaluated and unified before G is proved.
*/
static int c_such_that()
{
  int success=TRUE;
  ptr_psi_term arg1,arg2,funct,result;
  
  funct=aim->a;
  deref_ptr(funct);
  result=aim->b;
  get_two_args(funct->attr_list,&arg1,&arg2);
  if (arg1 && arg2) {
    deref_ptr(arg1);
    deref_ptr(arg2);
    deref_args(funct,set_1_2);
    resid_aim=NULL;
    push_goal(prove,arg2,DEFRULES,NULL);
    push_goal(unify,arg1,result,NULL);
    i_check_out(arg1);
  }
  else
    curry();
  
  return success;
}



/* Return an attr_list with one argument */
ptr_node one_attr()
{
   ptr_node n;

   n = STACK_ALLOC(node);
   n->key = one;
   n->data = NULL; /* To be filled in later */
   n->left = NULL;
   n->right = NULL;

   return n;
}


/* Return a psi term with one or two args, and the addresses of the args */
ptr_psi_term new_psi_term(numargs, typ, a1, a2)
int numargs;
ptr_definition typ;
ptr_psi_term **a1, **a2;
{
   ptr_psi_term t;
   ptr_node n1, n2;

   if (numargs==2) {
     n2 = STACK_ALLOC(node);
     n2->key = two;
     *a2 = (ptr_psi_term *) &(n2->data);
     n2->left = NULL;
     n2->right = NULL;
   }
   else
     n2=NULL;

   n1 = STACK_ALLOC(node);
   n1->key = one;
   *a1 = (ptr_psi_term *) &(n1->data);
   n1->left = NULL;
   n1->right = n2;

   t=stack_psi_term(4);
   t->type = typ;
   t->attr_list = n1;

   return t;
}


/* Return TRUE iff there are some rules r */
/* This is true for a user-defined function or predicate with a definition, */
/* and for a type with constraints. */
int has_rules(r)
ptr_pair_list r;
{
  if (r==NULL) return FALSE;
  while (r) {
    if (r->a!=NULL) return TRUE;
    r=r->next;
  }
  return FALSE;
}

/* Return TRUE if rules r are for a built-in */
int is_built_in(r)
ptr_pair_list r;
{
  return ((int)r>0 && (int)r<MAX_BUILT_INS);
}


/* List the characteristics (delay_check, dynamic/static, non_strict) */
/* in such a way that they can be immediately read in. */
list_special(t)
ptr_psi_term t;
{
  ptr_definition d = t->type;
  ptr_pair_list r = t->type->rule;
  int prflag=FALSE;

  if (t->type->type==type) {
    if (!d->always_check) {
      if (is_built_in(r)) fprintf(output_stream,"%% ");
      fprintf(output_stream,"delay_check(");
      display_psi_stream(t);
      fprintf(output_stream,")?\n");
      prflag=TRUE;
    }
  } else {
    if (!d->protected) {
      if (is_built_in(r)) fprintf(output_stream,"%% ");
      fprintf(output_stream,"%s(",(d->protected?"static":"dynamic"));
      display_psi_stream(t);
      fprintf(output_stream,")?\n");
      prflag=TRUE;
    } 
  }
  if (!d->evaluate_args) {
    if (is_built_in(r)) fprintf(output_stream,"%% ");
    fprintf(output_stream,"non_strict(");
    display_psi_stream(t);
    fprintf(output_stream,")?\n");
    prflag=TRUE;
  }
  /* if (prflag) fprintf(output_stream,"\n"); */
}


/******** C_LISTING
  List the definition of a predicate or a function, and the own constraints
  of a type (i.e. the non-inherited constraints).
*/
static int c_listing()
{
  int success=TRUE;
  ptr_psi_term arg1,arg2,g;
  int fp;
  ptr_pair_list r;
  ptr_node n;
  ptr_psi_term t, t2, *a1, *a2, *a3;
  char *s1,*s2;
  
  g=aim->a;
  deref_ptr(g);
  get_two_args(g->attr_list,&arg1,&arg2);
  if (arg1) {
    deref_ptr(arg1);
    list_special(arg1);
    fp=arg1->type->type;
    r=arg1->type->rule;
    if (is_built_in(r) || !has_rules(r)) {

      if (is_built_in(r)) {
        s1="built-in ";
        s2="";
      }
      else {
        s1="user-defined ";
        s2=" with an empty definition";
      }
      switch (fp) {
      case function:
        fprintf(output_stream,"%% '%s' is a %sfunction%s.\n",
                arg1->type->symbol,s1,s2);
        break;
      case predicate:
        fprintf(output_stream,"%% '%s' is a %spredicate%s.\n",
                arg1->type->symbol,s1,s2);
        break;
      case type:
        if (arg1->value) {
          fprintf(output_stream,"%% ");
          if (arg1->type!=quoted_string) fprintf(output_stream,"'");
          display_psi_stream(arg1);
          if (arg1->type!=quoted_string) fprintf(output_stream,"'");
          fprintf(output_stream," is a value of sort '%s'.\n",
                  arg1->type->symbol);
        }
        break;
      default:
        fprintf(output_stream,"%% '%s' is undefined.\n", arg1->type->symbol);
      }
    }
    else {
      if (fp==type || fp==function || fp==predicate) {
        n = one_attr();
        if (fp==function)
          t = new_psi_term(2, funcsym, &a1, &a2);
        else if (fp==predicate)
          t = new_psi_term(2, predsym, &a1, &a2);
        else { /* fp==type */
          t = new_psi_term(1, typesym, &a3, &a2); /* a2 is a dummy */
          t2 = new_psi_term(2, such_that, &a1, &a2);
        }
        n->data = (GENERIC) t;
        while (r) {
          *a1 = r->a; /* Func, pred, or type */
          *a2 = r->b;
          if (r->a) {
            /* Handle an attribute constraint with no predicate: */
            if (fp==type) { if (r->b==NULL) *a3 = r->a; else *a3 = t2; }
            listing_pred_write(n, (fp==function)||(fp==type));
            fprintf(output_stream,".\n");
          }
          r = r->next;
        }
        /* fprintf(output_stream,"\n"); */
        /* fflush(output_stream); */
      }
      else {
        success=FALSE;
        Errorline("argument of %P must be a predicate, function, or sort.\n",g);
      }
    }
  }
  else {
    success=FALSE;
    Errorline("argument missing in %P.\n",g);
  }
  
  return success;
}



/******** C_print_codes
  Print the codes of all the sorts.
*/
static int c_print_codes()
{
  ptr_psi_term t;

  t=aim->a;
  deref_args(t,set_empty);
  outputline("There are %d sorts.\n",type_count);
  print_codes();
  return TRUE;
}



/*********************** TEMPLATES FOR NEW PREDICATES AND FUNCTIONS  *******/



/******** C_PRED
  Template for C built-in predicates.
*/
static int c_pred()
{
  int success=TRUE;
  ptr_psi_term arg1,arg2,g;
  
  g=aim->a;
  deref_ptr(g);
  get_two_args(g->attr_list,&arg1,&arg2);
  if (arg1 && arg2) {
    deref_args(g,set_1_2);
  }
  else {
    success=FALSE;
    Errorline("argument(s) missing in %P.\n",g);
  }
  
  return success;
}



/******** C_FUNCT
  Template for C built-in functions.
*/
static int c_funct()
{
  int success=TRUE;
  ptr_psi_term arg1,arg2,funct;

  
  funct=aim->a;
  deref_ptr(funct);

  get_two_args(funct->attr_list,&arg1,&arg2);

  if (arg1 && arg2) {
    deref_args(funct,set_1_2);
  }
  else
    curry();
  
  return success;
}



/******************************************************************************
  
  Here are the routines which allow a new built_in type, predicate or function
  to be declared.
  
  ****************************************************************************/



/******** NEW_BUILT_IN(s,t,r)
  Add a new built-in predicate or function.
  Used also in x_pred.c

  S=string.
  T=type (function or predicate).
  R=address of C routine to call.
*/
void new_built_in(s,t,r)
char *s;
def_type t;
int (*r)();
{
  ptr_definition d;
  
  d=update_symbol(s);
  d->type=t;
  built_in_index++;
  d->rule=(ptr_pair_list )built_in_index;
  c_rule[built_in_index]=r;
}



/******** OP_DECLARE(p,t,s)
  Declare that string S is an operator of precedence P and of type T where
  T=xf, fx, yf, fy, xfx etc...
*/
static void op_declare(p,t,s)
int p;
operator t;
char *s;
{
  ptr_definition d;
  ptr_operator_data od;
  
  if (p>MAX_PRECEDENCE || p<0) {
    Errorline("operator precedence must be in the range 0..%d.\n",
	      MAX_PRECEDENCE);
    return;
  }
  d=update_symbol(s);

  od= (ptr_operator_data) heap_alloc (sizeof(operator_data));
  /* od= (ptr_operator_data) malloc (sizeof(operator_data)); 12.6 */
    
  od->precedence=p;
  od->type=t;
  od->next=d->op_data;
  d->op_data=od;
}



/******** DECLARE_OPERATOR(t)
  Declare a new operator or change a pre-existing one.

  For example: '*op*'(3,xfx,+)?
  T is the OP declaration.
*/
int declare_operator(t)
ptr_psi_term t;
{
  ptr_psi_term prec,type,atom;
  ptr_node n;
  char *s;
  int p;
  operator kind=nop;
  int success=FALSE;

  deref_ptr(t);
  n=t->attr_list;
  get_two_args(n,&prec,&type);
  n=find(featcmp,"3",n);
  if (n && prec && type) {
    atom=(ptr_psi_term )n->data;
    deref_ptr(prec);
    deref_ptr(type);
    deref_ptr(atom);
    if (!atom->value) {
      s=atom->type->symbol;
      if (sub_type(prec->type,integer) && prec->value) { /* 10.8 */
        p = * (REAL *)prec->value;
	if (p>0 && p<=MAX_PRECEDENCE) {
          if (type->type == xf_sym) kind=xf;
          else if (type->type == yf_sym) kind=yf;
          else if (type->type == fx_sym) kind=fx;
          else if (type->type == fy_sym) kind=fy;
          else if (type->type == xfx_sym) kind=xfx;
          else if (type->type == xfy_sym) kind=xfy;
          else if (type->type == yfx_sym) kind=yfx;
          else
            Errorline("bad operator kind '%s'.\n",type->type->symbol);
    
          if (kind!=nop) {
	    op_declare(p,kind,s);
	    success=TRUE;
	  }
        }
	else
	  Errorline("precedence must range from 1 to 1200 in %P.\n",t);
      }
      else
        Errorline("precedence must be a positive integer in %P.\n",t);
    }
    else
      Errorline("numbers or strings may not be operators in %P.\n",t);
  }
  else
    Errorline("argument missing in %P.\n",t);

  return success;
}



char *str_conc(s1,s2)
char *s1, *s2;
{
  char *result;

  result=(char *)heap_alloc(strlen(s1)+strlen(s2)+1);
  sprintf(result,"%s%s",s1,s2);

  return result;
}


char *sub_str(s,p,n)
char *s;
int p;
int n;
{
  char *result;
  int i;
  int l;

  l=strlen(s);
  if(p>l || p<0 || n<0)
    n=0;
  else
    if(p+n-1>l)
      n=l-p+1;

  result=(char *)heap_alloc(n+1);
  for(i=0;i<n;i++)
    *(result+i)= *(s+p+i-1);

  *(result+n)=0;
  
  return result;
}


int append_files(s1,s2)
char *s1, *s2;
{
  FILE *f1;
  FILE *f2;
  int result=FALSE;
  
  f1=fopen(s1,"a");
  if(f1) {
    f2=fopen(s2,"r");
    if(f2) {
      while(!feof(f2))
	fputc(fgetc(f2),f1);
      fclose(f2);
      fclose(f1);
      result=TRUE;
    }
    else
      printf("*** Error: couldn't open \"%s\"\n",f2);
   }
  else
    printf("*** Error: couldn't open \"%s\"\n",f1);

  return result;
}




/******** C_CONCATENATE
  Concatenate the strings in arguments 1 and 2.
*/
int c_concatenate()
{
  ptr_psi_term result,funct,temp_result;
  ptr_node n1, n2;
  int success=TRUE;
  int all_args=TRUE;
  char * c_result;
  ptr_psi_term arg1; 
  char * c_arg1; 
  ptr_psi_term arg2; 
  char * c_arg2; 

  funct=aim->a;
  deref_ptr(funct);
  result=aim->b;

  /* Evaluate all arguments first: */
  n1=find(featcmp,"1",funct->attr_list);
  if (n1) {
    arg1= (ptr_psi_term )n1->data;
    deref(arg1);
  }
  n2=find(featcmp,"2",funct->attr_list);
  if (n2) {
    arg2= (ptr_psi_term )n2->data;
    deref(arg2);
  }
  deref_args(funct,set_1_2);

  if (success) {
    if (n1) {
       if (overlap_type(arg1->type,quoted_string)) /* 10.8 */
          if (arg1->value)
              c_arg1= (char *)arg1->value;
          else {
            residuate(arg1);
            all_args=FALSE;
          }
       else
         success=FALSE;
    }
    else {
      all_args=FALSE;
      curry();
    };
  };

  if (success) {
    if (n2) {
       if (overlap_type(arg2->type,quoted_string)) /* 10.8 */
          if (arg2->value)
              c_arg2= (char *)arg2->value;
          else {
            residuate(arg2);
            all_args=FALSE;
          }
       else
         success=FALSE;
    }
    else {
      all_args=FALSE;
      curry();
    };
  };

  if(success && all_args) {
      c_result=str_conc( c_arg1, c_arg2 );
      temp_result=stack_psi_term(0);
      temp_result->type=quoted_string;
      temp_result->value=(GENERIC) c_result;
      push_goal(unify,temp_result,result,NULL);
  };

return success;
}




/******** C_STRING_LENGTH
  Return the length of the string in argument 1.
*/
int c_string_length()
{
  ptr_psi_term result,funct;
  ptr_node n1;
  int success=TRUE;
  int all_args=TRUE;
  int c_result;
  ptr_psi_term arg1; 
  char * c_arg1; 

  funct=aim->a;
  deref_ptr(funct);
  result=aim->b;

  /* Evaluate all arguments first: */
  n1=find(featcmp,"1",funct->attr_list);
  if (n1) {
    arg1= (ptr_psi_term )n1->data;
    deref(arg1);
  }
  deref_args(funct,set_1);

  if (success) {
    if (n1) {
       if (overlap_type(arg1->type,quoted_string)) /* 10.8 */
          if (arg1->value)
              c_arg1= (char *)arg1->value;
          else {
            residuate(arg1);
            all_args=FALSE;
          }
       else
         success=FALSE;
    }
    else {
      all_args=FALSE;
      curry();
    };
  };

  if (success && all_args) {
      c_result=strlen(c_arg1);
      push_goal(unify,real_stack_psi_term(0,(REAL)c_result),result,NULL);
  };

return success;
}




/******** C_SUB_STRING
  Return the substring of argument 1 from position argument 2 for a
  length of argument 3 characters.
*/
int c_sub_string()
{
  ptr_psi_term result,funct,temp_result;
  ptr_node n1,n2,n3;
  int success=TRUE;
  int all_args=TRUE;
  char * c_result;
  ptr_psi_term arg1; 
  char * c_arg1; 
  ptr_psi_term arg2; 
  int c_arg2; 
  ptr_psi_term arg3; 
  int c_arg3; 

  funct=aim->a;
  deref_ptr(funct);
  result=aim->b;

  /* Evaluate all arguments first: */
  n1=find(featcmp,"1",funct->attr_list);
  if (n1) {
    arg1= (ptr_psi_term )n1->data;
    deref(arg1);
  }
  n2=find(featcmp,"2",funct->attr_list);
  if (n2) {
    arg2= (ptr_psi_term )n2->data;
    deref(arg2);
  }
  n3=find(featcmp,"3",funct->attr_list);
  if (n3) {
    arg3= (ptr_psi_term )n3->data;
    deref(arg3);
  }
  deref_args(funct,set_1_2_3);

  if (success) {
    if (n1) {
       if (overlap_type(arg1->type,quoted_string)) /* 10.8 */
          if (arg1->value)
              c_arg1= (char *)arg1->value;
          else {
            residuate(arg1);
            all_args=FALSE;
          }
       else
         success=FALSE;
    }
    else {
      all_args=FALSE;
      curry();
    };
  };

  if (success) {
    if (n2) {
       if (overlap_type(arg2->type,integer)) /* 10.8 */
          if (arg2->value)
              c_arg2= (int)(* (double *)(arg2->value));
          else {
            residuate(arg2);
            all_args=FALSE;
          }
       else
         success=FALSE;
    }
    else {
      all_args=FALSE;
      curry();
    };
  };

  if (success) {
    if (n3) {
       if (overlap_type(arg3->type,integer)) /* 10.8 */
          if (arg3->value)
              c_arg3= (int)(* (double *)(arg3->value));
          else {
            residuate(arg3);
            all_args=FALSE;
          }
       else
         success=FALSE;
    }
    else {
      all_args=FALSE;
      curry();
    };
  };

  if (success && all_args) {
      c_result=sub_str(c_arg1,c_arg2,c_arg3);
      temp_result=stack_psi_term(0);
      temp_result->type=quoted_string;
      temp_result->value=(GENERIC) c_result;
      push_goal(unify,temp_result,result,NULL);
  };

return success;
}




/******** C_APPEND_FILE
  Append the file named by argument 2 to the file named by argument 1.
  This predicate will not residuate; it requires string arguments.
*/
int c_append_file()
{
  ptr_psi_term g;
  ptr_node n1,n2;
  int success=TRUE;
  ptr_psi_term arg1; 
  char * c_arg1; 
  ptr_psi_term arg2; 
  char * c_arg2; 

  g=aim->a;
  deref_ptr(g);

  /* Evaluate all arguments first: */
  n1=find(featcmp,"1",g->attr_list);
  if (n1) {
    arg1= (ptr_psi_term )n1->data;
    deref(arg1);
  }
  n2=find(featcmp,"2",g->attr_list);
  if (n2) {
    arg2= (ptr_psi_term )n2->data;
    deref(arg2);
  }
  deref_args(g,set_1_2);

  if (success) {
    if (n1) {
       if (overlap_type(arg1->type,quoted_string))
          if (arg1->value)
              c_arg1= (char *)arg1->value;
          else {
            success=FALSE;
            Errorline("bad argument in %P.\n",g);
          }
       else
         success=FALSE;
    }
    else {
      success=FALSE;
      Errorline("bad argument in %P.\n",g);
    };
  };

  if (success) {
    if (n2) {
       if (overlap_type(arg2->type,quoted_string))
          if (arg2->value)
              c_arg2= (char *)arg2->value;
          else {
            success=FALSE;
            Errorline("bad argument in %P.\n",g);
          }
       else
         success=FALSE;
    }
    else {
      success=FALSE;
      Errorline("bad argument in %P.\n",g);
    };
  };

  if (success)
    success=append_files(c_arg1,c_arg2);

return success;
}



/******** C_RANDOM
  Return an integer random number between 0 and abs(argument 1).
  Uses the Unix random() function.
*/
int c_random()
{
  ptr_psi_term result,funct;
  ptr_node n1;
  int success=TRUE;
  int all_args=TRUE;
  int c_result;
  ptr_psi_term arg1; 
  int c_arg1; 

  funct=aim->a;
  deref_ptr(funct);
  result=aim->b;

  /* Evaluate all arguments first: */
  n1=find(featcmp,"1",funct->attr_list);
  if (n1) {
    arg1= (ptr_psi_term )n1->data;
    deref(arg1);
  }
  deref_args(funct,set_1);

  if (success) {
    if (n1) {
       if (overlap_type(arg1->type,integer))
          if (arg1->value)
              c_arg1= (int)(* (double *)(arg1->value));
          else {
            residuate(arg1);
            all_args=FALSE;
          }
       else
         success=FALSE;
    }
    else {
      all_args=FALSE;
      curry();
    }
  }

  if (success && all_args) {
      if (c_arg1) {
        c_result=random();
        c_result=c_result-(c_result/c_arg1)*c_arg1;
      }
      else
        c_result=0;

      push_goal(unify,real_stack_psi_term(0,(REAL)c_result),result,NULL);
  }

  return success;
}



/******** C_INITRANDOM
  Uses its integer argument to initialize
  the random number generator, which is the Unix random() function.
*/
int c_initrandom()
{
  ptr_psi_term t;
  ptr_node n1;
  int success=TRUE;
  int all_args=TRUE;
  int c_result;
  ptr_psi_term arg1; 
  int c_arg1; 

  t=aim->a;
  deref_ptr(t);

  /* Evaluate all arguments first: */
  n1=find(featcmp,"1",t->attr_list);
  if (n1) {
    arg1= (ptr_psi_term )n1->data;
    deref(arg1);
  }
  deref_args(t,set_1);

  if (success) {
    if (n1) {
       if (overlap_type(arg1->type,integer))
          if (arg1->value)
              c_arg1= (int)(* (double *)(arg1->value));
          else {
            residuate(arg1);
            all_args=FALSE;
          }
       else
         success=FALSE;
    }
    else {
      all_args=FALSE;
    }
  }

  if (success && all_args) srandom(c_arg1);

  return success;
}


    
/******** INIT_BUILT_IN_TYPES
  Initialise the symbol tree with the built-in types.
  Declare all built-in predicates and functions.
  Initialise system type variables.
  Declare all standard operators.

  Called by life.c
*/
void init_built_in_types()
{
  ptr_definition t;
  symbol_table=NULL;
  
  and=update_symbol(",");
  apply=update_symbol("*apply*");
  boolean=update_symbol("bool");
  boolsym=update_symbol("*bool_pred*");
  built_in=update_symbol("built_in");
  colonsym=update_symbol(":");
  commasym=update_symbol(",");
  comment=update_symbol("*comment*");
  /* conjunction=update_symbol("*conjunction*"); 19.8 */
  constant=update_symbol("*constant*");
  cut=update_symbol("!");
  disjunction=update_symbol("*disjunction*");
  eof=update_symbol("end_of_file");
  eqsym=update_symbol("=");
  false=update_symbol("false");
  funcsym=update_symbol("->");
  functor=update_symbol("*functor*");
  iff=update_symbol("cond");
  integer=update_symbol("int");
  alist=update_symbol("list");
  list_object=update_symbol("*list_object*");
  nothing=update_symbol("*bottom*");
  predsym=update_symbol(":-");
  quote=update_symbol("`");
  quoted_string=update_symbol("string");
  real=update_symbol("real");
  stream=update_symbol("stream");
  succeed=update_symbol("succeed");
  such_that=update_symbol("|");
  top=update_symbol("@");
  true=update_symbol("true");
  timesym=update_symbol("time");
  typesym=update_symbol("::");
  variable=update_symbol("*variable*");
  opsym=update_symbol("op");
  loadsym=update_symbol("load");
  dynamicsym=update_symbol("dynamic");
  staticsym=update_symbol("static");
  encodesym=update_symbol("encode");
  listingsym=update_symbol("listing");
  provesym=update_symbol("prove");
  delay_checksym=update_symbol("delay_check");
  eval_argsym=update_symbol("non_strict");
  inputfilesym=update_symbol("input_file");
  call_handlersym=update_symbol("call_handler");
  xf_sym=update_symbol("xf");
  yf_sym=update_symbol("yf");
  fx_sym=update_symbol("fx");
  fy_sym=update_symbol("fy");
  xfx_sym=update_symbol("xfx");
  xfy_sym=update_symbol("xfy");
  yfx_sym=update_symbol("yfx");
  nullsym=update_symbol("<NULL PSI TERM>");
  null_psi_term=heap_psi_term(4);
  null_psi_term->type=nullsym;
  
  t=update_symbol("1");
  one=t->symbol;
  t=update_symbol("2");
  two=t->symbol;
  t=update_symbol("year");
  year_attr=t->symbol;
  t=update_symbol("month");
  month_attr=t->symbol;
  t=update_symbol("day");
  day_attr=t->symbol;
  t=update_symbol("hour");
  hour_attr=t->symbol;
  t=update_symbol("minute");
  minute_attr=t->symbol;
  t=update_symbol("second");
  second_attr=t->symbol;
  t=update_symbol("weekday");
  weekday_attr=t->symbol;
  
  nothing->type=type;
  top->type=type;

  error_psi_term=heap_psi_term(4); /* 8.10 */
  error_psi_term->type=update_symbol("*** ERROR ***");
  error_psi_term->type->code=NOT_CODED;

  /* Built-in routines */

  /* Program database */
  new_built_in("dynamic",predicate,c_dynamic);
  new_built_in("static",predicate,c_static);
  new_built_in("assert",predicate,c_assert_last);
  new_built_in("asserta",predicate,c_assert_first);
  new_built_in("clause",predicate,c_clause);
  new_built_in("retract",predicate,c_retract);
  new_built_in("setq",predicate,c_setq);
  new_built_in("*listing*",predicate,c_listing);
  new_built_in("*print_codes*",predicate,c_print_codes);

  /* File I/O */
  new_built_in("get",predicate,c_get);
  new_built_in("put",predicate,c_put);
  new_built_in("open_in",predicate,c_open_in);
  new_built_in("open_out",predicate,c_open_out);
  new_built_in("set_input",predicate,c_set_input);
  new_built_in("set_output",predicate,c_set_output);
  new_built_in("exists",predicate,c_exists);
  new_built_in("close",predicate,c_close);
  new_built_in("simple_load",predicate,c_load);
  new_built_in("*put_err*",predicate,c_put_err);

  /* Term I/O */
  new_built_in("write",predicate,c_write);
  new_built_in("writeq",predicate,c_writeq);
  new_built_in("pretty_write",predicate,c_pwrite);
  new_built_in("pretty_writeq",predicate,c_pwriteq);
  new_built_in("page_width",predicate,c_page_width);
  new_built_in("print_depth",predicate,c_print_depth);
  new_built_in("*put_err*",predicate,c_put_err);
  new_built_in("parse",function,c_parse);
  new_built_in("read",predicate,c_read_psi);
  new_built_in("read_token",predicate,c_read_token);
  new_built_in("*op*",predicate,c_op);
  new_built_in("*ops*",function,c_ops);
  new_built_in("*write_err*",predicate,c_write_err);
  new_built_in("*writeq_err*",predicate,c_writeq_err);

  /* Type checks */
  new_built_in("nonvar",predicate,c_nonvar);
  new_built_in("var",predicate,c_var);
  new_built_in("is_function",predicate,c_is_function);
  new_built_in("is_predicate",predicate,c_is_predicate);
  new_built_in("is_sort",predicate,c_is_sort);
  
  /* Arithmetic */
  insert_math_builtins();

  /* Comparison */
  new_built_in("<",function,c_lt);  
  new_built_in("=<",function,c_ltoe);  
  new_built_in(">",function,c_gt);  
  new_built_in(">=",function,c_gtoe);  
  new_built_in("=\\=",function,c_diff);
  new_built_in("=:=",function,c_equal);
  new_built_in("and",function,c_and);
  new_built_in("or",function,c_or);
  new_built_in("===",function,c_same_address);

  /* Psi-term navigation */
  new_built_in("features",function,c_features);
  new_built_in("project",function,c_project);
  new_built_in("rootsort",function,c_rootsort);
  new_built_in("strip",function,c_strip);

  /* Unification and assignment */
  new_built_in("<-",predicate,c_bk_assign);
  new_built_in("<<-",predicate,c_assign);
  new_built_in("=",predicate,c_unify_pred);
  new_built_in(":",function,c_unify_func); /* new 19.8 */
  new_built_in("&",function,c_unify_func);
  new_built_in("copy_term",function,c_copy_term);
  /* UNI new_built_in(":",function,c_unify_func); */

  /* Type hierarchy navigation */
  insert_type_builtins();

  /* String and character utilities */
  new_built_in("str2psi",function,c_string2psi);
  new_built_in("psi2str",function,c_psi2string);
  new_built_in("int2str",function,c_int2string);
  new_built_in("asc",function,c_ascii);
  new_built_in("chr",function,c_char);

  /* Control */
  new_built_in("|",function,c_such_that);
  new_built_in("cond",function,c_cond);
  new_built_in("eval",function,c_eval);
  new_built_in("evalin",function,c_eval_inplace);
  /* new_built_in("quote",function,c_quote); */
  new_built_in("prove",function,c_prove);
  new_built_in("undefined",function,c_fail);
  new_built_in("*print_variables*",predicate,c_print_variables);
  new_built_in("*get_choice*",function,c_get_choice);
  new_built_in("*set_choice*",predicate,c_set_choice);
  new_built_in("*exists_choice*",function,c_exists_choice);
  new_built_in("*apply*",function,c_apply);
  new_built_in("*bool_pred*",predicate,c_boolpred);

  new_built_in(":-",predicate,c_declaration);
  new_built_in("->",predicate,c_declaration);
  /* new_built_in("::",predicate,c_declaration); */
  new_built_in("<|",predicate,c_declaration);
  new_built_in(":=",predicate,c_declaration);

  new_built_in(";",predicate,c_disj);
  new_built_in("!",predicate,c_not_implemented);
  new_built_in(",",predicate,c_succeed);
  new_built_in("abort",predicate,c_abort);
  new_built_in("halt",predicate,c_halt);
  new_built_in("succeed",predicate,c_succeed);
  new_built_in("repeat",predicate,c_repeat);
  new_built_in("fail",predicate,c_fail);
  new_built_in("freeze",predicate,c_freeze);
  new_built_in("implies",predicate,c_implies);
  new_built_in("undo",predicate,c_undo);
  new_built_in("delay_check",predicate,c_delay_check);
  new_built_in("non_strict",predicate,c_non_strict);
  
  /* System */
  insert_system_builtins();

  new_built_in("strcon",function,c_concatenate);
  new_built_in("strlen",function,c_string_length);
  new_built_in("substr",function,c_sub_string);
  new_built_in("append_file",predicate,c_append_file);
  new_built_in("random",function,c_random);
  new_built_in("initrandom",predicate,c_initrandom);
}
