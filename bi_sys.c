/* Copyright 1992 Digital Equipment Corporation
   All Rights Reserved
*/

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

#define copyPsiTerm(a,b)        (ptr_psi_term )memcpy(a,b,sizeof(psi_term))



/******** C_TRACE
  With no arguments: Toggle the trace flag & print a message saying whether
  tracing is on or off.
  With argument 1: If it is top, return the trace flag and disable tracing.
  If it is true or false, set the trace flag to that value.  Otherwise, give
  an error.
  With argument 2: If it is top, return the stepflag and disable stepping.
  If it is true or false, set the stepflag to that value.  Otherwise, give
  an error.
*/
int c_trace()
{
  int success=TRUE;
  ptr_psi_term t,arg1,arg2;

  t=aim->a;
  deref_args(t,set_empty);
  get_two_args(t->attr_list,&arg1,&arg2);
  if (arg1) {
    deref_ptr(arg1);
    if (is_top(arg1)) {
      unify_bool_result(arg1,trace);
      trace=FALSE;
    }
    else if (arg1->type==true)
      trace=TRUE;
    else if (arg1->type==false)
      trace=FALSE;
    else {
      Errorline("bad first argument in %P.\n",t);
      /* report_error(t,"bad first argument"); */
      success=FALSE;
    }
  }
  if (arg2) {
    deref_ptr(arg2);
    if (is_top(arg2)) {
      unify_bool_result(arg2,stepflag);
      stepflag=FALSE;
    }
    else if (arg2->type==true)
      stepflag=TRUE;
    else if (arg2->type==false)
      stepflag=FALSE;
    else {
      Errorline("bad second argument in %P.\n",t);
      /* report_error(t,"bad second argument"); */
      success=FALSE;
    }
  }
  if (!arg1 && !arg2)
    toggle_trace();
  return success;
}



int c_tprove()
{
  ptr_psi_term t,arg1,arg2;

  t=aim->a;
  deref_args(t,set_empty);
  set_trace_to_prove();
  return TRUE;
}



/******** C_STEP
  Toggle the single step flag & print a message saying whether
  single stepping mode is on or off.
*/
static int c_step()
{
  ptr_psi_term t;

  t=aim->a;
  deref_args(t,set_empty);
  toggle_step();
  return TRUE;
}

/******** C_VERBOSE
  Toggle the verbose flag & print a message saying whether
  verbose mode is on or off.
*/
static int c_verbose()
{
  ptr_psi_term t;

  t=aim->a;
  deref_args(t,set_empty);
  verbose = !verbose;
  printf("*** Verbose mode is turned ");
  printf(verbose?"on.\n":"off.\n");
  return TRUE;
}

/******** C_WARNING
  Toggle the warning flag & print a message saying whether
  warnings are printed or not.
  Default: print warnings.
  (Errors cannot be turned off.)
*/
static int c_warning()
{
  ptr_psi_term t;

  t=aim->a;
  deref_args(t,set_empty);
  warningflag = !warningflag;
  printf("*** Warnings are");
  printf(warningflag?"":" not");
  printf(" printed.\n");
  return TRUE;
}

/******** C_MAXINT
  Return the integer of greatest magnitude that guarantees exact
  integer arithmetic.
*/
static int c_maxint()
{
  ptr_psi_term t,result;
  REAL max,val;
  int num,success;
  
  t=aim->a;
  deref_args(t,set_empty);
  result=aim->b;
  deref_ptr(result);
  success=get_real_value(result,&val,&num);
  if (success) {
    if (num)
      success=(val==(REAL)MAXINT);
    else
      success=unify_real_result(result,(REAL)MAXINT);
  }
  return success;
}

/* 21.1 */
/******** C_QUIET
  Return the value of not(NOTQUIET).
*/
static int c_quiet()
{
  ptr_psi_term t,result,ans;
  int success=TRUE;
  
  t=aim->a;
  deref_args(t,set_empty);
  result=aim->b;
  deref_ptr(result);
  ans=stack_psi_term(4);
  ans->type = !NOTQUIET ? true : false ;
  push_goal(unify,result,ans,NULL);
  return success;
}

/******** C_CPUTIME
  Return the cpu-time in seconds used by the Wild_Life interpreter.
*/
static int c_cputime()
{
  ptr_psi_term result, t;
  REAL time,val;
  int num,success;
  
  t=aim->a;
  deref_args(t,set_empty);
  result=aim->b;
  deref_ptr(result);
  success=get_real_value(result,&val,&num);
  if (success) {
    times(&life_end);
    time=(life_end.tms_utime-life_start.tms_utime)/60.0;
    if (num)
      success=(val==time);
    else
      success=unify_real_result(result,time);
  }
  return success;
}

/******** C_REALTIME
  Return the time in seconds since 00:00:00 GMT, January 1, 1970.
  This is useful for building real-time applications such as clocks.
*/
static int c_realtime()
{
  ptr_psi_term result, t;
  REAL time,val;
  int num,success;
  struct timeval tp;
  struct timezone tzp;
  
  t=aim->a;
  deref_args(t,set_empty);
  result=aim->b;
  deref_ptr(result);
  success=get_real_value(result,&val,&num);
  if (success) {
    gettimeofday(&tp, &tzp);
    time=(REAL)tp.tv_sec + ((REAL)tp.tv_usec/1000000.0);
    /* time=times(&life_end)/60.0; */
    if (num)
      success=(val==time);
    else
      success=unify_real_result(result,time);
  }
  return success;
}

/******** C_LOCALTIME
  Return a psi-term containing the local time split up into year, month, day,
  hour, minute, second, and weekday.
  This is useful for building real-time applications such as clocks.
*/
static int c_localtime()
{
  ptr_psi_term result, t, psitime, t1,t2,t3,t4,t5,t6;
  int success=TRUE;
  struct timeval tp;
  struct timezone tzp;
  struct tm *thetime;
  
  t=aim->a;
  deref_args(t,set_empty);
  result=aim->b;
  deref_ptr(result);

  gettimeofday(&tp, &tzp);
  thetime=localtime(&(tp.tv_sec));

  psitime=stack_psi_term(4);
  psitime->type=timesym;
  stack_add_int_attr(psitime, year_attr,    thetime->tm_year+1900);
  stack_add_int_attr(psitime, month_attr,   thetime->tm_mon+1);
  stack_add_int_attr(psitime, day_attr,     thetime->tm_mday);
  stack_add_int_attr(psitime, hour_attr,    thetime->tm_hour);
  stack_add_int_attr(psitime, minute_attr,  thetime->tm_min);
  stack_add_int_attr(psitime, second_attr,  thetime->tm_sec);
  stack_add_int_attr(psitime, weekday_attr, thetime->tm_wday);

  push_goal(unify,result,psitime,NULL);

  return success;
}

/******** C_STATISTICS
  Print some information about Wild_Life: stack size, heap size, total memory.
*/
static int c_statistics()
{
  ptr_psi_term t;
  int success=TRUE;
  int t1,t2,t3;

  t=aim->a;
  deref_args(t,set_empty);

  t1 = sizeof(mem_base)*(stack_pointer-mem_base);
  t2 = sizeof(mem_base)*(mem_limit-heap_pointer);
  t3 = sizeof(mem_base)*(mem_limit-mem_base);

  printf("\n");
  /* printf("************** SYSTEM< INFORMATION **************\n"); */
  printf("Stack size  : %8d bytes (%5dK) (%d%%)\n",t1,t1/1024,100*t1/t3);
  printf("Heap size   : %8d bytes (%5dK) (%d%%)\n",t2,t2/1024,100*t2/t3);
  printf("Total memory: %8d bytes (%5dK)\n",t3,t3/1024);

#ifdef X11
  printf("X predicates are installed.\n");
#else
  printf("X predicates are not installed.\n");
#endif
  
  /* printf("\n"); */
  /* printf("************************************************\n"); */
  return success;
}


/******** C_GARBAGE
  Force a call to the garbage collector.
*/
static int c_garbage()
{
  ptr_psi_term t;

  t=aim->a;
  deref_args(t,set_empty);
  garbage();
  return TRUE;
}

/******** C_SYSTEM
  Pass a string to shell for execution. Return the value as the result.
*/
static int c_system()
{
  int success=TRUE;
  ptr_psi_term arg1,arg2,funct,result;
  REAL value;
  int smaller;
  
  funct=aim->a;
  deref_ptr(funct);
  result=aim->b;
  get_two_args(funct->attr_list,&arg1,&arg2);
  if(arg1) {
    deref(arg1);
    deref_args(funct,set_1);
    if(success=matches(arg1->type,quoted_string,&smaller))
      if(arg1->value) {
	value=(REAL)system(arg1->value);
	if(value==127) {
	  success=FALSE;
          Errorline("could not execute shell in %P.\n",funct);
	  /* report_error(funct,"couldn't execute shell"); */
	}
	else
	  success=unify_real_result(result,value);
      }
      else
	residuate(arg1);
    else {
      success=FALSE;
      Errorline("bad argument in %P.\n",funct);
      /* report_error(funct,"bad argument"); */
    }
  }
  else
    curry();
  
  return success;
}

/******** C_ENCODE
  Force type encoding.
  This need normally never be called by the user.
*/
static int c_encode()
{
  ptr_psi_term t;

  t=aim->a;
  deref_args(t,set_empty);
  encode_types();
  return TRUE;
}

static GENERIC unitListElement;

void setUnitList(x)
GENERIC x;
{
	unitListElement = x;
}

ptr_psi_term unitListValue()
{
	return makePsiTerm(unitListElement);
}

GENERIC unitListNext()
{
	unitListElement = NULL;
	return NULL;
}

ptr_psi_term intListValue(p)
ptr_int_list p;
{
	return makePsiTerm(p->value);
}

GENERIC intListNext(p)
ptr_int_list p;
{
	return (GENERIC )(p->next);
}

ptr_psi_term quotedStackCopy(p)
ptr_psi_term p;
{
	ptr_psi_term q;

	q = stack_copy_psi_term(p);
	mark_quote(q);
	return q;
}

/* Return a ptr to a psi-term marked as  evaluated.  The psi-term is a copy at
 * the top level of the goal residuated on p, with the rest of the psi-term
 * shared.
 */

ptr_psi_term residListGoalQuote(p)
ptr_residuation p;
{
	ptr_psi_term psi;

	psi = stack_psi_term(4);
	copyPsiTerm(psi, p->goal->a);
	psi->status = 4;
	return psi;
}

GENERIC residListNext(p)
ptr_residuation p;
{
	return (GENERIC )(p->next);
}

ptr_psi_term makePsiTerm(x)
ptr_definition x;
{
	ptr_psi_term p;
	
	p = stack_psi_term(4);
	p->type = x;
	return p;
}

ptr_psi_term makePsiList(head, valueFunc, nextFunc)
GENERIC head;
ptr_psi_term (*valueFunc)();
GENERIC (*nextFunc)();
{
	ptr_psi_term phead;
	ptr_list l;

	phead = stack_psi_term(4);
	phead->type = alist;
	phead->value = (GENERIC)(l=STACK_ALLOC(list));
	l->car = NULL;				/* just in case head is NULL */
	l->cdr = NULL;
	while (head)
	{
		l->car = (*valueFunc)(head);
		head = (*nextFunc)(head);
		if (head)
		{
			l->cdr = makePsiTerm(alist);
			l->cdr->value = (GENERIC)(STACK_ALLOC(list));
			l = (ptr_list )l->cdr->value;
			l->cdr = NULL;
		}
	}
	return phead;
}



/******** C_ResidList
  rlist(A) ->  list all eval/prove goals residuated on variable 'A'.
*/
static int c_residList(x)
int x;
{
	ptr_psi_term func;
	ptr_psi_term result,arg1, other;
	ptr_residuation p;
	
	func = aim->a;
	deref_ptr(func);

	get_one_arg(func->attr_list, &arg1);
	if (!arg1)
	{
		curry();
		return TRUE;
	}
	
	result = aim->b;
	deref(result);
	deref_ptr(arg1);
	deref_args(func, set_1);

	other = makePsiList(arg1->resid, residListGoalQuote, residListNext);
	resid_aim = NULL;
	push_goal(unify,result,other,NULL);
	return TRUE;
}

ptr_goal makeGoal(p)
ptr_psi_term p;
{
	ptr_goal old = goal_stack;
	ptr_goal g;
	
	push_goal(prove, p, DEFRULES, NULL);
	g = goal_stack;
	g->next=NULL;
	goal_stack = old;
	return g;
}

/******** C_residuate
  residuate(A,B) ->  residuate goal B on variable A, non_strict in both args
*/
static int c_residuate()
{
	ptr_psi_term pred;
	ptr_psi_term arg1, arg2;
	ptr_residuation p;
	ptr_goal g;
	
	pred = aim->a;
	deref_ptr(pred);

	get_two_args(pred->attr_list, &arg1, &arg2);
	if ((!arg1)||(!arg2)) {
	  Errorline("%P requires two arguments.\n",pred);
	  return FALSE;
        }
	
	deref_ptr(arg1);
	deref_ptr(arg2);
	deref_args(pred, set_1_2);

	g = makeGoal(arg2);
	residuateGoalOnVar(g, arg1, NULL);
	
	return TRUE;
}

/******** C_mresiduate
  Multiple-variable residuation of a predicate.
  mresiduate(A,B) ->  residuate goal B on a list of variables A, non_strict in
  both args.  If any of the variables is bound the predicate is executed.
  The list must have finite length.
*/
static int c_mresiduate()
{
	int is_list, success=TRUE;
	ptr_psi_term pred;
	ptr_psi_term arg1, arg2, tmp;
	ptr_residuation p;
	ptr_goal g;
	
	pred = aim->a;
	deref_ptr(pred);

	get_two_args(pred->attr_list, &arg1, &arg2);
	if ((!arg1)||(!arg2)) {
	  Errorline("%P requires two arguments.\n",pred);
	  return FALSE;
        }
	
	deref_ptr(arg1);
	deref_ptr(arg2);
	deref_args(pred, set_1_2);

	g = makeGoal(arg2);

	/* First check that arg1 is a list: */
	tmp = arg1;
	is_list = TRUE;
	while (tmp && is_list) {
	  deref_ptr(tmp);
	  if (overlap_type(tmp->type,alist)) {
	    if (tmp->value)
	      tmp = ((ptr_list)tmp->value)->cdr;
            else
	      is_list=FALSE;
	  }
	  else
	    is_list=FALSE;
	}
	/* Then residuate on all the list variables: */
	if (is_list) {
	  tmp = arg1;
	  while (tmp) {
	    ptr_list l;
	    ptr_psi_term var;

	    deref_ptr(tmp);
	    l = (ptr_list)tmp->value;
	    var = l->car;
	    tmp = l->cdr;
	    if (var) {
	      deref_ptr(var);
	      residuateGoalOnVar(g, var, NULL);
	    }
	  }
	}
	else {
	  Errorline("%P should be a nil-terminated list in mresiduate.\n",arg1);
	  success=FALSE;
	}
	
	return success;
}

void insert_system_builtins()
{
  new_built_in("trace",predicate,c_trace);
  new_built_in("step",predicate,c_step);
  new_built_in("verbose",predicate,c_verbose);
  new_built_in("warning",predicate,c_warning);
  new_built_in("*quiet*",function,c_quiet); /* 21.1 */
  new_built_in("maxint",function,c_maxint);
  new_built_in("cputime",function,c_cputime);
  new_built_in("realtime",function,c_realtime);
  new_built_in("localtime",function,c_localtime);
  new_built_in("statistics",predicate,c_statistics);
  new_built_in("gc",predicate,c_garbage);
  new_built_in("system",function,c_system);
  new_built_in("encode",predicate,c_encode);
  new_built_in("rlist",function,c_residList);
  new_built_in("residuate",predicate,c_residuate);
  new_built_in("mresiduate",predicate,c_mresiduate);
  new_built_in("tprove",predicate,c_tprove);
}
