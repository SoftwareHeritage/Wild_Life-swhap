/* Copyright 1991 Digital Equipment Corporation.
** All Rights Reserved.
*****************************************************************/

#include <stdio.h>
#include <strings.h>
#include <math.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <sys/times.h>
#include <time.h>
#include <assert.h>
#include <errno.h>
#include <setjmp.h>

/* Time stamp technique */
#define TS

/*************************** CONSTANTS **************************/

/* Enable looking first for local set_up file */
/* In the final release, LOCALSETUP should be undefined. */
#define LOCALSETUP
#define LOCALSETUPFILE	"./.set_up"

/* MEM_SIZE is the amount of memory allotted as program data-space. */
#ifdef MICROLIFE
/* Small version for testing garbage collector */
#define MEM_SIZE (1500000) /* number of bytes */
#else
#define MEM_SIZE (2*2048000) /* number of bytes */
#endif

/* Garbage collection threshold (1/8 of MEM_SIZE is reasonable). */
#define GC_THRESHOLD (MEM_SIZE/32) /* number of words (4 bytes) */

/* Copy threshold (1/8 of GC_THRESHOLD is reasonable) */
#define COPY_THRESHOLD (GC_THRESHOLD/8)

/* Which C type to use to represent reals and integers in Wild_Life. */
#define REAL double

/* Maximum exactly representable integer (2^53-1 for double IEEE format) */
#define MAXINT 9007199254740991.0

/* Maximum number of tokens in a pretty-printed output term. */
#define PRETTY_SIZE 20000

/* Maximum number of built_ins */
#define MAX_BUILT_INS 255

/* Maximum size of file names and input tokens (which includes input strings) */
/* (Note: calculated tokens can be arbitrarily large) */
#define STRLEN 10000

/* Initial page width for printing */
#define PAGE_WIDTH 80

/* Initial depth limit for printing */
#define PRINT_DEPTH 1000000000

/* Power of ten to split printing (REALs are often more precise than ints) */
#define PRINT_SPLIT 1000000000
#define PRINT_POWER 9

/* Maximum depth of the parser stack */
/* = maximum depth of embedded brackets etc... */
#define PARSER_STACK_SIZE 10000

/* Maximum operator precedence */
#define MAX_PRECEDENCE 1200

/* Size of print buffer */
#define PRINT_BUFFER 100000

/* Head of prompt */
#define PROMPT "> "

/* Size of prompt buffer */
#define PROMPT_BUFFER 200
#define MAX_LEVEL ((PROMPT_BUFFER-4-strlen(PROMPT))/2)

/* Maximum number of goals executed between event polling */
/* Ideally, this should be a function of machine speed. */
#define XEVENTDELAY 1000

/* Maximum goal indentation during tracing */
#define MAX_TRACE_INDENT 40

#define HEAP_ALLOC(A) (A *)heap_alloc(sizeof(A))
#define STACK_ALLOC(A) (A *)stack_alloc(sizeof(A))

/* True flags for the flags field of psi-terms */
#define QUOTED_TRUE   1
#define UNFOLDED_TRUE 2

/* Standard booleans */
#define TRUE      1
#define FALSE     0
#define TRUEMASK  1

#define NOT_CODED 0
#define UN_CODED (CODE)0

/* Must be different from NULL, a built-in index, and a pointer */
/* Used to indicate that the rules of the definition are needed. */
#define DEFRULES  -1

#define EOLN 10

/* How many types can be encoded on one integer */
/* in the transitive closure encoding. */
#define INT_SIZE 8*sizeof(int)

/* Flags to indicate heap or stack allocation */
#define HEAP TRUE
#define STACK FALSE

/* Kinds of user inputs */
#define FACT 100
#define QUERY 200
#define ERROR 999

/* Bit masks for status field of psi-terms: RMASK is used as a flag to */
/* avoid infinite loops when tracing psi-terms, SMASK masks off the    */
/* status bits.  These are used in the 'mark' routines (copy.c) and in */
/* check_out. */
#define RMASK 256
#define SMASK 255

/* Initial value of time stamp (for variable binding) */
#ifdef TS
#define INIT_TIME_STAMP 1
#endif
  
/******************************** MACROS *******************************/

/* *** Macros for the tokenizer, define the types of ASCII characters. */

#define DIGIT(C) (C>='0' && C<='9')

#define UPPER(C) ((C>='A' && C<='Z') || C=='_')

#define LOWER(C) (C>='a' && C<='z')

#define ALPHA(C) (DIGIT(C) || UPPER(C) || LOWER(C))

/* Must be single-character tokens (unless surrounded by quotes) */
/* The chars '.', '?', and '`' have been added */
#define SINGLE(C) (C=='(' || C==')' || C=='[' || C==']' || C=='{' || C=='`' ||\
                   C=='}' || C==',' || C=='.' || C=='?' || C==';' || C=='@')

/* Can be components of multi-character tokens */
#define SYMBOL(C) (C=='!' || C=='#' || C=='$' || C=='%' || C=='&' ||\
                   C=='*' || C=='+' || C=='-' || C=='>' || C=='/' ||\
                   C==':' || C=='<' || C=='=' ||\
                   C=='~' || C=='^' || C=='|' || C=='\\')

/* Returns TRUE iff psi_term A is equal to string B. */
/* This cannot be used on encoded types.  */
#define equ_tok(A,B) (!strcmp(A.type->symbol,B))
#define equ_tok3(A,B,Q) (Q?FALSE:equ_tok(A,B))

/* Returns TRUE iff psi_term A is equal to character B. */
#define equ_tokch(A,B) (A.type->symbol[0]==B && A.type->symbol[1]==0)
#define equ_tokch3(A,B,Q) (Q?FALSE:equ_tokch(A,B))

/* Returns TRUE iff psi_term A is equal to character B. */
/* Handles also the case where B may be NULL, i.e. A must be empty */
#define equ_tokc(A,B) (B?equ_tokch(A,B):A.type->symbol[0]==0)
#define equ_tokc3(A,B,Q) (Q?FALSE:equ_tokc(A,B))

/* *** Other macros. */

/* The cut operation */
/* This ensures that a cut is below choice_stack. */
/*
#define cut_to(C) if ((ptr_choice_point)(C)<=choice_stack) { \
                       choice_stack=(ptr_choice_point)(C); \
                  }
*/

/* 13.1 */
/* New choice_stack value must be a valid choice point, i.e. not garbage */
#define cut_to(C) { ptr_choice_point cp=choice_stack; \
		    while ((GENERIC)cp>(GENERIC)(C)) cp=cp->next; \
		    choice_stack=cp; \
                  }

/* The basic dereference operation. */
/* P must be a pointer to a psi_term.  */
/* (For the other dereference routines, see lefun.c) */
#define deref_ptr(P) while(P->coref) P=P->coref

/* Predicates defined in Life whose args should not be evaluated. */
#define noneval(T) (T->type==quote || T->type==listingsym || T->type==loadsym)

/* CONSTant used to be a function, */
/* returns TRUE if psi_term S is a constant.  */
#define const(S) ((S).value==NULL && (S).type!=variable)

#define equal_types(A,B) ((A)==(B))

#define is_top(T) ((T)!=NULL && (T)->type==top && (T)->attr_list==NULL)

/* Object is inside Life data space */
#define VALID_RANGE(A) ((GENERIC)A>=mem_base && (GENERIC)A<mem_limit)

/* Object has valid address to be modified in garbage collector */
#ifdef X11
#define VALID_ADDRESS(A) (  VALID_RANGE(A) \
                         || (GENERIC)A==(GENERIC)&xevent_list \
                         || (GENERIC)A==(GENERIC)&xevent_existing \
                         || (GENERIC)A==(GENERIC)&var_tree \
                         )
#else
#define VALID_ADDRESS(A) (  VALID_RANGE(A) \
                         || (GENERIC)A==(GENERIC)&var_tree \
                         )
#endif

/******************************* TYPES ************************************/

/* GENERIC is the type of a pointer to any type.  This might not work on */
/* some machines, but it should be possible as MALLOC() uses something of */
/* that kind.  ANSI uses "void *" instead.  */

typedef int *                     GENERIC;
typedef char                      string[STRLEN];
typedef struct _operator_data *   ptr_operator_data;
typedef struct _int_list *        ptr_int_list;
typedef struct _resid_list *      ptr_resid_list; /* 21.9 */
typedef struct _definition *      ptr_definition;
typedef struct _residuation *     ptr_residuation;
typedef struct _psi_term *        ptr_psi_term;
typedef struct _node *            ptr_node;
typedef struct _pair_list *       ptr_pair_list;
typedef struct _triple_list *     ptr_triple_list;
typedef struct _list *            ptr_list;
typedef struct _stack *           ptr_stack;
typedef struct _goal *            ptr_goal;
typedef struct _choice_point *    ptr_choice_point;

/****************************** DATA STRUCTURES **************************/

/* Definition of an operator */
typedef enum { nop, xf, fx, yf, fy, xfx, /* yfy, */ xfy, yfx } operator;

typedef struct _operator_data {
  operator type;
  int precedence;
  ptr_operator_data next;
} operator_data;

/* List of integers or pointers */
typedef struct _int_list {
  GENERIC value;
  ptr_int_list next;
} int_list;

/* List of residuation variables */ /* 21.9 */
typedef struct _resid_list { 
  ptr_psi_term var;
  ptr_psi_term othervar; /* needed for its sort only */
  ptr_resid_list next;
} resid_list;

typedef enum { undef, predicate, function, type } def_type;

/* Definition of a symbol. */
/* This includes the rules associated to the symbol and how old they are.  */
typedef struct _definition {
  int date; 
  char *symbol;
  ptr_pair_list rule;
  ptr_triple_list properties;

  ptr_int_list code;
  ptr_int_list parents;
  ptr_int_list children;

  def_type type;
  char always_check;  /* TRUE by default */
  char protected;     /* TRUE by default */
  char evaluate_args; /* TRUE by default */
  char already_loaded; /* Cleared at the prompt, set upon loading */

  ptr_operator_data op_data;
} definition;

/* 22.9 */
typedef struct _residuation {
  char eqflag; /* 20.1 */
  char sortflag; /* 20.1 */ /* bestsort == if TRUE ptr_definition else ptr_int_list */
  GENERIC bestsort; /* 21.9 */
  GENERIC value; /* to handle psi-terms with a value field 6.10 */
  ptr_goal goal;
  ptr_residuation next;
} residuation;

/* PSI_TERM */
typedef struct _psi_term {
#ifdef TS
  unsigned int time_stamp; /* Avoid multiple trailing on a choice point. 9.6 */
#endif
  ptr_definition type;
  int status; /* Indicates whether the properties of the type have been */
              /* checked or the function evaluated */
  /* int curried; Distinguish between quoted and curried object 20.5 */
  /* 13.1 moved flags from here */
  int flags; /* 14.9 */ /* 13.1 moved flags to here */
  GENERIC value;
  ptr_node attr_list;
  ptr_psi_term coref;
  ptr_residuation resid; /* List of goals to prove if type is narrowed. */
} psi_term;

/* Binary tree node. */
/* KEY can be either an integer (a pointer) or a pointer to a string. */
/* DATA is the information accessed under the KEY, in most cases a pointer */
/* to a PSI-TERM.  */

typedef struct _node {
  char *key;
  ptr_node left;
  ptr_node right;
  GENERIC data;
} node;

typedef struct _pair_list {
  ptr_psi_term a;
  ptr_psi_term b;
  ptr_pair_list next;
} pair_list;

/* Used for type properties */
typedef struct _triple_list {
  ptr_psi_term a;   /* Attributes */
  ptr_psi_term b;   /* Constraint */
  ptr_definition c; /* Original type of attribute & constraint */
  ptr_triple_list next;
} triple_list;

typedef struct _list {
  ptr_psi_term car;
  ptr_psi_term cdr;
} list;

/* Used to identify the object on the undo_stack */
/* Use define instead of enums because quick masking is important */
typedef int type_ptr;
#define psi_term_ptr	0
#define resid_ptr	1
#define int_ptr		2
#define char_ptr       10 /* 20.1 */
#define def_ptr		3
#define code_ptr	4
#define goal_ptr	5
#define cut_ptr         6 /* 22.9 */
#define destroy_window	7+32 /* To backtrack on window creation */
#define show_window     8+32 /* To backtrack on show window */
#define hide_window     9+32 /* To backtrack on hide window */
#define undo_action	  32 /* Fast checking for an undo action */

typedef struct _stack {
  type_ptr type; 
  GENERIC a;
  GENERIC b;
  ptr_stack next;
} stack;

typedef enum {
  fail,
  prove,
  unify,
  unify_noeval,
  disj,
  what_next,
  eval,
  eval_cut,
  freeze_cut,
  implies_cut,
  general_cut,
  match,
  type_disj,
  clause,
  del_clause,
  retract,
  load
} goals;

typedef struct _goal {
  goals type;
  ptr_psi_term a;
  ptr_psi_term b;
  GENERIC c;
  ptr_goal next;
  int pending;
} goal;

typedef struct _choice_point {
  unsigned int time_stamp;
  ptr_stack undo_point;
  ptr_goal goal_stack;
  ptr_choice_point next;
  GENERIC stack_top;
} choice_point;

/***************************** EXTERNAL VARIABLES ************************/

extern jmp_buf env;

/* Memory-manager variables. */
/* Garbage collection is done when HEAP_POINTER-STACK_POINTER<MEM_LIMIT. */

extern GENERIC mem_base;
extern GENERIC heap_pointer;
extern GENERIC mem_limit;
extern GENERIC stack_pointer;

extern float garbage_time;
extern struct tms life_start,life_end;

extern GENERIC other_base;
/* extern GENERIC other_limit; 21.12 */
/* extern GENERIC other_pointer; 21.12 */

extern ptr_node symbol_table;
extern ptr_psi_term error_psi_term;
extern int parser_stack_index;

extern ptr_node var_tree;
extern ptr_node printed_vars;
extern ptr_node printed_pointers;
extern ptr_node pointer_names;
extern int gen_sym_counter;

extern int warningflag;
extern int verbose;
extern int trace,noisy;
extern int types_done;
extern int interrupted;

extern FILE *input_stream;
extern int line_count;
extern string input_file_name;
extern FILE *output_stream;
extern char *prompt;
extern int page_width;

/* extern ptr_psi_term empty_list; 5.8 */
extern ptr_definition *gamma_table;
extern int type_count;
extern int types_modified;

extern int main_loop_ok;
extern ptr_goal aim;
extern ptr_goal goal_stack;
extern ptr_choice_point choice_stack;
/* extern ptr_choice_point prompt_choice_stack; 12.7 */
extern ptr_stack undo_stack;
#ifdef TS
extern unsigned int global_time_stamp; /* 9.6 */
#endif

extern int assert_first;
extern int assert_ok;
extern int file_date;

/* The following variables are used to make built-in type comparisons */
/* as fast as possible.  They are defined in built_ins.c.  */
extern ptr_definition abortsym; /* 26.1 */
extern ptr_definition aborthooksym; /* 26.1 */
extern ptr_definition and;
extern ptr_definition apply;
extern ptr_definition boolean;
extern ptr_definition boolsym;
extern ptr_definition built_in;
extern ptr_definition colonsym;
extern ptr_definition commasym;
extern ptr_definition comment;
/* extern ptr_definition conjunction; 19.8 */
extern ptr_definition constant;
extern ptr_definition cut;
extern ptr_definition disjunction;
extern ptr_definition eof;
extern ptr_definition eqsym;
extern ptr_definition false;
extern ptr_definition funcsym;
extern ptr_definition functor;
extern ptr_definition iff;
extern ptr_definition integer;
extern ptr_definition alist;
extern ptr_definition list_object;
extern ptr_definition nothing;
extern ptr_definition predsym;
extern ptr_definition quote;
extern ptr_definition quoted_string;
extern ptr_definition real;
extern ptr_definition stream;
extern ptr_definition succeed;
extern ptr_definition such_that;
extern ptr_definition top;
extern ptr_definition timesym;
extern ptr_definition tracesym; /* 26.1 */
extern ptr_definition true;
extern ptr_definition typesym;
extern ptr_definition variable;
extern ptr_definition opsym;
extern ptr_definition loadsym;
extern ptr_definition dynamicsym;
extern ptr_definition staticsym;
extern ptr_definition encodesym;
extern ptr_definition listingsym;
extern ptr_definition provesym;
extern ptr_definition delay_checksym;
extern ptr_definition eval_argsym;
extern ptr_definition inputfilesym;
extern ptr_definition call_handlersym;
extern ptr_definition xf_sym;
extern ptr_definition fx_sym;
extern ptr_definition yf_sym;
extern ptr_definition fy_sym;
extern ptr_definition xfx_sym;
extern ptr_definition xfy_sym;
extern ptr_definition yfx_sym;
extern ptr_definition nullsym;

extern ptr_psi_term null_psi_term; /* Used to represent an empty parse token */

extern char *one;
extern char *two;
extern char *year_attr;
extern char *month_attr;
extern char *day_attr;
extern char *hour_attr;
extern char *minute_attr;
extern char *second_attr;
extern char *weekday_attr;

/************************* EXTERNAL FUNCTIONS *************************/

extern void init_system(); /* in life.c */ /* 26.1 */

extern int (* c_rule[])(); /* in built_ins.c */

extern ptr_psi_term stack_psi_term(); /* in lefun.c */
extern ptr_psi_term real_stack_psi_term(); /* in lefun.c */
extern ptr_psi_term heap_psi_term(); /* in lefun.c */
extern ptr_psi_term stack_empty_list(); /* in lefun.c */

/**********************************************************************/

/* include files that everyone needs */
#include "types.h"
#include "error.h"

/************ VarArg compatibility definitions ************************/

/*
 * Author: 		Seth Copen Goldstein
 * Version:		11
 * Creation Date:	Tue May 26 16:31:09 1992
 * Filename:		seth.h
 * History:
*/

#if !defined(_SETH_H_FILE_)
#define _SETH_H_FILE_

#include <varargs.h>

/* function protoype macros for ansi and old compilers */

#if defined(__STDC__) || defined(ds3100)
# define	ARGS(args)	args
#else
# define	ARGS(args)	()
#endif

/* varargs macros that understand the difference between stdargs and varargs */

#define VarArgBase	va_alist
#ifdef m88k
# define VarArgBaseDecl	va_type va_alist
#else
# define VarArgBaseDecl	int va_alist
#endif
#define VarArg		___va_lp___
#define VarArgDecl	va_list VarArg
/* Added last condition -- see Maurice Keulen */
#if defined(_VARARGS_H) || defined(_VARARGS_) || \
    defined(_sys_varargs_h) || defined(_H_VARARGS) /* 21.12 */
# define VarArgInit(l)	va_start(VarArg)
#else
# define VarArgInit(l)	va_start(VarArg, l)
#endif
#define VarArgNext(t)	va_arg(VarArg, t)
#define VarArgEnd()	va_end(VarArg)

#if 0
/* example usage of vararg macros */

foo(var1, var2, VarArgBase)	/* VarArgBase must be last parameter */
type var1;
type var2;
VarArgBaseDecl;			/* must have this as last decl */
{
	VarArgDecl;		/* declares variable that will be used to
				 * run down the list of arguments starting at
				 * VarArgBase
				 */
	typename var3;		/* example variable that gets one of the
				 * arguments from the argument list
				 */

	VarArgInit(var2);	/* MUST BE CALLED BEFORE ACCESSING THE
				 * ARGUMENTS, the parameter to this macro is
				 * ALWAYS the parameter preceding VarArgBase
				 */
	

	/* usage to send argument list to one of the v-printf functions */
	
	vfprintf(of, format, VarArg);

	/* usage to get an element off the argument list */
	
	var3 = VarArgNext(typename);

	/* for saftey sake use this to finish up */

	VarArgEnd();
}
#endif

#endif

/**********************************************************************/
