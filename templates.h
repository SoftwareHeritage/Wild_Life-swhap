/* Copyright 1991 Digital Equipment Corporation.
** All Rights Reserved.
*****************************************************************/


/* constants */

#define MAXNBARGS 20


/* defined in templates.c */

extern char *numbers[];
extern int set_extra_args[];
extern int get_arg ();


/* macros */

#define include_var_builtin(NBARGS) \
        ptr_psi_term g, args[NBARGS]; \
	int num[NBARGS]; \
	long val[NBARGS]; \
	int ii, success=TRUE, resi=FALSE


#define begin_builtin(FUNCNAME, NBARGS, NBARGSIN, TYPES) \
    if (NBARGS > MAXNBARGS) \
        Errorline ("in template: you have to increase MAXNBARGS at least to %d !\n", NBARGS); \
    \
    g=aim->a; \
    deref_ptr(g); \
    \
    for (ii = 0; success && ii < NBARGS; ii++) \
        success = get_arg (g, &args[ii], numbers[ii]); \
    \
    if (success) \
    { \
	for (ii = 0; ii < NBARGS; ii++) \
	    deref (args[ii]); \
    \
	deref_args (g, set_extra_args [NBARGS+1]); \
    \
	for (ii = 0; success && ii < NBARGS; ii++) \
	{ \
	    success = matches (args[ii]->type, types[ii], &num[ii]); \
	    if (args[ii]->value != NULL && num[ii]) \
	        if (types[ii] == integer) \
		    val[ii] = *(int *) args[ii]->value; \
		else \
		if (types[ii] == real) \
		    val[ii] = *(REAL *) args[ii]->value; \
		else \
		if (types[ii] == quoted_string) \
		    val[ii] = (long) args[ii]->value; \
		else \
		    Errorline ("in template: type %T not expected (built-in FUNCNAME).\n", types[ii]); \
	    else \
		if (args[ii]->type == true) \
		    val[ii] = TRUE; \
		else \
		if (args[ii]->type == false) \
		    val[ii] = FALSE; \
		else \
		if (args[ii]->type == xwindow || args[ii]->type == xpixmap) \
		    val[ii] = GetIntAttr (args[ii], "id"); \
		else \
		    num[ii] = FALSE; /* force the residuation */ \
	} \
    \
	if (success) \
	{ \
	    for (ii = 0; ii < NBARGSIN; ii++) \
	        if (args[ii]->resid != NULL || !num[ii]) \
		{ \
		    residuate (args[ii]); \
		    resi = TRUE; \
		} \
    \
	    if (success && !resi) \
	    {


#define end_builtin() \
            } \
        } \
	else \
            Errorline ("bad arguments in %P.\n", g); \
    } \
    else \
        Errorline ("missing arguments in %P.\n", g); \
    \
    return success; 

