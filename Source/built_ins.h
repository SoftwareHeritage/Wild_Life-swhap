/* Copyright 1991 Digital Equipment Corporation.
** All Rights Reserved.
*****************************************************************/

extern void init_built_in_types();

extern long check_real();
extern long get_real_value();
extern long unify_real_result();
extern void unify_bool_result();

extern void new_built_in();

extern long file_exists();
extern void exit_life();
extern long abort_life();
extern long c_abort();

ptr_psi_term stack_nil();
ptr_psi_term stack_cons();

ptr_psi_term collect_symbols();



/* used by collect_symbols */

#define least_sel 0
#define greatest_sel 1
#define op_sel 2

ptr_psi_term makePsiTerm ARGS((ptr_definition x));
ptr_psi_term makePsiList ARGS((GENERIC head, ptr_psi_term (*valueFunc)(), \
                               GENERIC (*nextFunc)()));

/* functions for accessing next and value fields of some structures */

ptr_psi_term intListValue();
GENERIC intListNext();
ptr_psi_term residListGoal();
GENERIC residListNext();
GENERIC unitListNext ARGS(());
ptr_psi_term unitListValue ARGS(());
void setUnitList ARGS((GENERIC x));
