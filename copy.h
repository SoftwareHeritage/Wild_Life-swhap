/* Copyright 1991 Digital Equipment Corporation.
** All Rights Reserved.
**
** Last modified on Fri Sep  6 14:17:04 1991 by vanroy
**      modified on Fri Aug 23 16:36:08 1991 by herve 
**      modified on Tue Feb 26 17:42:52 GMT+1:00 1991 by rmeyer
*****************************************************************/

extern void init_copy();
extern void clear_copy();

extern ptr_psi_term exact_copy();
extern ptr_psi_term quote_copy();
extern ptr_psi_term eval_copy();
extern ptr_psi_term inc_heap_copy();

extern ptr_psi_term distinct_copy();
extern ptr_node distinct_tree();

extern void mark_quote();
extern void mark_quote_tree();
extern void mark_eval();
extern void mark_eval_tree();
extern void mark_nonstrict();
