/* Copyright 1991 Digital Equipment Corporation.
** All Rights Reserved.
*****************************************************************/

extern char *heap_copy_string();
extern char *stack_copy_string();

extern ptr_node heap_insert();
extern ptr_node stack_insert();
extern ptr_node bk_stack_insert();
extern ptr_node bk2_stack_insert();
extern void heap_insert_copystr();
extern void stack_insert_copystr();

extern ptr_node find();

extern int intcmp();
extern int featcmp();

extern ptr_node find_data();

extern ptr_definition update_symbol();
