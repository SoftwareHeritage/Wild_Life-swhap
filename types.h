/* Copyright 1991 Digital Equipment Corporation.
** All Rights Reserved.
*****************************************************************/

#ifndef _TYPES_H_
#define _TYPES_H_

extern int types_modified;
extern int type_count;

extern int redefine();

extern void assert_type();
extern void assert_complicated_type();
extern void print_codes();

extern void assert_protected();
extern void assert_delay_check();
extern void assert_args_not_eval();
extern void clear_already_loaded();
extern void inherit_always_check();

extern int glb();
extern int glb_code();
extern int glb_value();
extern int sub_type();
extern int overlap_type();
extern int matches();

extern ptr_int_list decode();

extern void print_def_type();

ptr_int_list lub();
void or_codes();
ptr_int_list copyTypeCode();

#endif
