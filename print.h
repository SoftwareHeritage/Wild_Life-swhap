/* Copyright 1991 Digital Equipment Corporation.
** All Rights Reserved.
*****************************************************************/


typedef struct _tab_brk *       ptr_tab_brk;
typedef struct _item *          ptr_item;

typedef struct _tab_brk {
  int column;
  int broken;
  int printed;
} tab_brk;

typedef struct _item {
  char *str;
  ptr_tab_brk tab;
} item;

extern void init_print();
extern void pred_write();
extern void listing_pred_write();
extern int str_to_int();

extern int print_variables();
extern void print_resid_message();
extern void print_operator_kind();

extern void display_psi();
extern void display_psi_stdout();
extern void display_psi_stream();
extern void display_psi_stderr();

extern void print_code();

extern char *no_name;
extern char *buffer;

/* Global flags that modify how writing is done. */
extern int print_depth;
extern int indent;
extern int const_quote;
extern int write_stderr;
extern int write_corefs;
extern int write_resids;
