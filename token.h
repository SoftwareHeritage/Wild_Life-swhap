/* Copyright 1991 Digital Equipment Corporation.
** All Rights Reserved.
*****************************************************************/

extern void psi_term_error();

extern int stdin_terminal;
extern void stdin_cleareof();
extern void begin_terminal_io();
extern void end_terminal_io();
extern char *expand_file_name();
extern int open_input_file();
extern int open_output_file();

extern int read_char();
extern int read_line();
extern void read_token();
extern void read_token_b();
extern int var_occurred;

extern void put_back_char();
extern void put_back_token();

/* Part of global input file state */
extern ptr_psi_term saved_psi_term;
extern ptr_psi_term old_saved_psi_term;
extern char saved_char;
extern int eof_flag;

/* File state ADT */
extern ptr_psi_term input_state;
extern ptr_psi_term stdin_state;
extern void save_state();
extern void restore_state();
extern void new_state();

/* Names of the features */
#define STREAM "stream"
#define INPUT_FILE_NAME "input_file_name"
#define LINE_COUNT "line_count"
#define START_OF_LINE "start_of_line"
#define SAVED_CHAR "saved_char"
#define OLD_SAVED_CHAR "old_saved_char"
#define SAVED_PSI_TERM "saved_psi_term"
#define OLD_SAVED_PSI_TERM "old_saved_psi_term"
#define EOF_FLAG "eof_flag"

/* Psi-term utilities */
extern void heap_add_int_attr();
extern void heap_mod_int_attr();
extern void heap_add_str_attr();
extern void heap_mod_str_attr();
extern void heap_add_psi_attr();
extern void stack_add_int_attr();
/* extern void stack_mod_int_attr(); */
extern void stack_add_str_attr();
/* extern void stack_mod_str_attr(); */
extern void stack_add_psi_attr();
extern FILE *get_stream();

/* For parsing from a string */
extern int stringparse;
extern char *stringinput;

/* Parser/tokenizer state handling */
extern void save_parse_state();
extern void restore_parse_state();
extern void init_parse_state();

typedef struct _parse_block *ptr_parse_block;

typedef struct _parse_block {
  int lc;
  int sol;
  char sc;
  char osc;
  ptr_psi_term spt;
  ptr_psi_term ospt;
  int ef;
} parse_block;
