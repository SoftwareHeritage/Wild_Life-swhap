/* Copyright 1991 Digital Equipment Corporation.
** All Rights Reserved.
*****************************************************************/

#include "extern.h"
#include "trees.h"
#include "print.h"
#include "parser.h"
#include "info.h"
#include "login.h"
#include "lefun.h"
#include "built_ins.h"
#include "types.h"
#include "copy.h"
#include "token.h"
#include "interrupt.h"
#include "error.h"

#ifdef X11
#include "xpred.h"
#endif

int noisy=TRUE;
int file_date=3;
int types_done=FALSE;

struct tms life_start,life_end;
float garbage_time=0;

int arg_c;
char **arg_v;



void exit_if_true(exitflag)
int exitflag;
{
  if (exitflag) {
    Errorline("\n\n*** Execution is not allowed to continue.\n"); /* 21.1 */
    exit_life(TRUE);
  }
}



/* I/O initialization */
void init_io()
{
  struct stat buffer;

  fstat(fileno(stdin), &buffer);
  /* True iff stdin is from a terminal */
  stdin_terminal=(S_IFCHR & buffer.st_mode)!=0;
  input_state=NULL;
  stdin_state=NULL;
  output_stream=stdout;
}



/* Initial state of system to begin a query */
void init_system()
{
#ifdef X11
  x_window_creation=FALSE;
#endif
  stack_pointer=mem_base;
  goal_stack=NULL;
  choice_stack=NULL;
  undo_stack=NULL; /* 7.8 */
  var_tree=NULL;
  prompt=PROMPT;
  resid_aim=NULL;
  exit_if_true(!memory_check());
}



/******** MAIN(argc,argv)
This routine contains the Read-Solve-Print loop.
*/
main(argc, argv)
int argc;
char **argv;
{
  ptr_psi_term s;  
  ptr_stack save_undo_stack;
  int sort,exitflag;
  int c; /* 21.12 (prev. char) */ 
  
  arg_c=argc;
  arg_v=argv;
  
  quietflag = (argc>=2) ? !strcmp(argv[1],"-q") : FALSE; /* 21.1 */
  init_io();
  init_memory();
  exit_if_true(!mem_base || !other_base);
  assert(stack_pointer==mem_base); /* 8.10 */
  init_copy();
  assert(stack_pointer==mem_base); /* 8.10 */
  init_print();
  assert(stack_pointer==mem_base); /* 8.10 */

  /* Timekeeping initialization */
  tzset();
  times(&life_start);
  assert(stack_pointer==mem_base); /* 8.10 */

  init_built_in_types();
  assert(stack_pointer==mem_base); /* 8.10 */
#ifdef X11
  x_setup_builtins();
  assert(stack_pointer==mem_base); /* 8.10 */
#endif
  init_interrupt();
  assert(stack_pointer==mem_base); /* 8.10 */
  title();
  assert(stack_pointer==mem_base); /* 8.10 */
  init_trace();
  noisy=FALSE;

  assert(stack_pointer==mem_base); /* 8.10 */
  /* Read in the .set_up file */
  init_system();
  open_input_file("+SETUP+");
  push_goal(load,input_state,file_date,heap_copy_string("+SETUP+"));
  file_date+=2;
  main_prove();

  /* Main loop of interpreter */
  do {
    setjmp(env);
    /* printf("%ld\n",(long)(stack_pointer-mem_base)); */ /* 8.10 */
    init_system(); 
    /* init_trace(); 13.1 */

    begin_terminal_io();
    var_occurred=FALSE;
    save_undo_stack=undo_stack;
    stdin_cleareof();
    c=read_char();
    /* Wait until an EOF or a good character */
    while (c!=EOF && !(c>32 && c!='.' && c!=';')) c=read_char();
    if (c==EOF)
      exitflag=TRUE;
    else {
      put_back_char(c);
      s=stack_copy_psi_term(parse(&sort));
      exitflag=(s->type==eof);
    }
    end_terminal_io();

    if (!exitflag) {
      if (sort==QUERY) {
        clear_already_loaded(symbol_table);
        push_goal(what_next,TRUE,var_occurred,1);
        ignore_eff=TRUE;
        goal_count=0;
        push_goal(prove,s,DEFRULES,NULL);
        reset_step();
        start_chrono();
        main_prove();
        /* assert(goal_stack==NULL); */
        /* assert(choice_stack==NULL); */
	if (undo_stack) {
	  undo(NULL);
          Errorline("Non-NULL undo stack.\n");
	}
        /* assert(undo_stack==NULL); */
      }
      else if (sort==FACT) {
        assert_first=FALSE;
        assert_clause(s);
        undo(save_undo_stack); /* 17.8 */
        var_occurred=FALSE; /* 18.8 */
        encode_types();
        Infoline(assert_ok?"\n*** Yes\n":"\n*** No\n"); /* 21.1 */
      }
    }
  } while (!exitflag);

  exit_life(TRUE);
}
