/* Copyright 1991 Digital Equipment Corporation.
** All Rights Reserved.
*****************************************************************/

#include "extern.h"
#include <signal.h>
#include "token.h"
#include "login.h"
#include "built_ins.h"
#include "error.h"

int interrupted=FALSE;



/******** INTERRUPT()
  This routine is called whenever the user types CONTROL C which generates an
  interrupt. The interrupt is dealt with later, when convenient, or ignored.
*/
void interrupt()
{
  interrupted=TRUE;
  signal(SIGINT,interrupt);
}



/******** INIT_INTERRUPT
  This initialises interrupts by trapping the interrupt signal and sending it
  to INTERRUPT.
*/
void init_interrupt()
{
  if (signal(SIGINT,SIG_IGN)!=SIG_IGN)
    signal(SIGINT,interrupt);
}



/******** HANDLE_INTERRUPT()
  This deals with an eventual interrupt.
  Return TRUE if execution continues normally, otherwise abort query, toggle
  trace on or off, or quit Wild_Life (suicide).
*/
void handle_interrupt()
{
  ptr_psi_term old_state;
  char *old_prompt;
  char c,d;
  int count;

  if (interrupted) printf("\n");
  interrupted=FALSE;
  old_prompt=prompt;
  steptrace=FALSE;

  /* new_state(&old_state); */
  old_state=input_state;
  open_input_file("stdin");
  stdin_cleareof();

  StartAgain:
  do {
    printf("*** Command ");
    prompt="(q,c,a,s,t,h)?";

    do {
      c=read_char();
    } while (c!=EOLN && c>0 && c<=32);
  
    d=c;
    count=0;
    while (DIGIT(d)) { count=count*10+(d-'0'); d=read_char(); }

    while (d!=EOLN && d!=EOF) d=read_char();

    if (c=='h' || c=='?') {
      printf("*** [Quit (q), Continue (c), Abort (a), Step (s,RETURN), Trace (t), Help (h,?)]\n");
    }

  } while (c=='h' || c=='?');
  
  prompt=old_prompt;

  switch (c) {
  case 'v':
  case 'V':
    verbose=TRUE;
    break;
  case 'q':
  case 'Q':
  case EOF:
    if (c==EOF) printf("\n");
    exit_life(FALSE);
    break;
  case 'a':
  case 'A':
    abort_life(FALSE);
    show_count();
    break;
  case 'c':
  case 'C':
    trace=FALSE;
    stepflag=FALSE;
    break;
  case 't':
  case 'T':
    trace=TRUE;
    stepflag=FALSE;
    break;
  case 's':
  case 'S':
  case EOLN:
    trace=TRUE;
    stepflag=TRUE;
    break;
  case '0': case '1': case '2': case '3': case '4':
  case '5': case '6': case '7': case '8': case '9':
    trace=TRUE;
    stepflag=TRUE;
    if (count>0) {
      stepcount=count;
      stepflag=FALSE;
    }
    break;
  default:
    goto StartAgain;
  }
  input_state=old_state;
  restore_state(input_state);
}
