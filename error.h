/* Copyright 1991 Digital Equipment Corporation.
** All Rights Reserved.
**
*****************************************************************/

#ifndef _ERROR_H_
#define _ERROR_H_

extern void stack_info();

extern void init_trace();
extern void reset_step();
extern void tracing();
extern void new_trace();
extern void new_step();
extern void toggle_trace();
extern void toggle_step();
extern int quietflag; /* 21.1 */
extern int trace;
extern int verbose; /* 21.1 */
extern int stepflag;
extern int steptrace;
extern int stepcount;

#define NOTQUIET (!quietflag || verbose) /* 21.1 */

extern int warning();
extern int warningx();
extern void perr();
extern void perr_s();
extern void perr_s2();
extern void perr_i();

extern void report_error();
extern void report_warning();
extern void report_error2();
extern void report_warning2();

extern void nonnum_warning();
extern int bit_and_warning();
extern int bit_or_warning();
extern int mod_warning();
extern int shift_warning();

#ifndef NOTRACE
#define Traceline  if (trace) traceline
#else
#define Traceline  if (0) traceline
#endif

/* 21.1 */
#define Infoline   if (NOTQUIET) infoline

extern void Errorline();
extern void Syntaxerrorline();
extern void outputline(); /* To output_stream */
#define Warningline if (warningflag) warningline

#endif
