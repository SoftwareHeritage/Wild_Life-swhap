/*									tab:4
 *
 * bi_math.c - math builtins
 *
 * Copyright (c) 1992 Digital Equipment Corporation
 * All Rights Reserved.
 *
 * The standard digital prl copyrights exist and where compatible
 * the below also exists.
 * Permission to use, copy, modify, and distribute this
 * software and its documentation for any purpose and without
 * fee is hereby granted, provided that the above copyright
 * notice appear in all copies.  Copyright holder(s) make no
 * representation about the suitability of this software for
 * any purpose. It is provided "as is" without express or
 * implied warranty.
 */
static char _version_string_[] = "\nVersion:1:bi_math.c\0\n";

#include "extern.h"
#include "trees.h"
#include "login.h"
#include "parser.h"
#include "copy.h"
#include "token.h"
#include "print.h"
#include "lefun.h"
#include "memory.h"
#include "built_ins.h"
#include "error.h"

/******** C_MULT
  Multiplication is considered as a 3-variable relation as in Prolog:
  
  arg1 * arg2 = arg3
  
  Only it may residuate or curry.
*/
static int c_mult()
{
  int success=TRUE;
  ptr_psi_term arg1,arg2,arg3,t;
  int num1,num2,num3;
  REAL val1,val2,val3;
  
  t=aim->a;
  deref_ptr(t);
  get_two_args(t->attr_list,&arg1,&arg2);
  arg3=aim->b;
  
  if(arg1) {
    deref(arg1);
    success=get_real_value(arg1,&val1,&num1);
    if(success && arg2) {
      deref(arg2);
      deref_args(t,set_1_2);
      success=get_real_value(arg2,&val2,&num2);
    }
  }
  
  if(success)
    if(arg1 && arg2) {
      deref(arg3);
      success=get_real_value(arg3,&val3,&num3);
      if(success)
	switch(num1+num2*2+num3*4) {
	case 0:
          residuate3_double(arg1,arg2,arg3); /* 20.1 */

	  /* if(arg1==arg3)
	    success=unify_real_result(arg2,(REAL)1);
	  else
	    if(arg2==arg3)
	      success=unify_real_result(arg1,(REAL)1);
	    else
	      residuate2_double(arg1,arg3); 20.1
	  */
	  break;
	case 1:
	  if (val1==1.0)
	    push_goal(unify,arg2,arg3,NULL);
          else if (val1==0.0)
	    success=unify_real_result(arg3,(REAL)0);
          else if (val1!=1.0 && arg2==arg3) /* 9.9 */
	    success=unify_real_result(arg3,(REAL)0);
	  else
	    residuate2_double(arg2,arg3); /* 20.1 */
	  break;
	case 2:
	  if (val2==1.0)
	    push_goal(unify,arg1,arg3,NULL);
	  else if (val2==0.0)
	    success=unify_real_result(arg3,(REAL)0);
          else if (val2!=1.0 && arg1==arg3) /* 9.9 */
	    success=unify_real_result(arg3,(REAL)0);
	  else
	    residuate2_double(arg1,arg3); /* 20.1 */
	  break;
	case 3:
	  success=unify_real_result(arg3,val1*val2);
	  break;
	case 4:
	  if (arg1==arg2) {
            if (val3==0.0) /* 8.9 */
	      success=unify_real_result(arg1,(REAL)0);
            else if (val3>0.0)
	      residuate(arg1);
	    else
	      success=FALSE;
          }
	  else {
            /* Case A*B=0 is not dealt with because it is nondeterministic */
	    residuate2_double(arg1,arg2); /* 20.1 */
          }
	  break;
	case 5:
	  if(val1)
	    success=unify_real_result(arg2,val3/val1);
	  else
	    success=(val3==0);
	  break;
	case 6:
	  if(val2)
	    success=unify_real_result(arg1,val3/val2);
	  else
	    success=(val3==0);
	  break;
	case 7:
	  success=(val3==val1*val2);
	  break;
	}
      
    }
    else
      curry();
  
  nonnum_warning(t,arg1,arg2);
  return success;
}



/******** C_DIV
  Similar to multiply (watch out for cut and paste errors !).
*/
static int c_div()
{
  int success=TRUE;
  ptr_psi_term arg1,arg2,arg3,t;
  int num1,num2,num3;
  REAL val1,val2,val3;
  
  t=aim->a;
  deref_ptr(t);
  get_two_args(t->attr_list,&arg1,&arg2);
  arg3=aim->b;
  
  if (arg1) {
    deref(arg1);
    success=get_real_value(arg1,&val1,&num1);
    if (success && arg2) {
      deref(arg2);
      deref_args(t,set_1_2);
      success=get_real_value(arg2,&val2,&num2);
    }
  }
  
  if (success)
    if (arg1 && arg2) {
      deref(arg3);
      success=get_real_value(arg3,&val3,&num3);
      if (success)
	switch(num1+num2*2+num3*4) {
	case 0:
	  residuate3_double(arg1,arg2,arg3); /* 20.1 */
	  break;
	case 1:
	  if (val1) {
	    if (arg2==arg3) {
	      if (val1>0.0)
	        residuate(arg2);
	      else
		success=FALSE; /* A/B=B where A<0 */
            }
	    else
	      residuate2_double(arg2,arg3); /* 20.1 */
          }
          else if (arg2==arg3) /* 9.9 */
            success=unify_real_result(arg2,(REAL)0);
          else
            residuate2_double(arg2,arg3); /* 20.1 */
	  break;
	case 2:
	  if (val2) {
            if (val2==1.0) /* 8.9 */
              push_goal(unify,arg1,arg3,NULL);
            else if (arg1==arg3) /* 9.9 */
              success=unify_real_result(arg1,(REAL)0);
            else
	      residuate2_double(arg1,arg3); /* 20.1 */
          }
	  else {
	    success=FALSE;
            Errorline("division by zero in %P.\n",t); /* 8.9 */
          }
	  break;
	case 3:
	  if (val2)
	    success=unify_real_result(arg3,val1/val2);
	  else {
	    success=FALSE;
            Errorline("division by zero in %P.\n",t); /* 8.9 */
          }
	  break;
	case 4:
	  if (val3) {
            if (val3==1.0 && arg1!=arg2) { /* 9.9 */
              push_goal(unify,arg1,arg2,NULL);
            }
            else if (val3!=1.0 && arg1==arg2) /* 9.9 */
              success=unify_real_result(arg1,(REAL)0);
            else
	      residuate2_double(arg1,arg2); /* 20.1 */
          }
          else
            success=unify_real_result(arg1,(REAL)0);
	  break;
	case 5:
	  if (val3)
	    success=unify_real_result(arg2,val1/val3);
	  else
	    success=(val1==0);
	  break;
	case 6:
          if (val2)
	    success=unify_real_result(arg1,val3*val2);
          else {
            if (val3) {
	      success=FALSE;
              Errorline("division by zero in %P.\n",t); /* 8.9 */
            }
            else
              success=unify_real_result(arg1,(REAL)0);
          }
	  break;
	case 7:
	  if (val2)
	    success=(val3==val1/val2);
	  else {
	    success=FALSE;
            Errorline("division by zero in %P.\n",t); /* 8.9 */
          }
	  break;
	}
      
    }
    else
      curry();
  
  nonnum_warning(t,arg1,arg2);
  return success;
}



/* Main routine for floor & ceiling functions */
static int c_floor_ceiling(floorflag)
int floorflag;
{
  int success=TRUE;
  ptr_psi_term arg1,arg2,arg3,t;
  int num1,num3;
  REAL val1,val3;
  
  t=aim->a;
  deref_ptr(t);
  get_two_args(t->attr_list,&arg1,&arg2);
  arg3=aim->b;
  
  if(arg1) {
    deref(arg1);
    deref_args(t,set_1);
    success=get_real_value(arg1,&val1,&num1);
    if(success) {
      deref(arg3);
      success=get_real_value(arg3,&val3,&num3);
      if(success)
	switch(num1+num3*4) {
	case 0:
	  residuate(arg1);
	  break;
	case 1:
	  success=unify_real_result(arg3,(floorflag?floor(val1):ceil(val1)));
	  break;
	case 4:
	  residuate(arg1);
	  break;
	case 5:
	  success=(val3==(floorflag?floor(val1):ceil(val1)));
	}
    }
  }
  else
    curry();

  nonnum_warning(t,arg1,NULL);
  return success;
}



/******** C_FLOOR
  Return the largest integer inferior or equal to the argument
*/
static int c_floor()
{
  return c_floor_ceiling(TRUE);
}




/******** C_CEILING
  Return the smallest integer larger or equal to the argument
*/
static int c_ceiling()
{
  return c_floor_ceiling(FALSE);
}



/******** C_SQRT
  Return the square root of the argument
*/
static int c_sqrt()
{
  int success=TRUE;
  ptr_psi_term arg1,arg3,t;
  int num1,num3;
  REAL val1,val3;
  
  t=aim->a;
  deref_ptr(t);
  get_one_arg(t->attr_list,&arg1);
  arg3=aim->b;
  
  if (arg1) {
    deref(arg1);
    deref_args(t,set_1);
    success=get_real_value(arg1,&val1,&num1);
    if (success) {
      deref(arg3);
      success=get_real_value(arg3,&val3,&num3);
      if (success)
	switch(num1+num3*4) {
	case 0:
	  residuate2_double(arg1,arg3); /* 20.1 */
	  break;
	case 1:
	  if (val1>=0)
	    success=unify_real_result(arg3,sqrt(val1));
	  else {
	    success=FALSE;
            Errorline("square root of negative number in %P.\n",t);
          }
	  break;
	case 4:
	  success=unify_real_result(arg1,val3*val3);
	  break;
	case 5:
	  success=(val3*val3==val1 || (val1>=0 && val3==sqrt(val1)));
          if (val1<0) Errorline("square root of negative number in %P.\n",t);
	}
    }
  }
  else
    curry();

  nonnum_warning(t,arg1,NULL);
  return success;
}


#define SINFLAG 1
#define COSFLAG 2
#define TANFLAG 3


/* Main routine for sine and cosine */
static int c_trig(trigflag)
int trigflag;
{
  int success=TRUE;
  ptr_psi_term arg1,arg3,t; /* arg3 is result */
  int num1,num3;
  REAL val1,val3,ans;

  t=aim->a;
  deref_ptr(t);
  get_one_arg(t->attr_list,&arg1);
  arg3=aim->b;

  if (arg1) {
    deref(arg1);
    deref_args(t,set_1);
    success=get_real_value(arg1,&val1,&num1);
    if (success) {
      deref(arg3);
      success=get_real_value(arg3,&val3,&num3);
      if (success)
        switch(num1+num3*4) {
        case 0:
          residuate2_double(arg1,arg3); /* 20.1 */
          break;
        case 1:
          ans=(trigflag==SINFLAG?sin(val1):
              (trigflag==COSFLAG?cos(val1):
              (trigflag==TANFLAG?tan(val1):0.0)));
          success=unify_real_result(arg3,ans);
          break;
        case 4:
          if (trigflag==TANFLAG || (val3>= -1 && val3<=1)) {
            ans=(trigflag==SINFLAG?asin(val3):
                (trigflag==COSFLAG?acos(val3):
                (trigflag==TANFLAG?atan(val3):0.0)));
            success=unify_real_result(arg1,ans);
          }
          else
            success=FALSE;
          break;
        case 5:
          ans=(trigflag==SINFLAG?asin(val1):
              (trigflag==COSFLAG?acos(val1):
              (trigflag==TANFLAG?atan(val1):0.0)));
          success=(val3==ans);
        }
    }
  }
  else
    curry();

  nonnum_warning(t,arg1,NULL);
  return success;
}


/******** C_COSINE
  Return the cosine of the argument (in radians).
*/
static int c_cos()
{
  return (c_trig(COSFLAG));
}




/******** C_SINE
  Return the sine of the argument
*/
static int c_sin()
{
  return (c_trig(SINFLAG));
}



/******** C_TAN
  Return the tangent of the argument
*/
static int c_tan()
{
  return (c_trig(TANFLAG));
}



/******** C_BIT_AND
  Return the bitwise operation: ARG1 and ARG2.
*/
static int c_bit_and()
{
  int success=TRUE;
  ptr_psi_term arg1,arg2,arg3,t;
  int num1,num2,num3;
  REAL val1,val2,val3;
  
  t=aim->a;
  deref_ptr(t);
  get_two_args(t->attr_list,&arg1,&arg2);
  arg3=aim->b;
  
  if(arg1) {
    deref(arg1);
    success=get_real_value(arg1,&val1,&num1);
    if(success && arg2) {
      deref(arg2);
      deref_args(t,set_1_2);
      success=get_real_value(arg2,&val2,&num2);
    }
  }
  
  if(success)
    if(arg1 && arg2) {
      deref(arg3);
      success=get_real_value(arg3,&val3,&num3);
      if(success)
	switch(num1+num2*2+num3*4) {
	case 0:
	  residuate2_double(arg1,arg2); /* 20.1 */
	  break;
	case 1:
          if (bit_and_warning(arg1,val1)) return (c_abort());
	  if(val1)
	    residuate(arg2);
	  else
	    success=unify_real_result(arg3,(REAL)0);
	  break;
	case 2:
          if (bit_and_warning(arg2,val2)) return (c_abort());
	  if(val2)
	    residuate(arg1);
	  else
	    success=unify_real_result(arg3,(REAL)0);
	  break;
	case 3:
          if (bit_and_warning(arg1,val1)||bit_and_warning(arg2,val2))
            return (c_abort());
	  success=unify_real_result(arg3,(REAL)(((int)val1) & ((int)val2)));
	  break;
	case 4:
	  residuate2_double(arg1,arg2); /* 20.1 */
	  break;
	case 5:
          if (bit_and_warning(arg1,val1)) return (c_abort());
	  residuate(arg2);
	  break;
	case 6:
          if (bit_and_warning(arg2,val2)) return (c_abort());
	  residuate(arg1);
	  break;
	case 7:
          if (bit_and_warning(arg1,val1)||bit_and_warning(arg2,val2))
            return (c_abort());
	  success=(val3==(REAL)(((int)val1) & ((int)val2)));
	  break;
	}
      
    }
    else
      curry();
  
  nonnum_warning(t,arg1,arg2);
  return success;
}



/******** C_BIT_OR
  Return the bitwise operation: ARG1 or ARG2.
*/
static int c_bit_or()
{
  int success=TRUE;
  ptr_psi_term arg1,arg2,arg3,t;
  int num1,num2,num3;
  REAL val1,val2,val3;
  
  t=aim->a;
  deref_ptr(t);
  get_two_args(t->attr_list,&arg1,&arg2);
  arg3=aim->b;
  
  if(arg1) {
    deref(arg1);
    success=get_real_value(arg1,&val1,&num1);
    if(success && arg2) {
      deref(arg2);
      deref_args(t,set_1_2);
      success=get_real_value(arg2,&val2,&num2);
    }
  }
  
  if(success)
    if(arg1 && arg2) {
      deref(arg3);
      success=get_real_value(arg3,&val3,&num3);
      if(success)
	switch(num1+num2*2+num3*4) {
	case 0:
        case 4:
	  residuate2_double(arg1,arg2); /* 20.1 */
	  break;
	case 1:
        case 5:
          if (bit_or_warning(arg1,val1)) return (c_abort());
	  residuate(arg2);
	  break;
	case 2:
        case 6:
          if (bit_or_warning(arg2,val2)) return (c_abort());
	  residuate(arg1);
	  break;
	case 3:
          if (bit_or_warning(arg1,val1)||bit_or_warning(arg2,val2))
            return (c_abort());
	  success=unify_real_result(arg3,(REAL)(((int)val1) | ((int)val2)));
	  break;
	case 7:
          if (bit_or_warning(arg1,val1)||bit_or_warning(arg2,val2))
            return (c_abort());
	  success=(val3==(REAL)(((int)val1) | ((int)val2)));
	  break;
	}      
    }
    else
      curry();
  
  nonnum_warning(t,arg1,arg2);
  return success;
}


/******** C_SHIFT
  Return the bitwise shift left or shift right.
*/

static int c_shift_left()
{
  return (c_shift(FALSE));
}

static int c_shift_right()
{
  return (c_shift(TRUE));
}

static int c_shift(dir)
int dir;
{
  int success=TRUE;
  ptr_psi_term arg1,arg2,arg3,t;
  int num1,num2,num3;
  REAL val1,val2,val3,ans;
  
  t=aim->a;
  deref_ptr(t);
  get_two_args(t->attr_list,&arg1,&arg2);
  arg3=aim->b;
  
  if(arg1) {
    deref(arg1);
    success=get_real_value(arg1,&val1,&num1);
    if(success && arg2) {
      deref(arg2);
      deref_args(t,set_1_2);
      success=get_real_value(arg2,&val2,&num2);
    }
  }
  
  if(success)
    if(arg1 && arg2) {
      deref(arg3);
      success=get_real_value(arg3,&val3,&num3);
      if (success)
	switch(num1+num2*2+num3*4) {
	case 0:
        case 4:
	  residuate2_double(arg1,arg2); /* 20.1 */
	  break;
	case 1:
        case 5:
          if (shift_warning(dir,arg1,val1)) return (c_abort());
	  residuate(arg2);
	  break;
	case 2:
        case 6:
          if (shift_warning(dir,arg2,val2)) return (c_abort());
	  residuate(arg1);
	  break;
	case 3:
          if (shift_warning(dir,arg1,val1)||shift_warning(dir,arg2,val2))
            return (c_abort());
          ans=(REAL)(dir?(int)val1>>(int)val2:(int)val1<<(int)val2);
	  success=unify_real_result(arg3,ans);
	  break;
        case 7:
          if (shift_warning(dir,arg1,val1)||shift_warning(dir,arg2,val2))
            return (c_abort());
          ans=(REAL)(dir?(int)val1>>(int)val2:(int)val1<<(int)val2);
	  success=(val3==ans);
	  break;
	}      
    }
    else
      curry();
  
  nonnum_warning(t,arg1,arg2);
  return success;
}


/******** C_MOD
  The modulo operation.
*/
static int c_mod()
{
  int success=TRUE;
  ptr_psi_term arg1,arg2,arg3,t;
  int num1,num2,num3;
  REAL val1,val2,val3;
  
  t=aim->a;
  deref_ptr(t);
  get_two_args(t->attr_list,&arg1,&arg2);
  arg3=aim->b;
  
  if(arg1) {
    deref(arg1);
    success=get_real_value(arg1,&val1,&num1);
    if(success && arg2) {
      deref(arg2);
      deref_args(t,set_1_2);
      success=get_real_value(arg2,&val2,&num2);
    }
  }
  
  if(success)
    if(arg1 && arg2) {
      deref(arg3);
      success=get_real_value(arg3,&val3,&num3);
      if(success)
	switch(num1+num2*2+num3*4) {
	case 0:
	case 4:
	  residuate2_double(arg1,arg2); /* 20.1 */
	  break;
	case 1:
	case 5:
          if (mod_warning(arg1,val1)) return (c_abort());
	  residuate(arg2);
	  break;
	case 2:
	case 6:
          if (mod_warning(arg2,val2)) return (c_abort());
	  residuate(arg1);
	  break;
	case 3:
          if (mod_warning(arg1,val1)||mod_warning(arg2,val2))
            return (c_abort());
	  success=unify_real_result(arg3,(REAL)((int)val1 % (int)val2));
	  break;
	case 7:
          if (mod_warning(arg1,val1)||mod_warning(arg2,val2))
            return (c_abort());
	  success=(val3==(REAL)((int)val1 % (int)val2));
	  break;
	}      
    }
    else
      curry();
  
  nonnum_warning(t,arg1,arg2);
  return success;
}

/******** C_ADD
  Addition is considered as a 3-variable relation as in Prolog:
  
  arg1 + arg2 = arg3
  
  Only it may residuate or curry.

  Addition is further complicated by the fact that it is both a unary and
  binary function.
*/
static int c_add()
{
  int success=TRUE;
  ptr_psi_term arg1,arg2,arg3,t;
  int num1,num2,num3;
  REAL val1,val2,val3;
  
  t=aim->a;
  deref_ptr(t);
  get_two_args(t->attr_list,&arg1,&arg2);
  arg3=aim->b;
  
  if(arg1) {
    deref(arg1);
    success=get_real_value(arg1,&val1,&num1);
    if(success && arg2) {
      deref(arg2);
      deref_args(t,set_1_2);
      success=get_real_value(arg2,&val2,&num2);
    }
  }
  
  if(success)
    if(arg1 && arg2) {
      deref(arg3);
      success=get_real_value(arg3,&val3,&num3);
      if(success)
	switch(num1+num2*2+num3*4) {
	case 0:
	  if (arg1==arg3)
	    success=unify_real_result(arg2,(REAL)0);
          else if (arg2==arg3)
	    success=unify_real_result(arg1,(REAL)0);
          else
	    residuate3_double(arg1,arg2,arg3); /* 20.1 */
	  break;
	case 1:
	  if (val1) {
            if (arg2==arg3) /* 8.9 */
              success=FALSE;
            else
	      residuate2_double(arg2,arg3); /* 20.1 */
          }
          else
	    push_goal(unify,arg2,arg3,NULL);
	  break;
	case 2:
	  if (val2) {
            if (arg1==arg3) /* 8.9 */
              success=FALSE;
            else
	      residuate2_double(arg1,arg3); /* 20.1 */
          }
          else
	    push_goal(unify,arg1,arg3,NULL);
	  break;
	case 3:
	  success=unify_real_result(arg3,val1+val2);
	  break;
	case 4:
	  if (arg1==arg2)
	    success=unify_real_result(arg1,val3/2);
	  else
	    residuate2_double(arg1,arg2); /* 20.1 */
	  break;
	case 5:
	  success=unify_real_result(arg2,val3-val1);
	  break;
	case 6:
	  success=unify_real_result(arg1,val3-val2);
	  break;
	case 7:
	  success=(val3==val1+val2);
	  break;
	}
    }
    else
      if(arg1) {
	deref(arg3);
	success=get_real_value(arg3,&val3,&num3);
	if(success)
	  switch(num1+4*num3) {
	  case 0:
	    residuate2_double(arg1,arg3); /* 20.1 */
	    break;
	  case 1:
	    success=unify_real_result(arg3,val1);
	    break;
	  case 4:
	    success=unify_real_result(arg1,val3);
	    break;
	  case 5:
	    success=(val1==val3);
	  }
      }
      else
	curry();
  
  nonnum_warning(t,arg1,arg2);
  return success;
}




/******** C_SUB
  Identical (nearly) to C_ADD
*/
static int c_sub()
{
  int success=TRUE;
  ptr_psi_term arg1,arg2,arg3,t;
  int num1,num2,num3;
  REAL val1,val2,val3;
  
  t=aim->a;
  deref_ptr(t);
  get_two_args(t->attr_list,&arg1,&arg2);
  arg3=aim->b;
  
  if(arg1) {
    deref(arg1);
    success=get_real_value(arg1,&val1,&num1);
    if(success && arg2) {
      deref(arg2);
      deref_args(t,set_1_2);
      success=get_real_value(arg2,&val2,&num2);
    }
  }
  
  if(success)
    if(arg1 && arg2) {
      deref(arg3);
      success=get_real_value(arg3,&val3,&num3);
      if(success)
	switch(num1+num2*2+num3*4) {
	case 0:
	  if (arg1==arg3)
	    success=unify_real_result(arg2,(REAL)0);
	  else if (arg1==arg2)
	    success=unify_real_result(arg3,(REAL)0);
	  else
	    residuate3_double(arg1,arg2,arg3); /* 20.1 */
	  break;
	case 1:
	  if (arg2==arg3)
	    success=unify_real_result(arg3,val1/2);
          else
	    residuate2_double(arg2,arg3); /* 20.1 */
	  break;
	case 2:
	  if (val2) {
            if (arg1==arg3) /* 9.9 */
              success=FALSE;
            else
	      residuate2_double(arg1,arg3); /* 20.1 */
          }
          else
	    push_goal(unify,arg1,arg3,NULL);
	  break;
	case 3:
	  success=unify_real_result(arg3,val1-val2);
	  break;
	case 4:
	  if (arg1==arg2)
	    success=(val3==0);
          else if (val3)
	    residuate2_double(arg1,arg2); /* 20.1 */
	  else
	    push_goal(unify,arg1,arg2,NULL);
	  break;
	case 5:
	  success=unify_real_result(arg2,val1-val3);
	  break;
	case 6:
	  success=unify_real_result(arg1,val3+val2);
	  break;
	case 7:
	  success=(val3==val1-val2);
	  break;
	}
    }
    else
      if(arg1) {
	deref(arg3);
	success=get_real_value(arg3,&val3,&num3);
	if(success)
	  switch(num1+4*num3) {
	  case 0:
	    residuate2_double(arg1,arg3); /* 20.1 */
	    break;
	  case 1:
	    success=unify_real_result(arg3,-val1);
	    break;
	  case 4:
	    success=unify_real_result(arg1,-val3);
	    break;
	  case 5:
	    success=(val1== -val3);
	  }
      }
      else
	curry();
  
  nonnum_warning(t,arg1,arg2);
  return success;
}

/******** C_LOG
  Natural logarithm.
*/
static int c_log()
{
  int success=TRUE;
  ptr_psi_term arg1,arg3,t;
  int num1,num3;
  REAL val1,val3;
  
  t=aim->a;
  deref_ptr(t);
  get_one_arg(t->attr_list,&arg1);
  arg3=aim->b;
  
  if(arg1) {
    deref(arg1);
    deref_args(t,set_1);
    success=get_real_value(arg1,&val1,&num1);
    if(success) {
      deref(arg3);
      success=get_real_value(arg3,&val3,&num3);
      if(success)
	switch(num1+num3*4) {
	case 0:
	  residuate2_double(arg1,arg3); /* 20.1 */
	  break;
	case 1:
	  if (val1>0)
	    success=unify_real_result(arg3,log(val1));
	  else {
	    success=FALSE;
            Errorline("logarithm of %s in %P.\n",
                      (val1==0)?"zero":"a negative number",t);
          }
	  break;
	case 4:
	  success=unify_real_result(arg1,exp(val3));
	  break;
	case 5:
	  success=(exp(val3)==val1 || (val1>0 && val3==log(val1)));
          if (val1<=0)
            Errorline("logarithm of %s in %P.\n",
                      (val1==0)?"zero":"a negative number",t);
	}
    }
  }
  else
    curry();

  nonnum_warning(t,arg1,NULL);
  return success;
}




/******** C_EXP
  Exponential.
*/
static int c_exp()
{
  int success=TRUE;
  ptr_psi_term arg1,arg2,arg3,t;
  int num1,num3;
  REAL val1,val3;
  
  t=aim->a;
  deref_ptr(t);
  get_two_args(t->attr_list,&arg1,&arg2);
  arg3=aim->b;
  
  if(arg1) {
    deref(arg1);
    deref_args(t,set_1);
    success=get_real_value(arg1,&val1,&num1);
    if(success) {
      deref(arg3);
      success=get_real_value(arg3,&val3,&num3);
      if(success)
	switch(num1+num3*4) {
	case 0:
	  residuate2_double(arg1,arg3); /* 20.1 */
	  break;
	case 1:
	  success=unify_real_result(arg3,exp(val1));
	  break;
	case 4:
	  if(val3>0)
	    success=unify_real_result(arg1,log(val3));
	  else
	    success=FALSE;
	  break;
	case 5:
	  success=(exp(val1)==val3 || (val3>0 && val1==log(val3)));
	}
    }
  }
  else
    curry();

  nonnum_warning(t,arg1,NULL);
  return success;
}

insert_math_builtins()
{
  new_built_in("*",function,c_mult);
  new_built_in("+",function,c_add);
  new_built_in("-",function,c_sub);
  new_built_in("/",function,c_div);  
  new_built_in("mod",function,c_mod);
  new_built_in("/\\",function,c_bit_and);
  new_built_in("\\/",function,c_bit_or);
  new_built_in(">>",function,c_shift_right);
  new_built_in("<<",function,c_shift_left);
  new_built_in("floor",function,c_floor);
  new_built_in("ceiling",function,c_ceiling);
  new_built_in("exp",function,c_exp);
  new_built_in("log",function,c_log);
  new_built_in("cos",function,c_cos);
  new_built_in("sin",function,c_sin);
  new_built_in("tan",function,c_tan);
  new_built_in("sqrt",function,c_sqrt);
}

