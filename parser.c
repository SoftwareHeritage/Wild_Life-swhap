/* Copyright 1991 Digital Equipment Corporation.
** All Rights Reserved.
*****************************************************************/

#include "extern.h"
#include "trees.h"
#include "token.h"
#include "print.h"
#include "copy.h"
  
#define NOP 2000
  
psi_term read_life_form();

psi_term psi_term_stack[PARSER_STACK_SIZE];
int int_stack[PARSER_STACK_SIZE];
operator op_stack[PARSER_STACK_SIZE];

int parse_ok;
int parser_stack_index;
ptr_node var_tree;
int no_var_tree;


/******** SHOW(limit)
  This prints the parser's stack, for debugging purposes
  only, LIMIT marks the bottom of the current stack.
*/
void show(limit)
int limit;
{
  int i;
  
  for (i=1;i<=parser_stack_index;i++) {
    if (i==limit)
      printf("-> ");
    else
      printf("   ");
    printf("%3d: ",i);
    switch (op_stack[i]) {
    case fx:
      printf("FX  ");
      break;
    case xfx:
      printf("XFX ");
      break;
    case xf:
      printf("XF  ");
      break;
    case nop:
      printf("NOP ");
      break;
    default:
      printf("??? ");
    }
    printf(" prec=%4d  ",int_stack[i]);
    display_psi_stdout(&(psi_term_stack[i]));
    printf("\n");
  }
  printf("\n");
}



/******** PUSH(tok,prec,op)
  Push psi_term and precedence and operator onto parser stack.
*/
void push(tok,prec,op)
psi_term tok;
int prec;
operator op;
{
  if (parser_stack_index==PARSER_STACK_SIZE) {
    perr("*** Parser error ");
    psi_term_error();
    perr(": stack full.\n");
  }
  else {
    parser_stack_index++;
    psi_term_stack[parser_stack_index]=tok;
    int_stack[parser_stack_index]=prec;
    op_stack[parser_stack_index]=op;
  }
}



/******** POP(psi_term,op);
  This function pops PSI_TERM and OP off the parser stack and returns
  its precedence.
*/
int pop(tok,op)
ptr_psi_term tok;
operator *op;
{
  int r=0;
  
  if (parser_stack_index==0) {
    /*
      perr("*** Parser error ");
      psi_term_error();
      perr(": stack empty.\n");
    */

    (*tok)= *error_psi_term;
    parse_ok=FALSE;
  }
  else {
    (*tok)=psi_term_stack[parser_stack_index];
    (*op)=op_stack[parser_stack_index];
    r=int_stack[parser_stack_index];
    parser_stack_index--;
  }
  
  return r;
}



/******** LOOK()
  This function returns the precedence of the stack top.
*/
int look()
{
  return int_stack[parser_stack_index];
}



/******** PRECEDENCE(tok,typ)
  This function returns the precedence of
  TOK if it is an operator of type TYP where TYP is FX XFX XF etc...
  Note that this allows both a binary and unary minus.
  The result is NOP if tok is not an operator.
*/
int precedence(tok,typ)
psi_term tok;
operator typ;
{
  int r=NOP;
  ptr_operator_data o;

  o=tok.type->op_data;
  while(o && r==NOP) {
    if(typ==o->type)
      r=o->precedence;
    else
      o=o->next;
  }
  
  return r;
}



/******** STACK_COPY_PSI_TERM(tok)
  Return the address of a copy of TOK on the STACK.
  All psi_terms read in by the parser are read into the stack.
*/
ptr_psi_term stack_copy_psi_term(t)
psi_term t;
{
  ptr_psi_term p;
  
  p=STACK_ALLOC(psi_term);
  (*p)=t;
#ifdef TS
  p->time_stamp=global_time_stamp; /* 9.6 */
#endif
  
  return p;
}



/******** HEAP_COPY_PSI_TERM(tok)
  Return the address of a copy of TOK on the HEAP.
*/
ptr_psi_term heap_copy_psi_term(t)
psi_term t;
{
  ptr_psi_term p;
  
  p=HEAP_ALLOC(psi_term);
  (*p)=t;
#ifdef TS
  p->time_stamp=global_time_stamp; /* 9.6 */
#endif
  
  return p;
}



/******** MAKE_UNIFY_PAIR(tok,arg1,arg2)
  Create a call to general unify with arguments arg1 and arg2.
  Upon entering, a psi-term must already exist for tok.
*/
void make_unify_pair(tok,arg1,arg2)
ptr_psi_term tok,arg1,arg2;
{
  /* tok->type=update_symbol("::"); */
  tok->type=colonsym;
  stack_insert(featcmp,one,&(tok->attr_list),stack_copy_psi_term(*arg1));
  stack_insert(featcmp,two,&(tok->attr_list),stack_copy_psi_term(*arg2));
}



/******** FEATURE_INSERT(keystr,tree,psi)
  Insert the psi_term psi into the attribute tree.
  If the feature already exists, create a call to the unification
  function.
*/
feature_insert(keystr,tree,psi)
char *keystr;
ptr_node *tree;
ptr_psi_term psi;
{
  ptr_node loc;
  /* ptr_psi_term stk_psi=stack_copy_psi_term(*psi); 19.8 */

  if (loc=find(featcmp,keystr,*tree)) {
    /* If the feature exists, create a conjunction */
    ptr_psi_term tmp=stack_psi_term(0);
    /* ptr_list lst=STACK_ALLOC(list); 19.8 */

    make_unify_pair(tmp,(ptr_psi_term)loc->data,psi); /* 19.8 */
    /* tmp->type=conjunction; 19.8 */
    /* tmp->value=(GENERIC)lst; 19.8 */
    /* lst->car=(ptr_psi_term)loc->data; 19.8 */
    /* lst->cdr=stk_psi; 19.8 */
    loc->data=(GENERIC)tmp;
  }
  else {
    /* If the feature does not exist, insert it. */
    ptr_psi_term stk_psi=stack_copy_psi_term(*psi); /* 19.8 */
    stack_insert_copystr(keystr,tree,(GENERIC)stk_psi); /* 10.8 */
  }
}



/******** READ_LIST(typ,end,separator)
  This reads in and constructs the list of type TYP ending with END and whose
  separator is SEPARATOR.
  
  Example:
  TYP=disjunction,
  END="}",
  SEPARATOR=";" will read in disjunctions.

  Example:
  TYP=list,
  END="]",
  SEPARATOR="," will read lists such as [1,2,a,b,c|d]
*/
psi_term read_list(typ,e,s)
ptr_definition typ;
char e,s;
{
  psi_term t;
  psi_term l;
  ptr_list li;
  char a;
  /* char *estr="?"; 18.5 */
  char estr[2];

  strcpy(estr,"?");

  li=STACK_ALLOC(list);
  li->car=NULL;
  li->cdr=NULL;
  
  l.type=typ;
  l.status=0;
  l.flags=FALSE; /* 14.9 */
  l.attr_list=NULL;
  l.resid=NULL;
  l.value=(GENERIC)li;
  l.coref=NULL;
  
  if (parse_ok) {

    a=e;
    if (e==']') a='|';
    
    read_token(&t);
    
    if (!equ_tokc(t,e)) {
      
      put_back_token(t);
      
      li->car=stack_copy_psi_term(read_life_form(s,a));
      
      read_token(&t);
      
      if(equ_tokc(t,s)) {
	li->cdr=stack_copy_psi_term(read_list(typ,e,s));
        estr[0]=e;
	t.type=update_symbol(estr);
      }
      
      if(equ_tokch(t,'|')) {
	li->cdr=stack_copy_psi_term(read_life_form(s,e));
	read_token(&t);
      }
      
      if(!equ_tokc(t,e)) {
        if (stringparse) parse_ok=FALSE;
        else {
	  perr("*** Syntax error ");psi_term_error();
          perr(": bad symbol in list '");
	  display_psi_stderr(&t);
	  perr("'.\n");
	  put_back_token(t);
        }
      }
    }

  }

  return l;
}




/******** READ_PSI_TERM()
  This reads in a complex object from the input
  stream, that is, a whole psi-term.

  Examples:

  [A,B,C]

  {0;1;2+A}

  <a,b,c> death(victim => V,murderer => M)

  which(x,y,z)

  A:g(f)

  I have allowed mixing labelled with unlabelled attributes.

  Example:
  
  f(x=>A,B,y=>K,"hklk",D) is parsed as f(1=>B,2=>"hklk",3=>D,x=>A,y=>K).
*/
psi_term read_psi_term()
{
  psi_term t,t2,t3;
  char s[10];
  int count=0,f=TRUE,f2,v;

  if(parse_ok) {
    
    read_token(&t);
    
    if(equ_tokch(t,'['))
      t=read_list(alist,']',',');
    else
      if(equ_tokch(t,'{')) 
	t=read_list(disjunction,'}',';');

      /* The syntax <a,b,c> for conjunctions has been abandoned.
	else
	if(equ_tokch(t,'<'))
	t=read_list(conjunction,'>',',');
	*/
  
    if(parse_ok 
       && t.type!=eof
       && !bad_psi_term(&t)
       /* && (precedence(t,fx)==NOP)
	  && (precedence(t,fy)==NOP) */
       ) {
      read_token(&t2);
      if(equ_tokch(t2,'(')) {
	
	do {
	  
	  f2=TRUE;
	  read_token(&t2);
	  
	  if(const(t2) && !bad_psi_term(&t2)) {
	    read_token(&t3);
	    if(equ_tok(t3,"=>")) {
	      t3=read_life_form(',',')');
              feature_insert(t2.type->symbol,&(t.attr_list),&t3);
	      f2=FALSE;
	    }
	    else 
	      put_back_token(t3);
	  }
	  
	  if(parse_ok && equal_types(t2.type,integer)) {
	    read_token(&t3);
	    if(equ_tok(t3,"=>")) {
	      t3=read_life_form(',',')');
	      v= *(REAL *)t2.value;
	      sprintf(s,"%d",v,0);
              feature_insert(s,&(t.attr_list),&t3);
	      f2=FALSE;
	    }
	    else 
	      put_back_token(t3);
	  }
	  
	  if(f2) {
	    put_back_token(t2);
	    t2=read_life_form(',',')');
	    ++count;
	    sprintf(s,"%d",count,0);
            feature_insert(s,&(t.attr_list),&t2);
	  }
	  
	  read_token(&t2);
	  
	  if(equ_tokch(t2,')'))
	    f=FALSE;
	  else
	    if(!equ_tokch(t2,',')) {
              if (stringparse) parse_ok=FALSE;
              else {
                perr("*** Syntax error ");psi_term_error();
                perr(": ',' expected in argument list.\n");
	        f=FALSE;
              }
	    }
	  
	} while(f && parse_ok);
      }
      else
	put_back_token(t2);
    }
  }
  else
    t= *error_psi_term;

  if(t.type==variable && t.attr_list) {
    t2=t;
    t.type=apply;
    t.value=NULL;
    t.coref=NULL;
    t.resid=NULL;
    stack_insert(featcmp,functor->symbol,
		 &(t.attr_list),
		 stack_copy_psi_term(t2));
  }
  
  return t;
}



/******** MAKE_LIFE_FORM(tok,arg1,arg2)
  This routine inserts ARG1 and ARG2 as the first and second attributes of
  psi_term TOK, thus creating the term TOK(1=>arg1,2=>arg2).

  If TOK is ':' then a conjunction is created if necessary.
  Example:
  a:V:b:5:int => V: <a,b,5,int> (= conjunction list).
*/
psi_term make_life_form(tok,arg1,arg2)
ptr_psi_term tok,arg1,arg2;
{  
  ptr_list l;
  ptr_psi_term a1,a2;

  deref_ptr(tok);
  tok->attr_list=NULL;
  tok->resid=NULL;

  if (/* UNI FALSE */ equ_tokch((*tok),':') && arg1 && arg2) {
    
    /* Here beginneth a terrible FIX,
       I will have to rewrite the psi_termiser and the parser to handle POINTERS
       to psi-terms instead of PSI_TERMS !!!
    */

    a1=arg1;
    a2=arg2;
    
    deref_ptr(a1);
    deref_ptr(a2);
    
    /* End of extremely ugly fix. */

    if(a1!=a2) {
      if(a1->type==top && 
	 !a1->attr_list &&
	 !a1->resid) {
	if(a1!=arg1)
	  /* push_ptr_value(psi_term_ptr,&(a1->coref)); 9.6 */
	  push_psi_ptr_value(a1,&(a1->coref));
	a1->coref=stack_copy_psi_term(*arg2);
	tok=arg1;
      }
      else
	if(a2->type==top && 
	   !a2->attr_list &&
	   !a2->resid) {
	  if(a2!=arg2)
	    /* push_ptr_value(psi_term_ptr,&(a2->coref)); 9.6 */
	    push_psi_ptr_value(a2,&(a2->coref));
	  a2->coref=stack_copy_psi_term(*arg1);
	  tok=arg2;
	}   
	else {
          make_unify_pair(tok,arg1,arg2); /* 19.8 */
	  /* tok->type=conjunction; 19.8 */
	  /* l=STACK_ALLOC(list); 19.8 */
	  /* tok->value=(GENERIC)l; 19.8 */
	  /* l->car=stack_copy_psi_term(*arg1); 19.8 */
	  /* l->cdr=stack_copy_psi_term(*arg2); 19.8 */
	}
    }
    else
      tok=arg1;
  }
  else {
    stack_insert(featcmp,one,&(tok->attr_list),stack_copy_psi_term(*arg1));
    if (arg2)
      stack_insert(featcmp,two,&(tok->attr_list),stack_copy_psi_term(*arg2));
  }
  
  return *tok;
}



/******** BAD_PSI_TERM(t)
  This returns true if T is a psi_term which is not allowed to be considered
  as a constant by the parser.

  Example: "A=)+6."  would otherwise be parsed as: "=(A,+(')',6))", this was
	             going a bit far.
*/
bad_psi_term(t)
ptr_psi_term t;
{
  char *s,c;
  int r;
  
  s=t->type->symbol;
  c=s[0];
  r=(s[1]==0
    && (c=='(' || c==')' || c=='[' || c==']' ||
        c=='{' || c=='}' || c=='.' || c=='?')
    );
/*
  if (strcmp(s,")"))
    if (strcmp(s,"("))
      if (strcmp(s,"["))
        if (strcmp(s,"]"))
          if (strcmp(s,"{"))
            if (strcmp(s,"}"))
              if (strcmp(s,"."))
                if (strcmp(s,"?"))
                  r=FALSE;
*/
  return r;
}


	    
/******** CRUNCH(prec,limit)
  Crunch up = work out the arguments of anything on the stack whose precedence
  is <= PREC, and replace it with the corresponding psi-term. Do not go any
  further than LIMIT which is the end of the current expression.
*/
void crunch(prec,limit)
int prec;
int limit;
{
  psi_term t,t1,t2,t3;
  operator op1,op2,op3;
  
  if(parse_ok && prec>=look() && parser_stack_index>limit) {
    
    pop(&t1,&op1);
    
    switch(op1) {
      
    case nop:
      pop(&t2,&op2);
      if(op2==fx)
	t=make_life_form(&t2,&t1,NULL);
      else
	if(op2==xfx) {
	  pop(&t3,&op3);
	  if(op3==nop)
	    t=make_life_form(&t2,&t3,&t1);
	  else {
	    printf("*** Parser: ooops, NOP expected.\n");
	    parse_ok=FALSE;
	    t= *error_psi_term;
	  }
	}
      break;
      
    case xf:
      pop(&t2,&op2);
      if(op2==nop)
	t=make_life_form(&t1,&t2,NULL);
      else {
	printf("*** Parser: ugh, NOP expected.\n");
	t= *error_psi_term;
	parse_ok=FALSE;
      }
      break;
      
    default:
      printf("*** Parser: yuck, weirdo operator.\n");
    }
    
    push(t,look(),nop);
    
    crunch(prec,limit);
  }
}



/******** READ_LIFE_FORM(str1,str2)
  This reads in one life-form from the input stream which finishes with
  the psi_term whose name is STR1 or STR2, typically if we're reading a list
  [A,4*5,b-4!] then STR1="," and STR2="|" . It would be incorrect if "," were
  taken as an operator.

  This routine implements the two state expression parser as described in the
  implementation guide. It deals with all the various types of operators,
  precedence is dealt with by the CRUNCH function. Each time an opening
  parenthesis is encountered a new expression is started.
*/
psi_term read_life_form(ch1,ch2)
char ch1,ch2;
{
  psi_term t,t2;
  int limit,pr_op,pr_1,pr_2,start=0;
  int fin=FALSE;
  int state=0;
  int prec=0;
  
  operator op;
  
  limit=parser_stack_index+1;
  
  if(parse_ok)
    do {
      if(state)
	read_token(&t);
      else
	t=read_psi_term();
      
      if(!start)
	start=line_count;
      
      if(!fin)
	if(state) {      
	  if(equ_tokc(t,ch1) || equ_tokc(t,ch2)) {
	    fin=TRUE;
	    put_back_token(t);
	  }
	  else {
	    
	    pr_op=precedence(t,xf);
	    pr_1=pr_op-1;
	    
	    if(pr_op==NOP) {
	      pr_op=precedence(t,yf);
	      pr_1=pr_op;
	    }
	    
	    if(pr_op==NOP) {
	      
	      pr_op=precedence(t,xfx);
	      pr_1=pr_op-1;
	      pr_2=pr_op-1;
	      
	      if(pr_op==NOP) {
		pr_op=precedence(t,xfy);
		pr_1=pr_op-1;
		pr_2=pr_op;
	      }
	      
	      if(pr_op==NOP) {
		pr_op=precedence(t,yfx);
		pr_1=pr_op;
		pr_2=pr_op-1;
	      }
	      
	      /* if(pr_op==NOP) {
		pr_op=precedence(t,yfy);
		pr_1=pr_op;
		pr_2=pr_op-1;
	      }
              */
	      
	      if(pr_op==NOP) {
		fin=TRUE;
		put_back_token(t);
	      }
	      else
		{
		  crunch(pr_1,limit);
		  push(t,pr_2,xfx);
		  prec=pr_2;
		  state=0;
		}
	    }
	    else {
	      crunch(pr_1,limit);
	      push(t,pr_1,xf);
	      prec=pr_1;
	    }
	  }
	}
	else {

	  if(t.attr_list)
	    pr_op=NOP;
	  else {
	    pr_op=precedence(t,fx);
	    pr_2=pr_op-1;
	  	  
	    if(pr_op==NOP) {
	      pr_op=precedence(t,fy);
	      pr_2=pr_op;
	    }
	  }

	  if(pr_op==NOP) {
	    if(equ_tokch(t,'(')) {
	      t2=read_life_form(')',0);
	      if(parse_ok) {
		push(t2,prec,nop);
		read_token(&t2);
		if(!equ_tokch(t2,')')) {
                  if (stringparse) parse_ok=FALSE;
                  else {
                    perr("*** Syntax error ");psi_term_error();
                    perr(": ')' missing.\n");
		    put_back_token(t2);
		  }
		}
		state=1;
	      }
	    }
	    else 
	      if(bad_psi_term(&t)) {
		put_back_token(t);
		/* psi_term_error(); */
		fin=TRUE;
	      }
	      else {
		push(t,prec,nop);
		state=1;
	      }
	  }
	  else {
	    push(t,pr_2,fx);
	    prec=pr_2;
	  }
	  
	}
      
    } while (!fin && parse_ok);
  
  if (state)
    crunch(MAX_PRECEDENCE,limit);
  
  if (parse_ok && parser_stack_index!=limit) {
    if (stringparse) parse_ok=FALSE;
    else {
      perr("*** Syntax error ");psi_term_error();
      perr(": bad expression.\n");
    }
  }
  else
    pop(&t,&op);
  
  if (!parse_ok)
    t= *error_psi_term;

  parser_stack_index=limit-1;
  
  return t;
}



/******** PARSE(is_it_a_clause)
  This returns one clause or query from the input stream.
  It also indicates the type psi-term read, that is whether it was a clause
  or a query in the IS_IT_A_CLAUSE variable. This is the top level of the
  parser.

  The whole parser is, rather like the psi_termiser, not too well written.
  It handles psi_terms rather than pointers which causes a lot of messy code
  and is somewhat slower.
*/
psi_term parse(q)
int *q;
{
  psi_term s,t,u;
  int c;

  parser_stack_index=0;
  parse_ok=TRUE;

  s=read_life_form('.','?');
  
  if (parse_ok) {
    if (s.type!=eof) {
      read_token(&t);
      if (equ_tokch(t,'?'))
	*q=QUERY;
      else if (equ_tokch(t,'.'))
	*q=FACT;
      else {
        if (stringparse) parse_ok=FALSE;
        else {
          perr("*** Syntax error ");psi_term_error();perr(": ");
	  display_psi_stderr(&t);
	  perr(".\n");
        }
	*q=ERROR;
      }
    }
  }

  if (!parse_ok) {

    while (saved_psi_term!=NULL) read_token(&u);

    prompt="error>";
    while((c=read_char()) && c!=EOF && c!='.' && c!='?' && c!=EOLN) {}

    *q=ERROR;
  }
  else if (saved_char)
    do {
      c=read_char();
      if (c==EOLN)
        c=0;
      else if (c<0 || c>32) {
        put_back_char(c);
        c=0;
      }
    } while(c && c!=EOF);

  /* Make sure arguments of nonstrict terms are marked quoted. */
  if (parse_ok) mark_nonstrict(&s); /* 25.8 */

  /* mark_eval(&s); 24.8 XXX */

  /* Mark all the psi-terms corresponding to variables in the var_tree as    */
  /* quoted.  This is needed for correct parsing of inputs; otherwise vars   */
  /* that occur in an increment of a query are marked to be evaluated again! */
  /* mark_quote_tree(var_tree); 24.8 XXX */

  return s;
}
