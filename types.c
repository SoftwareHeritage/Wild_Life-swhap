/* Copyright 1991 Digital Equipment Corporation.
** All Rights Reserved.
*****************************************************************/

/****************************************************************************

  These routines implement type encoding using the "Transitive Closure"
  binary encoding algorithm.

 ****************************************************************************/

#include "extern.h"
#include "login.h"
#include "trees.h"
#include "print.h"
#include "memory.h"
#include "error.h"
#include "token.h"

int types_modified;
int type_count;

ptr_definition *gamma_table;

ptr_int_list adults,children;

typedef struct _pair_def{
  ptr_definition car;
  ptr_definition cdr;
} pair_def;




/******** PRINT_DEF_TYPE(t)
  This prints type T to stderr, where T=predicate, function or type.
*/
void print_def_type(t)
def_type t;
{
  switch (t) {
  case predicate:
    perr("predicate");
    break;
  case function:
    perr("function");
    break;
  case type:
    perr("sort");
    break;
  default:
    perr("undefined");
  }
}


/* Confirm an important change */
int yes_or_no()
{
  char *old_prompt,c,d;
  ptr_psi_term old_state;

  perr("*** Are you really sure you want to do that ");
  old_prompt=prompt;
  prompt="(y/n)?";
  old_state=input_state;
  open_input_file("stdin");

  do {
    do {
      c=read_char();
    } while (c!=EOLN && c>0 && c<=32);
  } while (c!='y' && c!='n');

  d=c;
  while (d!=EOLN && d!=EOF) d=read_char();

  prompt=old_prompt;
  input_state=old_state;
  restore_state(old_state);
  return (c=='y');
}


/* Remove references to d in d's children or parents */
remove_cycles(d, dl)
ptr_definition d;
ptr_int_list *dl;
{
  while (*dl) {
    if (((ptr_definition)(*dl)->value)==d)
      *dl = (*dl)->next;
    else
      dl= &((*dl)->next);
  }
}



/******** REDEFINE(t)
  This decides whether a definition (a sort, function, or predicate)
  may be extended or not.
*/
int redefine(t)
ptr_psi_term t;
{
  void make_type_link(); /* Forward declaration */
  ptr_definition d,d2;
  ptr_int_list l,*l2;
  int success=TRUE;
  
  deref_ptr(t);
  d=t->type;
  if (d->date<file_date) {
    if (d->type==type) {
      /* Except for top, sorts are always unprotected, with a warning. */
      if (FALSE /*d==top*/) {
        Errorline("the top sort '@' may not be extended.\n");
        success=FALSE;
      }
      else if (d!=top)
        Warningline("extending definition of sort '%s'.\n",d->symbol);
    }
    else if (d->protected && d->type!=undef) {
      if (d->date>0) {
        /* The term was entered in a previous file, and therefore */
        /* cannot be altered. */
        Errorline("the user-defined %T '%s' may not be changed.\n",
                  d->type, d->symbol);
        success=FALSE;
      }
      else {
        if (d->rule && (int)d->rule<=MAX_BUILT_INS /*&& input_stream==stdin*/) {
          /* d is a built-in, and therefore cannot be altered. */
          Errorline("the built-in %T '%s' may not be extended.\n",
                    d->type, d->symbol);
          success=FALSE;
        }
        else {
          /* d is not a built-in, and therefore can be altered. */
          Warningline("extending the %T '%s'.\n",d->type,d->symbol);
          if (warningflag) if (!yes_or_no()) success=FALSE;
        }
      }
    }
    
    if (success) {
      if (d->type==type) { /* d is an already existing type */
        /* Remove cycles in the type hierarchy of d */
        /* This is done by Richard's version, and I don't know why. */
        /* It seems to be a no-op. */
        remove_cycles(d, &(d->children));
        remove_cycles(d, &(d->parents));
        /* d->rule=NULL; */ /* Types must keep their rules! */
        /* d->properties=NULL; */ /* Types get new properties from encode */
      }
      if (d->date==0) d->date=file_date;
      /* d->type=undef; */ /* Objects keep their type! */
      /* d->always_check=TRUE; */
      /* d->protected=TRUE; */
      /* d->children=NULL; */
      /* d->parents=NULL; */
      /* d->code=NOT_CODED; */
    }
  }

  return success;
}



/******** CONS(value,list)
  Returns the list [VALUE|LIST]
*/
ptr_int_list cons(v,l)
GENERIC v;
ptr_int_list l;
{
  ptr_int_list n;

  n=HEAP_ALLOC(int_list);
  n->value=v;
  n->next=l;
  
  return n;
}



/******** ASSERT_LESS(t1,t2)
  Assert that T1 <| T2.
  Return false if some sort of error occurred.
*/
int assert_less(t1,t2)
ptr_psi_term t1,t2;
{
  ptr_definition d1,d2; 
  int ok=FALSE;
  deref_ptr(t1);
  deref_ptr(t2);

  if (t1->type==top) {
    Errorline("the top sort '@' may not be a subsort.\n");
    return FALSE;
  }
  if (t1->value || t2->value) {
    Errorline("the declaration '%P <| %P' is illegal.\n",t1,t2);
    return FALSE;
  }
  /* Note: A *full* cyclicity check of the hierarchy is done in encode_types. */
  if (t1->type==t2->type) {
    Errorline("cyclic sort declarations are not allowed.\n");
    return FALSE;
  }
    
  if (!redefine(t1)) return FALSE;
  if (!redefine(t2)) return FALSE;
  d1=t1->type;
  d2=t2->type;
  if (d1->type==predicate || d1->type==function) {
    Errorline("the %T '%s' may not be redefined as a sort.\n",  
              d1->type, d1->symbol);
  }
  else if (d2->type==predicate || d2->type==function) {
    Errorline("the %T '%s' may not be redefined as a sort.\n",  
              d2->type, d2->symbol);
  }
  else {
    d1->type=type;
    d2->type=type;
    types_modified=TRUE;
    make_type_link(d1, d2); /* 1.7 */
    /* d1->parents=cons(d2,d1->parents); */
    /* d2->children=cons(d1,d2->children); */
    ok=TRUE;
  }
  
  return ok;
}



/******** ASSERT_PROTECTED(n,prot)
  Mark all the nodes in the attribute tree N with protect flag prot.
*/
void assert_protected(n,prot)
ptr_node n;
int prot;
{
  ptr_psi_term t;

  if (n) {
    assert_protected(n->left,prot);
    
    t=(ptr_psi_term)n->data;
    deref_ptr(t);
    if (t->type) {
      if (t->type->type==type) {
        Warningline("'%s' is a sort. It can be extended without a declaration.\n",
                    t->type->symbol);
      }
      else if ((int)t->type->rule<MAX_BUILT_INS &&
               (int)t->type->rule>0) {
        if (!prot)
          Warningline("'%s' is a built-in--it has not been made dynamic.\n",
                      t->type->symbol);
      }
      else {
        t->type->protected=prot;
        if (prot) t->type->date&=(~1); else t->type->date|=1;
      }
    }

    assert_protected(n->right,prot);
  }
}



/******** ASSERT_ARGS_NOT_EVAL(n)
  Mark all the nodes in the attribute tree N as having unevaluated arguments,
  if they are functions or predicates.
*/
void assert_args_not_eval(n)
ptr_node n;
{
  ptr_psi_term t;

  if (n) {
    assert_args_not_eval(n->left);
    
    t=(ptr_psi_term)n->data;
    deref_ptr(t);
    if (t->type) {
      if (t->type->type==type) {
        Warningline("'%s' is a sort--only functions and predicates\
 can have unevaluated arguments.\n",t->type->symbol);
      }
      else
        t->type->evaluate_args=FALSE;
    }

    assert_args_not_eval(n->right);
  }
}



/******** ASSERT_DELAY_CHECK(n)
  Assert that the types in the attribute tree N will have their
  properties checked only when they have attributes.  If they
  have no attributes, then no properties are checked.
*/
void assert_delay_check(n)
ptr_node n;
{
  ptr_psi_term t;

  if(n) {
    assert_delay_check(n->left);
    
    t=(ptr_psi_term)n->data;
    deref_ptr(t);
    if (t->type) {
      t->type->always_check=FALSE;
    }

    assert_delay_check(n->right);
  }
}



/******** CLEAR_ALREADY_LOADED()
  Clear the 'already_loaded' flags in all symbol table entries.
  Done at each top level prompt.
*/
void clear_already_loaded(n)
ptr_node n;
{
  ptr_definition d;

  if (n) {
    d=(ptr_definition)n->data;
    d->already_loaded=FALSE;
    clear_already_loaded(n->left);
    clear_already_loaded(n->right);
  }
}



/******** ASSERT_TYPE(t)
  T is the psi_term <|(type1,type2).
  Add that to the type-definitions.
*/
void assert_type(t)
ptr_psi_term t;
{
  ptr_psi_term arg1,arg2;

  get_two_args(t->attr_list,&arg1,&arg2);
  if(arg1==NULL || arg2==NULL) {
    Errorline("bad sort declaration '%P' (%E).\n",t);
  }
  else
    assert_ok=assert_less(arg1,arg2);
}



/******** ASSERT_COMPLICATED_TYPE
  This deals with all the type declarations of the form:
  
  a(attr) <| b.				% (a<|b)
  a(attr) <| b | pred.
  
  a(attr) <| {b;c;d}.			% (a<|b, a<|c, a<|d)
  a(attr) <| {b;c;d} | pred.
  
  a := b(attr).				% (a<|b)
  a := b(attr) | pred.
  
  a := {b(attr1);c(attr2);d(attr3)}.	% (b<|a,c<|a,d<|a)
  a := {b(attr1);c(attr2);d(attr3)} | pred.
*/
void assert_complicated_type(t)
ptr_psi_term t;
{
  ptr_psi_term arg2,typ1,typ2,pred=NULL;
  ptr_list lst;
  int eqflag = equ_tok((*t),":=");
  int ok, any_ok=FALSE;
  
  get_two_args(t->attr_list,&typ1,&arg2);
  
  if (typ1 && arg2) {
    deref_ptr(typ1);
    deref_ptr(arg2);
    typ2=arg2;
    if (!strcmp(arg2->type->symbol,"|")) {
      typ2=NULL;
      get_two_args(arg2->attr_list,&arg2,&pred);
      if (arg2) {
        deref_ptr(arg2);
        typ2=arg2;
      }
    }
    if (typ2) {
      if (typ2->type==disjunction) {
        if (typ1->attr_list && eqflag) {
          Warningline("attributes ignored left of ':=' declaration (%E).\n");
        }
        while (arg2 && arg2->value) {
          lst=(ptr_list)arg2->value;
          arg2=lst->car;
          if (arg2) {
            deref_ptr(arg2);
            if (eqflag) {
              ok=assert_less(arg2,typ1);
              if (ok) any_ok=TRUE;
              if (ok && (arg2->attr_list || pred!=NULL)) {
                add_rule(arg2,pred,type);
              }
            }
            else {
              ok=assert_less(typ1,arg2);
              if (ok) any_ok=TRUE;
              if (ok && arg2->attr_list) {
                Warningline("attributes ignored in sort declaration (%E).\n");
              }
            }
            arg2=lst->cdr;
            if (arg2)
              deref_ptr(arg2);
          }
        }
        assert_ok=TRUE;
      }
      else if (eqflag) {
        if (typ1->attr_list) {
          Warningline("attributes ignored left of ':=' declaration (%E).\n");
        }
        ok=assert_less(typ1,typ2);
        if (ok) any_ok=TRUE;
        typ2->type=typ1->type;
        if (ok && (typ2->attr_list || pred!=NULL))
          add_rule(typ2,pred,type);
        else
          assert_ok=TRUE;
      }
      else {
        if (typ2->attr_list) {
          Warningline("attributes ignored right of '<|' declaration (%E).\n");
        }
        ok=assert_less(typ1,typ2);
        if (ok) any_ok=TRUE;
        if (ok && (typ1->attr_list || pred!=NULL))
          add_rule(typ1,pred,type);
        else
          assert_ok=TRUE;
      }
    }
    else {
      Errorline("argument missing in sort declaration (%E).\n");
    }
  }
  else {
    Errorline("argument missing in sort declaration (%E).\n");
  }
  if (!any_ok) assert_ok=FALSE;
}



/******** ASSERT_ATTRIBUTES(t)
  T is of the form ':: type(attributes) | pred', the attributes must be 
  appended to T's definition, and will be propagated after ENCODING to T's
  subtypes.
*/
void assert_attributes(t)
ptr_psi_term t;
{
  ptr_psi_term arg1,arg2,pred=NULL,typ;
  ptr_definition d;
  
  get_two_args(t->attr_list,&arg1,&arg2);
  
  if (arg1) {
    typ=arg1;
    deref_ptr(arg1);
    if (!strcmp(arg1->type->symbol,"|")) {
      get_two_args(arg1->attr_list,&arg1,&pred);
      if (arg1) {
        typ=arg1;
        deref_ptr(arg1);
      }
    }
    
    if (arg1 && const(*arg1)) {
      if (!redefine(arg1)) return;
      d=arg1->type;
      if (d->type==predicate || d->type==function) {
        Errorline("the %T '%s' may not be redefined as a sort.\n",
                  d->type, d->symbol);
      }
      else {
        d->type=type;
        types_modified=TRUE;
        add_rule(typ,pred,type);
      }
    }
    else {
      Errorline("bad argument in sort declaration '%P' (%E).\n",t);
    }
  }
  else {
    Errorline("sort declaration has no argument (%E).\n");
  }
}



/******** FIND_ADULTS(list,symbol_tree_node)
  Returns the list of all the maximal types (apart from top) in the symbol 
  table. That is, types which have no parents.
  This routine modifies the global variable 'adults'.
*/
void find_adults(n)
ptr_node n;
{
  ptr_definition d;
  ptr_int_list l;

  if(n) {
    find_adults(n->left);
    
    d=(ptr_definition)n->data;
    if(d->type==type && d->parents==NULL) {
      l=HEAP_ALLOC(int_list);
      l->value=(GENERIC)d;
      l->next=adults;
      adults=l;
    }

    find_adults(n->right);
  }
}


/******** INSERT_OWN_PROP(definition)
  Append a type's "rules" (i.e. its own attr. & constr.) to its property list.
  The property list also contains the type's code.
  A type's attributes and constraints are stored in the 'rule' field of the
  definition.
*/
void insert_own_prop(d)
ptr_definition d;
{
  ptr_int_list l;
  ptr_pair_list rule;
  ptr_triple_list *t;
  int flag;

  l=HEAP_ALLOC(int_list);
  l->value=(GENERIC)d;
  l->next=children;
  children=l;

  rule = d->rule;
  while (rule) {
    t= &(d->properties);
    flag=TRUE;
    
    while (flag) {
      if (*t)
        if ((*t)->a==rule->a && (*t)->b==rule->b && (*t)->c==d)
          flag=FALSE;
        else
          t= &((*t)->next);
      else {
        *t = HEAP_ALLOC(triple_list);
        (*t)->a=rule->a;
        (*t)->b=rule->b;
        (*t)->c=d;
        (*t)->next=NULL;
        flag=FALSE;
      }
    } 
    rule=rule->next;
  }
}


/******** INSERT_PROP(definition,prop)
  Append the properties to the definition if they aren't already present.
*/
void insert_prop(d,prop)
ptr_definition d;
ptr_triple_list prop;
{
  ptr_int_list l;
  ptr_triple_list *t;
  int flag;

  l=HEAP_ALLOC(int_list);
  l->value=(GENERIC)d;
  l->next=children;
  children=l;

  while (prop) {
    t= &(d->properties);
    flag=TRUE;
    
    while (flag) {
      if (*t)
        if ((*t)->a==prop->a && (*t)->b==prop->b && (*t)->c==prop->c)
          flag=FALSE;
        else
          t= &((*t)->next);
      else {
        *t = HEAP_ALLOC(triple_list);
        (*t)->a=prop->a;
        (*t)->b=prop->b;
        (*t)->c=prop->c;
        (*t)->next=NULL;
        flag=FALSE;
      }
    } 
    prop=prop->next;
  }
}



/******** PROPAGATE_DEFINITIONS()
  This routine propagates the definition (attributes,predicates) of a type to 
  all its sons.
*/
void propagate_definitions()
{
  ptr_int_list kids;
  ptr_definition d;
  
  adults=NULL;
  find_adults(symbol_table);
  
  while (adults) {
    
    children=NULL;
    
    while (adults) {
      d=(ptr_definition)adults->value;
      
      insert_own_prop(d);
      children=children->next;
      
      kids=d->children;
      
      while(kids) {
        insert_prop(kids->value,d->properties);
        /* if (d->always_check && kids->value)
          ((ptr_definition)kids->value)->always_check=TRUE; */
        kids=kids->next;
      }
      adults=adults->next;
    }
    adults=children;
  }
}



/******************************************************************************

  The following routines implement sort encoding.

*/



/******** COUNT_SORTS(t,c)
  Count the number of sorts in the symbol table T.
*/
int count_sorts(t,c0)
ptr_node t;
int c0;
{
  ptr_definition d;
  int c1;
  
  if (t) {
    c1=count_sorts(t->left,c0);
    d=(ptr_definition)t->data;
    if (d->type==type) c1++;
    c0=count_sorts(t->right,c1);
  }
  return c0;
}



/******** CLEAR_CODING(t)
  Clear the bit-vector coding of the sorts in symbol_table T.
*/
void clear_coding(t)
ptr_node t;
{
  ptr_definition d;
  
  if (t) {
    clear_coding(t->left);
    d=(ptr_definition)t->data;
    if (d->type==type) d->code=NOT_CODED;
    clear_coding(t->right);
  }
}



/******** LEAST_SORTS(t)
  From symbol table T, build the list of terminals (i.e. sorts with no
  children) in nothing->parents.
*/
void least_sorts(t)
ptr_node t;
{
  ptr_definition d;
  
  if (t) {
    least_sorts(t->left);
    d=(ptr_definition)t->data;
    if (d->type==type && d->children==NULL && d!=nothing)
      nothing->parents=cons(d,nothing->parents);
    least_sorts(t->right);
  }
}
  


/******** ALL_SORTS(t)
  From symbol table T, build a list of all sorts (except nothing)
  in nothing->parents.
*/
void all_sorts(t)
ptr_node t;
{
  ptr_definition d;
  
  if (t) {
    all_sorts(t->left);
    d=(ptr_definition)t->data;
    if (d->type==type && d!=nothing)
      nothing->parents=cons(d,nothing->parents);
    all_sorts(t->right);
  }
}
  


/******** TWO_TO_THE(p)
  Return the code worth 2^p.
*/
ptr_int_list two_to_the(p)
int p;
{
  ptr_int_list result,code;
  int v=1;

  code=HEAP_ALLOC(int_list);
  code->value=0;
  code->next=NULL;
  result=code;
  
  while (p>=INT_SIZE) {
    code->next=HEAP_ALLOC(int_list);
    code=code->next;
    code->value=0;
    code->next=NULL;
    p=p-INT_SIZE;
  }

  v= v<<p ;
  code->value=(GENERIC)v;

  return result;
}


/******** copyTypeCode(code)
  returns copy of code on the heap
*/
ptr_int_list copyTypeCode(u)
ptr_int_list u;
{
  ptr_int_list code;

  code = HEAP_ALLOC(int_list);
  code->value=0;
  code->next=NULL;

  or_codes(code, u);

  return code;
}



/******** OR_CODES(code1,code2)
  Performs CODE1 := CODE1 or CODE2,
  'or' being the binary logical operator on bits.
*/
void or_codes(u,v)
ptr_int_list u,v;
{
  while (v) {
    u->value= (GENERIC)(((int)(u->value)) | ((int)(v->value)));
    v=v->next;
    if (u->next==NULL && v) {
      u->next=HEAP_ALLOC(int_list);
      u=u->next;
      u->value=0;
      u->next=NULL;
    }
    else
      u=u->next;
  }
}



/******** EQUALIZE_CODES(t,w)
  Make sure all codes are w words long, by increasing the length of the
  shorter ones.
  This simplifies greatly the bitvector manipulation routines.
  This operation should be done after encoding.
  For correct operation, w>=maximum number of words used for a code.
*/
equalize_codes(t,w)
ptr_node t;
int w;
{
  ptr_definition d;
  ptr_int_list c,*ci;
  int i;

  if (t) {
    equalize_codes(t->left,w);
    equalize_codes(t->right,w);
    d = (ptr_definition)t->data;
    if (d->type==type) {
      c = (ptr_int_list)d->code;
      ci = &(ptr_int_list)d->code;
  
      /* Count how many words have to be added */
      while (c) {
        ci= &(c->next);
        c=c->next;
        w--;
      }
      assert(w>=0);
      /* Add the words */
      for (i=0; i<w; i++) {
        *ci = HEAP_ALLOC(int_list);
        (*ci)->value=0;
        ci= &((*ci)->next);
      }
      (*ci)=NULL;
    }
  }
}



/******** MAKE_TYPE_LINK(t1,t2)
  Assert that T1 <| T2, this is used to initialise the built_in type relations
  so that nothing really horrible happens if the user modifies built-in types
  such as INT or LIST.
  This routine also makes sure that top has no links.
*/
void make_type_link(t1,t2)
ptr_definition t1, t2;
{
  if (t2!=top && !type_member(t2,t1->parents))
    t1->parents=cons(t2,t1->parents);
  if (t2!=top && !type_member(t1,t2->children))
    t2->children=cons(t1,t2->children);
}




/******** TYPE_MEMBER(t,tlst)
  Return TRUE iff type t is in the list tlst.
*/

int type_member(t,tlst)
ptr_definition t;
ptr_int_list tlst;
{
  while (tlst) {
   if (t==(ptr_definition)tlst->value) return TRUE;
   tlst=tlst->next;
  }
  return FALSE;
}


void perr_sort(d)
ptr_definition d;
{
  perr_s("%s",d->symbol);
}

void perr_sort_list(anc)
ptr_int_list anc;
{
  if (anc) {
    perr_sort_list(anc->next);
    if (anc->next) perr(" <| ");
    perr_sort((ptr_definition)anc->value);
  }
}

void perr_sort_cycle(anc)
ptr_int_list anc;
{
  perr_sort((ptr_definition)anc->value);
  perr(" <| ");
  perr_sort_list(anc);
}



/******** TYPE_CYCLICITY(d,anc)
  Check cyclicity of type hierarchy.
  If cyclic, return a TRUE error condition and print an error message
  with a cycle.
*/
int type_cyclicity(d,anc)
ptr_definition d;
ptr_int_list anc;
{
  ptr_int_list p=d->parents;
  ptr_definition pd;
  int errflag;
  int_list anc2;

  while (p) {
    pd=(ptr_definition)p->value;
    /* If unmarked, mark and recurse */
    if (pd->code==NOT_CODED) {
      pd->code = (ptr_int_list)TRUE;
      anc2.value=(GENERIC)pd;
      anc2.next=anc;
      errflag=type_cyclicity(pd,&anc2);
      if (errflag) return TRUE;
    }
    /* If marked, check if it's in the ancestor list */
    else {
      if (type_member(pd,anc)) {
        perr("*** Error: there is a cycle in the sort hierarchy.\n");
        perr("*** Cycle: [");
        perr_sort_cycle(anc);
        perr("]\n");
        exit_life(TRUE);
        return TRUE;
      }
    }
    p=p->next;
  }
  return FALSE;
}



/******** PROPAGATE_ALWAYS_CHECK(d)
  Recursively set the always_check flag to 'FALSE' for all d's
  children.  Continue until encountering only 'FALSE' values. 
  Return a TRUE flag if a change was made somewhere (for the
  closure calculation).
*/
void propagate_always_check(d,ch)
ptr_definition d;
int *ch;
{
  ptr_int_list child_list;
  ptr_definition child;

  child_list = d->children;
  while (child_list) {
    child = (ptr_definition)child_list->value;
    if (child->always_check) {
      child->always_check = FALSE;
      *ch = TRUE;
      propagate_always_check(child,ch);
    }
    child_list = child_list->next;
  }
}



/******** ONE_PASS_ALWAYS_CHECK(t,ch)
  Go through the symbol table & propagate all FALSE always_check
  flags of all sorts to their children.  Return a TRUE flag
  if a change was made somewhere (for the closure calculation).
*/
void one_pass_always_check(t,ch)
ptr_node t;
int *ch;
{
  ptr_definition d;

  if (t) {
    one_pass_always_check(t->left,ch);
    d = (ptr_definition)t->data;
    if (d->type==type && !d->always_check) {
      propagate_always_check(d,ch);
    }
    one_pass_always_check(t->right,ch);
  }
}



/******** INHERIT_ALWAYS_CHECK()
  The 'always_check' flag, if false, should be propagated to a sort's
  children.  This routine does a closure on this propagation operation
  for all declared sorts.
*/
void inherit_always_check()
{
  int change;

  do {
    change=FALSE;
    one_pass_always_check(symbol_table,&change);
  } while (change);
}



/******** ENCODE_TYPES()
  This routine performs type-coding using transitive closure.
  First any previous coding is undone.
  Then a new encryption is performed.

  Some of these routines loop indefinitely if there is a circular type
  definition (an error should be reported but it isn't implemented (but it's
  quite easy to do)).
*/
void encode_types()
{
  int p=0,i,possible,ok=TRUE;
  ptr_int_list layer,l,kids,dads,code;
  ptr_definition xdef,kdef,ddef,err;
  
  if (types_modified) {
    
    nothing->parents=NULL;
    nothing->children=NULL;
    
    top->parents=NULL;
    top->children=NULL;

    /* The following definitions are vital to avoid crashes */
    make_type_link(integer,real);

    make_type_link(alist,list_object);
    make_type_link(disjunction,list_object);
    /* make_type_link(conjunction,list_object); 19.8 */

    make_type_link(true,boolean);
    make_type_link(false,boolean);

    /* These just might be useful */
    make_type_link(quoted_string,built_in);
    make_type_link(boolean,built_in);
    make_type_link(list_object,built_in);
    make_type_link(real,built_in);
    
    type_count=count_sorts(symbol_table,-1); /* bottom does not count */
    clear_coding(symbol_table);
    nothing->parents=NULL; /* Must be cleared before all_sorts */
    all_sorts(symbol_table);
    if (type_cyclicity(nothing,NULL)) {
      clear_coding(symbol_table);
      return;
    }
    clear_coding(symbol_table);
    nothing->parents=NULL; /* Must be cleared before least_sorts */
    least_sorts(symbol_table);
    
    nothing->code=NULL;
    
    Infoline("*** Codes:\n%C= %s\n", NULL, nothing->symbol);
    
    gamma_table=(ptr_definition *) heap_alloc(type_count*sizeof(definition));
    
    layer=nothing->parents;
    
    while (layer) {
      l=layer;
      do {
        xdef=(ptr_definition)l->value;
        if (xdef->code==NOT_CODED && xdef!=top) {
          
          kids=xdef->children;
          code=two_to_the(p);
          
          while (kids) {
            kdef=(ptr_definition)kids->value;
            or_codes(code,kdef->code);
            kids=kids->next;
          }
          
          xdef->code=code;
          gamma_table[p]=xdef;
          
          Infoline("%C = %s\n", code, xdef->symbol);
          p=p+1;
        }
        
        l=l->next;
        
      } while (l);
      
      l=layer;
      layer=NULL;
      
      do {
        xdef=(ptr_definition)l->value;
        dads=xdef->parents;
        
        while (dads) {
          ddef=(ptr_definition)dads->value;
          if(ddef->code==NOT_CODED) {
            
            possible=TRUE;
            kids=ddef->children;
            
            while(kids && possible) {
              kdef=(ptr_definition)kids->value;
              if(kdef->code==NOT_CODED)
                possible=FALSE;
              kids=kids->next;
            }
            if(possible)
              layer=cons(ddef,layer);
          }
          dads=dads->next;
        }
        l=l->next;
      } while(l);
    }
    
    top->code=two_to_the(p);
    for (i=0;i<p;i++)
      or_codes(top->code,two_to_the(i));

    gamma_table[p]=top;
    
    Infoline("%C = @\n\n", top->code);
    equalize_codes(symbol_table,p/32+1);

    propagate_definitions();

    /* Inherit 'FALSE' always_check flags to all types' children */
    inherit_always_check();
    
    Infoline("*** Encoding done, %d sorts\n",type_count);
    
    if (overlap_type(real,quoted_string)) {
      Errorline("the sorts 'real' and 'string' are not disjoint.\n");
      ok=FALSE;
    }
    
    if (overlap_type(real,alist)) {
      Errorline("the sorts 'real' and 'list' are not disjoint.\n");
      ok=FALSE;
    }
    
    if (overlap_type(alist,quoted_string)) {
      Errorline("the sorts 'list' and 'string' are not disjoint.\n");
      ok=FALSE;
    }
    
    if (!ok) {
      perr("*** Internal problem:\n");
      perr("*** Wild_Life may behave abnormally because some basic types\n");
      perr("*** have been defined incorrectly.\n\n");
    }

    types_modified=FALSE;
    types_done=TRUE;
  }
}



/******** PRINT_CODES()
  Print all the codes.
*/
void print_codes()
{
  int i;

  for (i=0; i<type_count; i++) {
    outputline("%C = %s\n", gamma_table[i]->code, gamma_table[i]->symbol);
  }
}



/******** GLB_VALUE(result,f,c,value1,value2,value)
  Do the comparison of the value fields of two psi-terms.
  This is used in conjunction with glb_code to correctly implement
  completeness for disequality for psi-terms with non-NULL value fields.
  This must be preceded by a call to glb_code, since it uses the outputs
  of that call.

  result   result of preceding glb_code call (non-NULL iff non-empty intersec.)
  f,c      sort intersection (sortflag & code) of preceding glb_code call.
  value1   value field of first psi-term.
  value2   value field of second psi-term.
  value    output value field (if any).
*/
int glb_value(result,f,c,value1,value2,value)
int result;
int f;
GENERIC c;
GENERIC value1,value2,*value;
{
  ptr_int_list code;

  if (!result) return FALSE;
  if (value1==NULL) {
    *value=value2;
    return TRUE;
  }
  if (value2==NULL) {
    *value=value1;
    return TRUE;
  }
  /* At this point, both value fields are non-NULL */
  /* and must be compared. */

  /* Get a pointer to the sort code */
  code = f ? ((ptr_definition)c)->code : (ptr_int_list)c;

  /* This rather time-consuming analysis is necessary if both objects */
  /* have non-NULL value fields.  Note that only those objects with a */
  /* non-NULL value field needed for disentailment are looked at.     */
  if (sub_CodeType(code,real->code)) {
    *value=value1;
    return (*(REAL *)value1 == *(REAL *)value2);
  }
  else if (sub_CodeType(code,quoted_string->code)) {
    *value=value1;
    return (!strcmp((char *)value1,(char *)value2));
  }
  else if (sub_CodeType(code,list_object->code)) {
    /* For lists, return TRUE if both are nil or both are non-nil */
    *value=value1;
    return ((((ptr_list)value1)->car==NULL)==(((ptr_list)value2)->car==NULL));
  }
  else {
    /* All other sorts with 'value' fields always return TRUE, that is, */
    /* the value field plays no role in disentailment. */
    *value=value1;
    return TRUE;
  }
}



/******** GLB_CODE(f1,c1,f2,c2,f3,c3) (21.9)
  Calculate glb of two type codes C1 and C2, put result in C3.
  Return a result value (see comments of glb(..)).

  Sorts are stored as a 'Variant Record':
    f1==TRUE:  c1 is a ptr_definition (an interned symbol).
    f1==FALSE: c1 is a ptr_int_list (a sort code).
  The result (f3,c3) is also in this format.
  This is needed to correctly handle psi-terms that don't have a sort code
  (for example, functions, predicates, and singleton sorts).
  The routine handles a bunch of special cases that keep f3==TRUE.
  Other than that, it is almost a replica of the inner loop of glb(..).
*/
int glb_code(f1,c1,f2,c2,f3,c3)
int f1,f2,*f3;
GENERIC c1,c2,*c3;
{
  int result=0;
  int v1,v2,v3;
  ptr_int_list cd1,cd2,*cd3; /* sort codes */

  /* First, the cases where c1 & c2 are ptr_definitions: */
  if (f1 && f2) {
    if ((ptr_definition)c1==(ptr_definition)c2) {
      *c3=c1;
      result=1;
    }
    else if ((ptr_definition)c1==top) {
      *c3=c2;
      if ((ptr_definition)c2==top)
        result=1;
      else
        result=3;
    }
    else if ((ptr_definition)c2==top) {
      *c3=c1;
      result=2;
    }
    /* If both inputs are either top or the same ptr_definition */
    /* then can return quickly with a ptr_definition. */
    if (result) {
      *f3=TRUE; /* c3 is ptr_definition (an interned symbol) */
      return result;
    }
  }
  /* In the other cases, can't return with a ptr_definition: */
  cd1=(ptr_int_list)(f1?(GENERIC)((ptr_definition)c1)->code:c1);
  cd2=(ptr_int_list)(f2?(GENERIC)((ptr_definition)c2)->code:c2);
  cd3=(ptr_int_list*)c3;
  *f3=FALSE; /* cd3 is ptr_int_list (a sort code) */
  if (cd1==NOT_CODED) {
    if (cd2==NOT_CODED) {
      if (c1==c2) {
        *cd3=cd1;
        result=1;
      }
      else
        result=0;
    }
    else if (cd2==top->code) {
      *cd3=cd1;
      result=2;
    }
    else
      result=0;
  }
  else if (cd1==top->code) {
    if (cd2==top->code) {
      *cd3=cd1;
      result=1;
    }
    else {
      *cd3=cd2;
      result=3;
    }
  }
  else if (cd2==NOT_CODED)
    result=0;
  else if (cd2==top->code) {
    *cd3=cd1;
    result=2;
  }
  else while (cd1 && cd2) {
    /* Bit operations needed only if c1 & c2 coded & different from top */
    *cd3 = STACK_ALLOC(int_list);
    (*cd3)->next=NULL;
    
    v1=(int)(cd1->value);
    v2=(int)(cd2->value);
    v3=v1 & v2;
    (*cd3)->value=(GENERIC)v3;
    
    if (v3) {
      if (v3<v1 && v3<v2)
        result=4;
      else if (result!=4)
        if (v1<v2)
          result=2;
        else if (v1>v2)
          result=3;
        else
          result=1;
    }
    else if (result)
      if (v1 || v2)
        result=4;
        
    cd1=cd1->next;
    cd2=cd2->next;
    cd3= &((*cd3)->next);
  }

  return result;
}



/******** GLB(t1,t2,t3)
  This function returns the Greatest Lower Bound of two types T1 and T2 in T3.
  
  T3 = T1 /\ T2

  If T3 is not a simple type then C3 is its code, and T3=NULL.
  
  It also does some type comparing, and returns
  
  0 if T3 = bottom
  1 if T1 = T2
  2 if T1 <| T2
  3 if T1 |> T2
  4 otherwise ( T3 strictly <| T1 and T3 strictly <| T2)
  
  These results are used for knowing when to inherit properties or release
  residuations.
  The t3 field is NULL iff a new type is needed to represent the
  result.
*/
int glb(t1,t2,t3,c3)
ptr_definition t1;
ptr_definition t2;
ptr_definition  *t3;
ptr_int_list *c3;
{
  ptr_int_list c1,c2;
  int result=0;
  int v1,v2,v3;

  *c3=NULL;
  
  if (t1==t2) { 
    result=1;
    *t3= t1;
  }
  else if (t1==top) {
    *t3= t2;
    if (t2==top)
      result=1;
    else
      result=3;
  }
  else if (t2==top) {
    result=2;
    *t3= t1;
  }
  else {
    c1=t1->code;
    c2=t2->code;
    if (c1!=NOT_CODED && c2!=NOT_CODED) {
      result=0;
      while (c1 && c2) {

        *c3 = STACK_ALLOC(int_list);
        (*c3)->next=NULL;

        v1=(int)(c1->value);
        v2=(int)(c2->value);
        v3=v1 & v2;

        (*c3)->value=(GENERIC)v3;

        if (v3) {
          if (v3<v1 && v3<v2)
            result=4;
          else if (result!=4)
            if (v1<v2)
              result=2;
            else if (v1>v2)
              result=3;
            else
              result=1;
        }
        else if (result)
          if (v1 || v2)
            result=4;

        c1=c1->next;
        c2=c2->next;
        c3= &((*c3)->next);
      }
      *t3=NULL;
    }
  }
  
  if (!result) *t3=nothing;
  
  return result;
}



/******** OVERLAP_TYPE(t1,t2)
  This function returns TRUE if GLB(t1,t2)!=bottom.
  This is essentially the same thing as GLB, only it's faster 'cause we don't
  care about the resulting code.
*/
int overlap_type(t1,t2)
ptr_definition t1;
ptr_definition t2;
{
  ptr_int_list c1,c2;
  int result=TRUE;
  
  if (t1!=t2 && t1!=top && t2!=top) {
    
    c1=t1->code;
    c2=t2->code;
    result=FALSE;

    if (c1!=NOT_CODED && c2!=NOT_CODED) {     
      while (!result && c1 && c2) {          
        result=(((int)(c1->value)) & ((int)(c2->value)));
        c1=c1->next;
        c2=c2->next;
      }
    }
  }
  
  /*
  printf("overlap_type(%s,%s) => %d\n",t1->def->symbol,t2->def->symbol,result);
  */
  
  return result;
}


/******** SUB_CodeType(c1,c2)
  Return TRUE if code C1 is <| than type C2, that is if type represented
  by code C1 matches type represented by C2.

  We already know that t1 and t2 are not top.
*/
int sub_CodeType(c1,c2)
ptr_int_list c1;
ptr_int_list c2;
{
  if (c1!=NOT_CODED && c2!=NOT_CODED) {
    while (c1 && c2) {
      if ((int)c1->value & ~(int)c2->value) return FALSE;
      c1=c1->next;
      c2=c2->next;
    }
  }
  else
    return FALSE;

  return TRUE;
}



/******** SUB_TYPE(t1,t2)
  Return TRUE if type T1 is <| than type T2, that is if T1 matches T2.
*/
int sub_type(t1,t2)
ptr_definition t1;
ptr_definition t2;
{
  if (t1!=t2)
    if (t2!=top)
    {
      if (t1==top)
        return FALSE;
      else
        return sub_CodeType(t1->code, t2->code);
    }
  return TRUE;
}



/******** MATCHES(t1,t2,s)
  Returns TRUE if GLB(t1,t2)!=bottom.
  Sets S to TRUE if type T1 is <| than type T2, that is if T1 matches T2.
*/
int matches(t1,t2,smaller)
ptr_definition t1;
ptr_definition t2;
int *smaller;
{
  ptr_int_list c1,c2;
  int result=TRUE;
  
  *smaller=TRUE;
  
  if (t1!=t2)
    if (t2!=top)
      if (t1==top)
        *smaller=FALSE;
      else {
        c1=t1->code;
        c2=t2->code;
        result=FALSE;
        
        if (c1!=NOT_CODED && c2!=NOT_CODED) {          
          while (c1 && c2) {          
            if ((int)c1->value &  (int)c2->value) result=TRUE;
            if ((int)c1->value & ~(int)c2->value) *smaller=FALSE;
            c1=c1->next;
            c2=c2->next;
          }
        }
        else
          *smaller=FALSE;
      }
  
  return result;
}



/******** STRICT_MATCHES(t1,t2,s)
  Almost the same as matches, except that S is set to TRUE only
  if the type of t1 is strictly less than the type of t2.
  Because of the implementation of ints, reals, strings, and lists,
  this has to take the value field into account, and thus must
  be passed the whole psi-term.
*/
int strict_matches(t1,t2,smaller)
ptr_psi_term t1;
ptr_psi_term t2;
int *smaller;
{
  int result,sm;

  result=matches(t1->type,t2->type,&sm);

  if (sm) {
    /* At this point, t1->type <| t2->type */
    if (t1->type==t2->type) {
      /* Same types: strict only if first has a value & second does not */
      if (t1->value!=NULL && t2->value==NULL)
        sm=TRUE;
      else
        sm=FALSE;
    }
    else {
      /* Different types: the first must be strictly smaller */
      sm=TRUE;
    }
  }

  *smaller=sm;
  return result;
}



/******** BIT_LENGTH(c)
  Returns the number of bits needed to code C. That is the rank of the first
  non NULL bit of C.
  
  Examples:
  C= 1001001000   result=7
  C= 10000        result=1
  C= 0000000      result=0
  
*/
int bit_length(c)
ptr_int_list c;
{
  unsigned int p=0,dp=0,v=0,dv=0;
  
  while (c) {
    v=(int)c->value;
    if(v) {
      dp=p;
      dv=v;
    }
    c=c->next;
    p=p+INT_SIZE;
  }
  
  while (dv) {
    dp++;
    dv=dv>>1;
  }
  
  return dp;
}



/******** DECODE(c)
  Returns a list of the symbol names which make up the disjunction whose
  code is C.
*/

ptr_int_list decode(c)
ptr_int_list c;
{
  ptr_int_list c2,c3,c4,result=NULL,*prev;
  int p;
  
  p=bit_length(c);
  
  while (p) {
    p--;
    c2=gamma_table[p]->code;
    result=cons(gamma_table[p],result);
    prev= &c4;
    *prev=NULL;
    
    while (c2) {
      c3=STACK_ALLOC(int_list);
      *prev=c3;
      prev= &(c3->next);
      *prev=NULL;
      
      c3->value=(GENERIC)(((int)(c->value)) & ~((int)(c2->value)));
      
      c=c->next;
      c2=c2->next;
    }
    
    c=c4;
    p=bit_length(c);
  }
  
  return result;
}
