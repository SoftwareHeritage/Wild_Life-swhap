/*									tab:4
 *
 * lub.c - find least upper bound of the root sorts of two psi terms
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
 *
 * Author: 			Seth Copen Goldstein
 * Version:			26
 * Creation Date:	Fri Jun  5 12:14:39 1992
 * Filename:		lub.c
 * History:
 */
static char _version_string_[] = "\nVersion:1:lub.c\0\n";

#include "extern.h"
#include "login.h"
#include "trees.h"
#include "print.h"
#include "memory.h"
#include "error.h"
#include "token.h"

extern ptr_definition built_in;

ptr_int_list appendIntList(tail, more)
ptr_int_list tail;				/* attach copies of more to tail */
ptr_int_list more;
{
	while (more)
	{
		tail->next = STACK_ALLOC(int_list);
		tail= tail->next;
		tail->value = more->value;
		tail->next = NULL;
		more = more->next;
	}
	return tail;
}

static int bfs(p, ans, pattern, flags)
ptr_definition p;
ptr_int_list ans;
ptr_int_list pattern;
int *flags;
{
	ptr_int_list head = STACK_ALLOC(int_list);
	ptr_int_list tail;
	ptr_int_list par;
	int len;
	int found = 0;
	
	if (p == top)
	{
		or_codes(ans, top);
		return;
	}

/*	print_code(pattern);*/
/*	printf("\n");*/

	par = p->parents;
	if (par == NULL)
		return 0;				/* only parent is top */
	
	assert(par->value != NULL);

	head->value = par->value;
	head->next  = NULL;
	par = par->next;
	tail = appendIntList(head, par);

	while (head)
	{
/*		pc(head->value);*/
		len = bit_length(((ptr_definition )head->value)->code);
		if (!flags[len])
		{
			/* we havn't checked this type before */
			
			if (!((ptr_definition )head->value == top) &&
				!((ptr_definition )head->value == built_in) &&
				(sub_CodeType(pattern,((ptr_definition)head->value)->code)))
			{
				or_codes(ans, ((ptr_definition)head->value)->code);
/*				print_code(ans);*/
/*				printf("ans\n");*/
				found++;
			}
			else
				tail = appendIntList(tail,
									 ((ptr_definition )head->value)->parents);
			flags[len] = 1;
		}
		head = head->next;
	}
	return found;
}


/******************************************/
/* make a decoded type list from one type */
/******************************************/

static ptr_int_list makeUnitList(x)
ptr_definition x;
{
	ptr_int_list ans;

	ans = STACK_ALLOC(int_list);
	ans->value = (GENERIC )x;
	ans->next = NULL;
	return ans;
}

/*****************************************************************************/
/* returns a decoded type list of the root sorts that make up the least upper
 * bound of the two terms, a &b.  Deals with  speacial cases of integers,
 * strings, etc.
 */
/*****************************************************************************/

ptr_int_list lub(a,b,pp)
ptr_psi_term a;
ptr_psi_term b;
ptr_psi_term *pp;
{
	extern int type_count;		/* the number of sorts in the hierarchy */
	ptr_definition ta;			/* type of psi term a */
	ptr_definition tb;			/* type of psi term b */
	int *flags;					/* set to 1 if this type has been checked in
								 * the lub search.
								 */
	ptr_int_list ans;
	ptr_int_list pattern;
	int found;
	
	ta = a->type;
	tb = b->type;
	
	/* special cases first */
	
	if (isValue(a) && isValue(b) && sub_type(ta,tb) && sub_type(tb,ta))
	{
		/* special case of two values being of same type.  Check that they
		 * might actually be same value before returning the type
		 */
		if (isSubTypeValue(a, b))
		{
			/* since we alreadyuu know they are both values, isSubTypeValue
			 * returns TRUE if they are same value, else false
			 */
			
			*pp = a;
			return NULL;
		}
	}
	
	if (sub_type(ta, tb)) return makeUnitList(tb);
	if (sub_type(tb, ta)) return makeUnitList(ta);

	/* ta has the lub of tb&ta without the high bit set, search upwards for a
	 * type that has the same lower bits as ta
	 */

	/* get the pattern to search for */
	
	pattern = copyTypeCode(ta->code);
	or_codes(pattern, tb->code);		/* pattern to search for */
	ans = copyTypeCode(pattern);		/* resulting pattern */
	
	/* initialize the table to be non-searched */
	
	flags = (int *)stack_alloc(sizeof(int) * type_count);
	memset(flags, 0, sizeof(int) * type_count);

	/* now do a breadth first search for each of arg1 and arg2 */

	found  = bfs(ta, ans, pattern, flags);
	found += bfs(tb, ans, pattern, flags);

	if (found)
		ans = decode(ans);
	else
		ans = makeUnitList(top);
	
	return ans;
}


