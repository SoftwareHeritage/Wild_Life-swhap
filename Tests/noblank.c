
#include <stdio.h>

/* Remove all blanks from the input: */
main()
{

  char c;

  while ((c=getc(stdin))!=EOF)
    if (c!=' ') putc(c,stdout);
}
