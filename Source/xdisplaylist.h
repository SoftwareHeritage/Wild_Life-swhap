/* Copyright 1991 Digital Equipment Corporation.
** All Rights Reserved.
*****************************************************************/

#ifdef X11

#include "list.h"

#define xDefaultFont -1
#define xDefaultLineWidth -1

typedef enum {DRAW_LINE, DRAW_RECTANGLE, DRAW_ARC, DRAW_POLYGON,
	      FILL_RECTANGLE, FILL_ARC, FILL_POLYGON,
	      DRAW_STRING, DRAW_IMAGE_STRING} Action;


typedef struct _Line
{
    Action action;
    ListLinks links;
    int	x0, y0, x1, y1;
    long function;
    long color;
    long linewidth;
} Line;

    
typedef struct _Rectangle
{
    Action action;
    ListLinks links;
    int	x, y, width, height;
    long function;
    long color;
    long linewidth;
} Rectangle;


typedef struct _Arc
{
    Action action;
    ListLinks links;
    int	x, y, width, height, startangle, arcangle;
    long function;
    long color;
    long linewidth;
} Arc;


typedef struct _String
{
    Action action;
    ListLinks links;
    int	x, y;
    char *str;
    long function;
    long color;
    long font;
} String;

    
typedef struct _Polygon
{
    Action action;
    ListLinks links;
    XPoint *points;
    long npoints;
    long function;
    long color;
    long linewidth;
} Polygon;


typedef union _DisplayElt
{
    Action action;
    Line line;
    Rectangle rectangle;
    Arc arc;
    String str;
    Polygon polygon;
} DisplayElt;

typedef DisplayElt *RefDisplayElt;


/*****************************************/


extern ListHeader * x_display_list ();
extern void x_set_gc ();
extern void x_record_line ();
extern void x_record_arc ();
extern void x_record_rectangle ();
extern void x_record_string ();
extern void x_record_polygon ();
extern void x_refresh_window ();
extern void x_free_display_list ();

#endif

