/* Copyright 1991 Digital Equipment Corporation.
** All Rights Reserved.
*****************************************************************/

#ifdef X11

#include <stdio.h>
#include <ctype.h>
#include <malloc.h>
#include <sys/types.h>
#include <sys/time.h>
#include <sys/ioctl.h>

#include <X11/Xlib.h>
#include <X11/Xutil.h>
#include <X11/keysym.h>

#include "extern.h"
#include "print.h"
#include "built_ins.h"
#include "types.h"
#include "trees.h"
#include "lefun.h"
#include "login.h"
#include "error.h"
#include "memory.h"
#include "templates.h"
#include "xpred.h"
#include "xdisplaylist.h"

#include "life_icon"

/*****************************************/


#define stdin_fileno fileno (stdin)
#define CR 0x0d
#define BS 0x08


/* a closure for enum xevents_list */
typedef struct _EventClosure
{
    int display;
    int window;
    int mask;
    ptr_psi_term beginSpan;
} EventClosure;


/*****************************************/

extern FILE *input_stream;
extern int line_count;
extern int start_of_line;
extern int saved_char; /* 11.2 */
extern int old_saved_char; /* 11.2 */

extern char **arg_v;
extern int arg_c;

/*****************************************/

ptr_psi_term xevent_existing = NULL;
ptr_psi_term xevent_list = NULL;

ptr_definition xevent, xkeyboard_event, xmouse_button, 
               xexpose_event, xdestroy_event, 
               xdisplay, xdrawable, xwindow, xpixmap, 
               xgc, xdisplaylist;

int x_window_creation = FALSE;

/*****************************************/

static int x_types[] = {
    KeyPress,
    KeyRelease,
    ButtonPress,
    ButtonRelease,
    EnterNotify,
    LeaveNotify,
    LeaveNotify,    
    LeaveNotify,
    LeaveNotify,
    LeaveNotify,
    LeaveNotify,
    LeaveNotify,
    LeaveNotify,
    LeaveNotify,
    KeymapNotify,
    Expose,
    VisibilityNotify,
    0, /* StructureNotify */
    ResizeRequest,
    0, /* SubstructureNotifyMask */
    0, /* SubstructureRedirectMask */
    0, /* FocusChangeMask */
    PropertyNotify,
    ColormapNotify
};


/*****************************************************************/
/* Macros */

#define DrawableGC(w) (GC)GetIntAttr (GetPsiAttr (w, "graphic_context"), "id")
#define WindowDisplayList(w) GetIntAttr (GetPsiAttr (w, "display_list"), "id")

/*****************************************************************/
/* Static */
/* handle the errors X */

static int x_handle_error (display, x_error)
Display *display;
XErrorEvent *x_error;
{
    char msg[128];
    XGetErrorText (display, x_error->error_code, msg, 128);
    Errorline ("(X Error) %s.\n", msg);
/* don't use abort_life(TRUE) because it tries to destroy windows ...
   and loops because the window is yet in the stack !!
   jch - Fri Aug  7 17:58:27 MET DST 1992
*/
    exit_life (TRUE);
}


static int x_handle_fatal_error (display)
Display *display;
{
    Errorline ("Fatal X Error.\n");
    exit_life (TRUE);
}

/*****************************************************************/
/* Utility */
/* unify psi_term T to the integer value V */
/* could be in builtins.c */

int unify_int_result (t, v)
ptr_psi_term t;
int v;
{
    int smaller;
    int success=TRUE;


    deref_ptr (t);
    push_ptr_value (int_ptr, &(t->value));
    t->value = heap_alloc (sizeof(REAL));
    *(REAL *) t->value = v;
  
    matches (t->type, integer, &smaller);
  
    if (!smaller) 
    {
	push_ptr_value (def_ptr, &(t->type));
	t->type = integer;
	t->status = 0;
    }
    else
        success = FALSE;
  
    if (success) 
    {
	i_check_out (t);
	if (t->resid)
	    release_resid (t);
    }
  
    return success;
}


/*****************************************************************/
/* Static */
/* build a psi-term of type t with a feature f of value v */

static ptr_psi_term NewPsi (t, f, v)
ptr_definition t;
char * f;
int v;
{
    ptr_psi_term p;

    p = stack_psi_term (4);
    p->type = t;
    stack_add_int_attr (p, f, v);
    return p;
}


/*****************************************************************/
/* Utilities */
/* return the value of the attribute attributeName on the psi-term psiTerm */

int GetIntAttr (psiTerm, attributeName)

ptr_psi_term psiTerm;
char *attributeName;
{
    ptr_node nodeAttr;
    ptr_psi_term psiValue;
    

    if ((nodeAttr = find (featcmp, attributeName, psiTerm->attr_list)) == NULL)
    {
        Errorline ("in GetIntAttr: no attribute name on psi-term ?\n");
	exit_life (TRUE);
    }

    if ((psiValue = (ptr_psi_term) nodeAttr->data) == NULL)

    {
        Errorline ("in GetIntAttr: no value on psi-term ?\n");
	exit_life (TRUE);
    }

    return *(REAL *) psiValue->value;
}


/*****************************************************************/
/* Utilities */
/* return the psi-term of the attribute attributeName on the psi-term psiTerm */

ptr_psi_term GetPsiAttr (psiTerm, attributeName)

ptr_psi_term psiTerm;
char *attributeName;
{
    ptr_node nodeAttr;
    ptr_psi_term psiValue;
    

    if ((nodeAttr = find (featcmp, attributeName, psiTerm->attr_list)) == NULL)
    {
        Errorline ("in GetPsiAttr: no attribute name on psi-term ?\n");
	exit_life (TRUE);
    }

    if ((psiValue = (ptr_psi_term) nodeAttr->data) == NULL)
    {
        Errorline ("in GetPsiAttr: no value on psi-term ?\n");
	exit_life (TRUE);
    }

    return psiValue;
}

/*****************************************************************/
/* Static */
/* resize the pixmap of the window */

static void ResizePixmap (psi_window, display, window, width, height)

ptr_psi_term psi_window;
Display *display;
Window window;
unsigned int width, height;
{
    Pixmap pixmap;
    GC pixmapGC;
    ptr_psi_term psiPixmap, psiPixmapGC;
    XGCValues gcvalues;
    XWindowAttributes attr;

    /* free the old pixmap */
    psiPixmap = GetPsiAttr (psi_window, "pixmap");
    if ((pixmap = GetIntAttr (psiPixmap, "id")) != NULL)
    {
	/* change the pixmap */
	XFreePixmap (display, pixmap);
	/* change the pixmap'gc too, because the gc is created on the pixmap ! */
	psiPixmapGC = GetPsiAttr (psiPixmap, "graphic_context");
	XFreeGC (display, GetIntAttr (psiPixmapGC, "id"));
	stack_add_int_attr (psiPixmap, "id", NULL);
	stack_add_int_attr (psiPixmapGC, "id", NULL);
    }

    /* init a new pixmap on the window */
    XGetWindowAttributes (display, window, &attr);
    if ((pixmap = XCreatePixmap (display, window, 
				 attr.width+1, attr.height+1,
				 attr.depth)) != NULL)
    {
	stack_add_int_attr (psiPixmap, "id", pixmap);
	gcvalues.cap_style = CapRound;
	gcvalues.join_style = JoinRound;
	pixmapGC = XCreateGC (display, pixmap, 
			      GCJoinStyle|GCCapStyle, &gcvalues);
	stack_add_psi_attr (psiPixmap, "graphic_context", 
			    NewPsi (xgc, "id", pixmapGC));
    }
}


/*****************************************************************/
/* Static */
/* free all attributes of a window, that is its display list, its gc, its pixmap ... */

static void FreeWindow (display, psi_window)

Display *display;
ptr_psi_term psi_window;

{
    ptr_psi_term psiPixmap;


    XFreeGC (display, DrawableGC (psi_window));
    x_free_display_list (WindowDisplayList (psi_window));

    psiPixmap = GetPsiAttr (psi_window, "pixmap");
    XFreeGC (display, DrawableGC (psiPixmap));
    XFreePixmap (display, GetIntAttr (psiPixmap, "id"));
}


/*****************************************************************/
/******** xcOpenConnection

  xcOpenConnection (+Name, -Connection)
 
  open a connection to the X server.

 */

int xcOpenConnection ()

{
    include_var_builtin (2);
    ptr_definition types[2];
    char *display;
    Display *connection;
    ptr_psi_term psiConnection;


    types[0] = quoted_string;
    types[1] = xdisplay;


    begin_builtin (xcOpenConnection, 2, 1, types);

    if (strcmp ((char *) val[0], ""))
        display = (char *) val[0];
    else
        display = NULL; 

    if (connection = XOpenDisplay (display))
    {
	psiConnection = NewPsi (xdisplay, "id", connection);
	push_goal (unify, psiConnection, args[1], NULL);

	success = TRUE;
    }
    else
    {
        Errorline ("couldn't open connection in %P.\n", g);
	success = FALSE;
    }

    end_builtin ();
}


/*****************************************************************/
/******** xcDefaultRootWindow

  xcDefaultRootWindow (+Display, -Root)
 
  return the root window of the given display

 */

int xcDefaultRootWindow ()

{
    include_var_builtin (2);
    ptr_definition types[2];
    Display *display;
    ptr_psi_term psiRoot;


    types[0] = real;
    types[1] = xdrawable;

    begin_builtin (xcDefaultRootWindow, 2, 1, types);

    display = (Display *) val[0];

    psiRoot = NewPsi (xwindow, "id", DefaultRootWindow (display));

    push_goal (unify, psiRoot, args[1], NULL);
    success = TRUE;

    end_builtin ();
}



/*****************************************************************/
/******** static GetConnectionAttribute */

static int GetConnectionAttribute (display, attributeId, attribute)

Display *display;
int attributeId, *attribute;

{
    switch (attributeId) 
    {
	case 0: 
	    *attribute = (int) ConnectionNumber (display);
	    break;
	case 1: 
	    *attribute = (int) display->proto_major_version; 
	    break;
	case 2: 
	    *attribute = (int) display->proto_minor_version; 
	    break;
	case 3: 
	    *attribute = (int) ServerVendor (display);
	    break;
	case 4: 
	    *attribute = (int) ImageByteOrder (display);
	    break;
	case 5: 
	    *attribute = (int) BitmapUnit (display);
	    break;
	case 6: 
	    *attribute = (int) BitmapPad (display);
	    break;
	case 7: 
	    *attribute = (int) BitmapBitOrder (display);
	    break;
	case 8: 
	    *attribute = (int) VendorRelease (display);
	    break;
	case 9: 
	    *attribute = (int) display->qlen; 
	    break;
	case 10: 
	    *attribute = (int) LastKnownRequestProcessed (display);
	    break;
	case 11: 
	    *attribute = (int) display->request;
	    break;
	case 12: 
	    *attribute = (int) DisplayString (display); 
	    break;
	case 13: 
	    *attribute = (int) DefaultScreen (display); 
	    break;
	case 14: 
	    *attribute = (int) display->min_keycode;
	    break;
	case 15: 
	    *attribute = (int) display->max_keycode;
	    break;
	default: 
	    return FALSE;
	    break;
    }

    return TRUE;
}

/*****************************************************************/
/******** xcGetConnectionAttribute

  xcGetConnectionAttribute (+Display, +AttributeId, -Value)

  returns the value corresponding to the attribute id.

 */

int xcGetConnectionAttribute ()
     
{
    include_var_builtin (3);
    ptr_definition types[3];
    int attr;


    types[0] = real;
    types[1] = real;
    types[2] = real;

    begin_builtin (xcGetConnectionAttribute, 3, 2, types);

    if (GetConnectionAttribute (val[0], val[1], &attr))
    {
	unify_real_result (args[2], (REAL) attr);
	success = TRUE;
    }
    else
    {
        Errorline ("could not get connection attribute in %P.\n", g);
	success = FALSE;
    }

    end_builtin ();
}


/*****************************************************************/
/******** GetScreenAttribute */

static int GetScreenAttribute (display, screen, attributeId, attribute)

Display *display;
int screen, attributeId, *attribute;

{
    Screen *s;


    s = ScreenOfDisplay (display, screen);
    switch (attributeId) 
    {
	case 0: 
	    *attribute = (int) DisplayOfScreen(s);
	    break;
	case 1: 
	    *attribute = (int) RootWindowOfScreen(s);
	    break;
	case 2: 
	    *attribute = (int) WidthOfScreen(s);
	    break;
	case 3: 
	    *attribute = (int) HeightOfScreen(s);
	    break;
	case 4: 
	    *attribute = (int) WidthMMOfScreen(s);
	    break;
	case 5: 
	    *attribute = (int) HeightMMOfScreen(s);
	    break;
	case 6: 
	    *attribute = (int) DefaultDepthOfScreen(s);
	    break;
	case 7: 
	    *attribute = (int) DefaultVisualOfScreen(s);
	    break;
	case 8: 
	    *attribute = (int) DefaultGCOfScreen(s);
	    break;
	case 9: 
	    *attribute = (int) DefaultColormapOfScreen(s);
	    break;
	case 10: 
	    *attribute = (int) WhitePixelOfScreen(s);
	    break;
	case 11: 
	    *attribute = (int) BlackPixelOfScreen(s);
	    break;
	case 12: 
	    *attribute = (int) MaxCmapsOfScreen(s);
	    break;
	case 13: 
	    *attribute = (int) MinCmapsOfScreen(s);
	    break;
	case 14: 
	    *attribute = (int) DoesBackingStore(s);
	    break;
	case 15: 
	    *attribute = (int) DoesSaveUnders(s);
	    break;
	case 16: 
	    *attribute = (int) EventMaskOfScreen(s);
	    break;
	default: 
	    return FALSE;
	    break;
    }

    return TRUE;
}


/*****************************************************************/
/******** xcGetScreenAttribute

  xcGetScreenAttribute (+Display, +Screen, +AttributeId, -Value)

  returns the value corresponding to the attribute id.

 */

int xcGetScreenAttribute ()
     
{
    include_var_builtin (4);
    ptr_definition types[4];
    int attr;


    types[0] = real;
    types[1] = real;
    types[2] = real;
    types[3] = real;

    begin_builtin (xcGetScreenAttribute, 4, 3, types);

    if (GetScreenAttribute (val[0], val[1], val[2], &attr))
    {
	unify_real_result (args[3], (REAL) attr);
	success = TRUE;
    }
    else
    {
        Errorline ("could not get screen attribute in %P.\n", g);
	success = FALSE;
    }

    end_builtin ();
}


/*****************************************************************/
/******** xcCloseConnection

  xcCloseConnection (+Connection)

  Close the connection.

 */

int xcCloseConnection ()
     
{
    include_var_builtin (1);
    ptr_definition types[1];


    types[0] = real;

    begin_builtin (xcCloseConnection, 1, 1, types);

    XCloseDisplay ((Display *) val[0]);
    success = TRUE;

    end_builtin ();
}



/*****************************************************************/
/******** xcCreateSimpleWindow

  xcCreateSimpleWindow (+Display, +Parent, +X, +Y, +Width, +Height,
                        +BackGroundColor, +WindowTitle, +IconTitle, 
			+Permanent, +Show, -Window)

  create a simple window.

 */

int xcCreateSimpleWindow()
     
{
    include_var_builtin (12);
    ptr_definition types[12];
    Window window;
    Pixmap life_icon;
    XSizeHints hints;
    XWindowChanges changes;
    unsigned long changesMask;
    XSetWindowAttributes attributes;
    unsigned long attributesMask;
    int j;
    int permanent, show;
    Display * display;
    GC gc;
    XGCValues gcvalues;
    ptr_psi_term psiWindow;


    for (j = 0; j < 12; j++)
        types[j] = real;
    types[7]= quoted_string;
    types[8]= quoted_string;
    types[9]= boolean;
    types[10]= boolean;

    begin_builtin (xcCreateSimpleWindow, 12, 11, types);

    permanent = val[9];
    show = val[10];

    if (window = XCreateSimpleWindow (val[0], val[1], /* display, parent */
				      val[2], val[3], /* X, Y */
				      val[4], val[5], /* Width, Height */
				      20, 1,          /* BorderWidth, BorderColor */
				      val[6]))        /* BackGround */
    {
	psiWindow = stack_psi_term (4);
	psiWindow->type = xwindow;
	stack_add_int_attr (psiWindow, "id", window);

	/* attach the icon of life */
	life_icon = XCreateBitmapFromData (val[0], window, life_icon_bits,
				      life_icon_width, life_icon_height);

	/* set properties */
	hints.x = val[2];
	hints.y = val[3];
	hints.width =val[4] ;
	hints.height = val[5];
	hints.flags = PPosition | PSize;
	XSetStandardProperties (val[0], window, 
				val[7], val[8], 
				life_icon, arg_v, arg_c,
				&hints);	

	changes.x = val[2];
	changes.y = val[3];
	changes.width =val[4] ;
	changes.height = val[5];
	changesMask = CWX | CWY | CWWidth | CWHeight;
	display = (Display *) val[0];
	XReconfigureWMWindow (val[0], window, DefaultScreen (display),
			      changesMask, &changes);

	/* set the background color */
	XSetWindowBackground ((Display *) val[0], window, val[6]);

	/* set the geometry before to show the window */
	XMoveResizeWindow ((Display *) val[0], window,
			   val[2], val[3], val[4], val[5]);

	/* set the back pixel in order to have the color when deiconife */
	attributes.background_pixel = val[6];
	attributes.backing_pixel = val[6];
	attributesMask = CWBackingPixel|CWBackPixel;
        XChangeWindowAttributes ((Display *) val[0], window, 
				 attributesMask, &attributes);

	if (!permanent)
	{
	    push_window (destroy_window, (Display *) val[0], window);
	    x_window_creation = TRUE;
	}
	else
	if (show)
	    push_window (show_window, (Display *) val[0], window);

	if (show)
	    x_show_window ((Display *) val[0], window);

	/* create a GC on the window for the next outputs */
	gcvalues.cap_style = CapRound;
	gcvalues.join_style = JoinRound;
	gc = XCreateGC (val[0], window, GCJoinStyle|GCCapStyle, &gcvalues);
	stack_add_psi_attr (psiWindow, "graphic_context", 
			    NewPsi (xgc, "id", gc));

	/* init a display list on the window for the refresh window */
	stack_add_psi_attr (psiWindow, "display_list", 
			    NewPsi (xdisplaylist, "id", x_display_list ()));

	/* init a pixmap on the window for the refresh mechanism */
	stack_add_psi_attr (psiWindow, "pixmap", 
			    NewPsi (xpixmap, "id", NULL));
	ResizePixmap (psiWindow, val[0], window, val[4], val[5]);

	push_goal (unify, psiWindow, args[11], NULL);
	success = TRUE;
    }
    else
    {
        Errorline ("could not create a simple window in %P.\n", g);
	success = FALSE;
    }

    end_builtin ();
}


/*****************************************************************/
#if 0

xcCreateWindow is not used anymore since we use xcCreateSimpleWindow.
I just keep this code in case - jch - Thu Aug  6 16:11:23 MET DST 1992

/******** xcCreateWindow

  xcCreateWindow (+Connection, +Parent, +X, +Y, +Width, +Height,
                  +BorderWidth, +Depth, +Class, +Visual, 
		  +Permanent, +Show, -Window)

  create a window on the display Connection.

 */

int xcCreateWindow()
     
{
    include_var_builtin (13);
    ptr_definition types[13];
    Window window;
    XWindowChanges changes;
    unsigned long changesMask;
    XSizeHints hints;
    int j, permanent, show;
    GC gc;
    XGCValues gcvalues;


    for (j = 0; j < 13; j++)
        types[j] = real;

    begin_builtin (xcCreateWindow, 13, 12, types);

    permanent = val[10];
    show = val[11];

    if (window = XCreateWindow (val[0], val[1], /* display, parent */
				val[2], val[3], /* X, Y */
				val[4], val[5], /* Width, Height */
				val[6], val[7], /* BorderWidth, Depth */
				val[8], val[9], /* Class, Visual */
                                0, (XSetWindowAttributes *) NULL))
    {
	unify_real_result (args[12], (REAL) window);

	changes.x = val[2];
	changes.y = val[3];
	changes.width =val[4] ;
	changes.height = val[5];
	changesMask = CWX | CWY | CWWidth | CWHeight;
	XConfigureWindow (val[0], window, changesMask, &changes);

	hints.x = val[2];
	hints.y = val[3];
	hints.width =val[4] ;
	hints.height = val[5];
	hints.flags = PPosition | PSize;
	XSetNormalHints (val[0], window, &hints);

	if (!permanent)
	{
	    push_window (destroy_window, val[0], window);
	    x_window_creation = TRUE;
	}
	else
	if (show)
	    push_window (show_window, val[0], window);

	if (show)
	    x_show_window (val[0], window);

	/* create a GC on the window for the next outputs */
	gcvalues.cap_style = CapRound;
	gcvalues.join_style = JoinRound;
	gc = XCreateGC (val[0], window, GCJoinStyle|GCCapStyle, &gcvalues);
	stack_add_int_attr (args[12], "gc", gc);

	/* init a display list on the window for the refresh window */
	stack_add_int_attr (args[12], "display_list", NULL);

	success = TRUE;
    }
    else
    {
        Errorline ("could not create window in %P.\n", g);
	success = FALSE;
    }

    end_builtin ();
}

#endif


/*****************************************************************/
/******** xcSetStandardProperties

  xcSetStandardProperties (+Display, +Window, +WindowTitle, +IconTitle, 
                           +X, +Y, +Width, +Height)

*/

int xcSetStandardProperties ()
{
    include_var_builtin (8);
    ptr_definition types[8];
    int j;
    XSizeHints hints;


    for (j=0; j<8; j++)
        types[j] = real;
    types[1] = xwindow;
    types[2] = quoted_string;
    types[3] = quoted_string;

    begin_builtin (xcSetStandardProperties, 8, 8, types);

    hints.x = val[4];
    hints.y = val[5];
    hints.width = val[6] ;
    hints.height = val[7];
    hints.flags = PPosition | PSize; 

    XSetStandardProperties(val[0], val[1],
			   val[2], val[3],     /* window title, icon title */
			   None,               /* icon pixmap */
			   (char **) NULL, 0,  /* argv, argc */
			   &hints); 

    ResizePixmap (args[1], val[0], val[1], val[6], val[7]);

    success = TRUE;

    end_builtin ();

}



/*****************************************************************/
/******** xcGetWindowGeometry

  xcGetWindowGeometry (+Display, +Window, -X, -Y, -Width, -Height)

  returns the geometry of the window.

 */

int xcGetWindowGeometry ()
     
{
    include_var_builtin (6);
    ptr_definition types[6];
    int j, x, y;
    unsigned int w, h, bw, d;
    Window r;


    for (j=0; j<6; j++)
        types[j] = real;
    types[1] = xdrawable;

    begin_builtin (xcGetWindowGeometry, 6, 2, types);

    if (XGetGeometry ((Display *) val[0], (Drawable) val[1], 
		      &r, &x, &y, &w, &h, &bw, &d))
    {
	unify_real_result (args[2], (REAL) x);
	unify_real_result (args[3], (REAL) y);
	unify_real_result (args[4], (REAL) w);
	unify_real_result (args[5], (REAL) h);
	success = TRUE;
    }
    else
    {
	Errorline ("could not get the geometry in %P.\n", g);
	success = FALSE;
    }

    end_builtin ();
}


/*****************************************************************/
/******** GetWindowAttribute */

static int GetWindowAttribute (display, window, attributeId, attribute)

int display, window, attributeId, *attribute;

{
    XWindowAttributes windowAttributes;


    XGetWindowAttributes (display, window, &windowAttributes);
    switch (attributeId) 
    {
	case 0: 
	    *attribute = windowAttributes.x;	
	    break;
	case 1: 
	    *attribute = windowAttributes.y;
	    break;
	case 2: 
	    *attribute = windowAttributes.width;
	    break;
	case 3: 
	    *attribute = windowAttributes.height;
	    break;
	case 4: 
	    *attribute = windowAttributes.border_width;
	    break;
	case 5: 
	    *attribute = windowAttributes.depth;
	    break;
	case 6: 
	    *attribute = windowAttributes.root;
	    break;
	case 7: 
	    *attribute = (int)windowAttributes.screen;
	    break;
	case 8: 
	    *attribute = (int)windowAttributes.visual;
	    break;
	case 9: 
	    *attribute = windowAttributes.class;
	    break;
	case 10: 
	    *attribute = windowAttributes.all_event_masks;
	    break;
	case 11: 
	    *attribute = windowAttributes.bit_gravity;
	    break;
	case 12: 
	    *attribute = windowAttributes.win_gravity;
	    break;
	case 13: 
	    *attribute = windowAttributes.backing_store;
	    break;
	case 14: 
	    *attribute = windowAttributes.backing_planes;
	    break;
	case 15: 
	    *attribute = windowAttributes.backing_pixel;
	    break;
	case 16: 
	    *attribute = windowAttributes.override_redirect;
	    break;
	case 17: 
	    *attribute = windowAttributes.save_under;
	    break;
	case 18: 
	    *attribute = windowAttributes.your_event_mask;
	    break;
	case 19: 
	    *attribute = windowAttributes.do_not_propagate_mask;
	    break;
	case 20: 
	    *attribute = windowAttributes.colormap;
	    break;
	case 21: 
	    *attribute = windowAttributes.map_installed;
	    break;
	case 22: 
	    *attribute = windowAttributes.map_state;
	    break;
	default: 
	    return FALSE;
	    break;
    }
    return TRUE;
}


/*****************************************************************/
/******** xcGetWindowAttribute

  xcGetWindowAttribute (+Display, +Window, +AttributeId, -Value)

  returns the value corresponding to the attribute id of the window.

 */

int xcGetWindowAttribute()
     
{
    include_var_builtin (4);
    ptr_definition types[4];
    int attr;


    types[0] = real;
    types[1] = xwindow;
    types[2] = real;
    types[3] = real;

    begin_builtin (xcGetWindowAttribute, 4, 3, types);

    if (GetWindowAttribute (val[0], val[1], val[2], &attr))
    {
	unify_real_result (args[3], (REAL) attr);
	success = TRUE;
    }
    else
    {
	Errorline ("could not get a window attribute in %P.\n", g);
	success = FALSE;
    }

    end_builtin ();
}


/*****************************************************************/
/******** xcSetWindowGeometry

  xcSetWindowGeometry (+Display, +Window, +X, +Y, +Width, +Height)

  set the geometry of the window.

 */

int xcSetWindowGeometry ()
     
{
    include_var_builtin (6);
    ptr_definition types[6];
    int j;


    for (j=0; j<6; j++)
        types[j] = real;
    types[1] = xdrawable;

    begin_builtin (xcSetWindowGeometry, 6, 6, types);

    XMoveResizeWindow ((Display *) val[0], (Drawable) val[1], 
		       val[2], val[3], val[4], val[5]);

    /* modify the pixmap */
    ResizePixmap (args[1], val[0], val[1], val[4], val[5]);

    success = TRUE;

    end_builtin ();
}



/*****************************************************************/
/******** SetWindowAttribute */

static int SetWindowAttribute (psi_window, display, window, attributeId, attribute)

ptr_psi_term psi_window;
Display *display;
Drawable window;
unsigned long attributeId, attribute;

{
    XSetWindowAttributes attributes;
    XWindowChanges changes;
    unsigned long attributesMask = 0;
    unsigned long changesMask = 0;
    int backgroundChange = FALSE;
    int sizeChange = FALSE;
    unsigned int width, height;
    int x, y, bw, d;
    Window r;

    switch (attributeId) 
    {
	case 0: 
	    changes.x = attribute;
	    changesMask |= CWX;
	    break;
	case 1:
	    changes.y = attribute;
	    changesMask |= CWY;
	    break;
	case 2:
	    changes.width = attribute;
	    changesMask |= CWWidth;
	    XGetGeometry (display, window, &r, &x, &y, &width, &height, &bw, &d);
	    width = attribute;
	    sizeChange = TRUE;
	    break;
	case 3:
	    changes.height = attribute;
	    changesMask |= CWHeight;
	    XGetGeometry (display, window, &r, &x, &y, &width, &height, &bw, &d);
	    height = attribute;
	    sizeChange = TRUE;
	    break;
	case 4:
	    changes.border_width = attribute;
	    changesMask |= CWBorderWidth;
	    break;
	case 11:
	    attributes.bit_gravity = attribute;
	    attributesMask |= CWBitGravity;
	    break;
	case 12:
	    attributes.win_gravity = attribute;
	    attributesMask |= CWWinGravity;
	    break;
	case 13:
	    attributes.backing_store = attribute;
	    attributesMask |= CWBackingStore;
	    break;
	case 14:
	    attributes.backing_planes = attribute;
	    attributesMask |= CWBackingPlanes;
	    break;
	case 15:
	    attributes.backing_pixel = attribute;
	    attributesMask |= CWBackingPixel;
	    break;
	case 16:
	    attributes.override_redirect = attribute;
	    attributesMask |= CWOverrideRedirect;
	    break;
	case 17:
	    attributes.save_under = attribute;
	    attributesMask |= CWSaveUnder;
	    break;
	case 18:
	    attributes.event_mask = attribute;
	    attributesMask |= CWEventMask;
	    break;
	case 19:
	    attributes.do_not_propagate_mask = attribute;
	    attributesMask |= CWDontPropagate;
	    break;
	case 20:
	    attributes.colormap = attribute;
	    attributesMask |= CWColormap;
	    break;
	case 23:
	    changes.sibling = attribute;
	    changesMask |= CWSibling;
	    break;
	case 24:
	    changes.stack_mode = attribute;
	    changesMask |= CWStackMode;
	    break;
	case 25:
	    attributes.background_pixmap = attribute;
	    attributesMask |= CWBackPixmap;
	    break;
	case 26:
	    attributes.background_pixel = attribute;
	    attributesMask |= CWBackPixel;
	    backgroundChange = TRUE;

	    /* change the backing_pixel in order to fill the pixmap with */
	    attributes.backing_pixel = attribute;
	    attributesMask |= CWBackingPixel;
	    break;
	case 27:
	    attributes.border_pixmap = attribute;
	    attributesMask |= CWBorderPixmap;
	    break;
	case 28:
	    attributes.border_pixel = attribute;
	    attributesMask |= CWBorderPixel;
	    break;
	case 29:
	    attributes.cursor = attribute;
	    attributesMask |= CWCursor;
	    break;
    	default: 
	    return FALSE;
	    break;
    }

    if (changesMask)
        XConfigureWindow (display, window, changesMask, &changes);

    if (attributesMask)
        XChangeWindowAttributes (display, window, attributesMask, &attributes);

    if (backgroundChange)
        XClearArea (display, window, 0, 0, 0, 0, True);

    if (sizeChange)
        ResizePixmap (psi_window, display, window, width, height);

    return TRUE;
}


/*****************************************************************/
/******** xcSetWindowAttribute

  xcSetWindowAttribute (+Display, +Window, +AttributeId, +Value)

  set the value corresponding to the attribute id.

 */

int xcSetWindowAttribute ()
     
{
    include_var_builtin (4);
    ptr_definition types[4];


    types[0] = real;
    types[1] = xwindow;
    types[2] = real;
    types[3] = real;

    begin_builtin (xcSetWindowAttribute, 4, 4, types);

    if (SetWindowAttribute (args[1], val[0], val[1], val[2], val[3]))
    {
	XSync (val[0], 0);
        success = TRUE;
    }
    else
    {
	Errorline ("could not set window attribute in %P.\n", g);
	success = FALSE;
    }

    end_builtin ();
}



/*****************************************************************/
/******** xcMapWindow

  xcMapWindow (+Connection, +Window)

  map the Window on the display Connection.

 */

int xcMapWindow()
     
{
    include_var_builtin (2);
    ptr_definition types[2];


    types[0] = real;
    types[1] = real;

    begin_builtin (xcMapWindow, 2, 2, types);

    XMapWindow (val[0], val[1]);
    XSync (val[0], 0);

    push_window (hide_window, val[0], val[1]);
    success = TRUE;

    end_builtin ();
}



/*****************************************************************/
/******** xcUnmapWindow

  xcUnmapWindow (+Connection, +Window)

  unmap the Window on the display Connection.

 */

int xcUnmapWindow()
     
{
    include_var_builtin (2);
    ptr_definition types[2];


    types[0] = real;
    types[1] = real;

    begin_builtin (xcUnmapWindow, 2, 2, types);

    XUnmapWindow (val[0], val[1]);
    XSync (val[0], 0);

    push_window (show_window, val[0], val[1]);
    success = TRUE;

    end_builtin ();
}



/*****************************************************************/
/******** xcSelectInput

  xcSelectInput (+Connection, +Window, +Mask)

  select the desired event types

 */

int xcSelectInput()
     
{
    include_var_builtin (3);
    ptr_definition types[3];


    types[0] = real;
    types[1] = real;
    types[2] = real;

    begin_builtin (xcSelectInput, 3, 3, types);

    XSelectInput (val[0], val[1], val[2]);
    success = TRUE;

    end_builtin ();
}



/*****************************************************************/
/******** xcRefreshWindow

  
  xcRefreshWindow (+Connection, +Window)

  refresh the window

  */

int xcRefreshWindow()
     
{
    include_var_builtin (2);
    ptr_definition types[2];
    Pixmap pixmap;
    ptr_psi_term psiPixmap;


    types[0] = real;
    types[1] = xwindow;

    begin_builtin (xcRefreshWindow, 2, 2, types);

    psiPixmap = GetPsiAttr (args[1], "pixmap");
    if ((pixmap = (Pixmap) GetIntAttr (psiPixmap, "id")) != NULL)
        x_refresh_window (val[0], val[1], pixmap,
			  DrawableGC (psiPixmap), 
			  WindowDisplayList (args[1]));
    else
        x_refresh_window (val[0], val[1], val[1],
			  DrawableGC (args[1]), 
			  WindowDisplayList (args[1]));

    success = TRUE;

    end_builtin ();
}



/*****************************************************************/
/******** xcPostScriptWindow

  
  xcPostScriptWindow (+Display, +Window, Filename)

  output the contents of the window in Filename

  */

int xcPostScriptWindow ()
     
{
    include_var_builtin (3);
    ptr_definition types[3];


    types[0] = real;
    types[1] = xwindow;
    types[2] = quoted_string;

    begin_builtin (xcPostScriptWindow, 3, 3, types);

    success = x_postscript_window (val[0], val[1],
				   GetIntAttr (GetPsiAttr (args[1], "display_list"), 
					       "id"),
				   val[2]);

    end_builtin ();
}



/*****************************************************************/
/******** xcDestroyWindow

  
  xcDestroyWindow (+Connection, +Window)

  Close and destroy the window (unbacktrable).

  */

int xcDestroyWindow()
     
{
    include_var_builtin (2);
    ptr_definition types[2];
    ptr_psi_term psi;

    types[0] = real;
    types[1] = xwindow;

    begin_builtin (xcDestroyWindow, 2, 2, types);

    psi = GetPsiAttr (args[1], "permanent");
    if (!strcmp (psi->type->symbol, "true"))
    {
        Errorline ("cannot destroy a permanent window.\n");
	exit_life (TRUE); /* was: main_loop_ok=FALSE; - jch */
	success = FALSE;
    }
    else
    {
        FreeWindow (val[0], args[1]);
	XDestroyWindow (val[0], val[1]);
	XSync (val[0], 0);
	clean_undo_window (val[0], val[1]);
	success = TRUE;
    }

    end_builtin ();
}



/*****************************************************************/
/******** CREATEGC

  xcCreateGC (+Connection, +Drawable, -GC)

  create a graphic context.

 */

int xcCreateGC ()
     
{
    include_var_builtin (3);
    ptr_definition types[3];
    GC gc;
    XGCValues GCvalues;


    types[0] = real;
    types[1] = xdrawable;
    types[2] = real;

    begin_builtin (xcCreateGC, 3, 2, types);

    if (gc = XCreateGC (val[0], val[1], 0, GCvalues))
    {
	unify_real_result (args[2], (REAL) (int) gc);
	success = TRUE;
    }
    else
    {
	Errorline ("could not create gc in %P.\n", g);
	success = FALSE;
    }

    end_builtin ();
}



/*****************************************************************/
/******** GETGCATTRIBUTE */

static int GetGCAttribute (gc, attributeId, attribute)

GC gc;
int attributeId, *attribute;

{
    switch (attributeId) 
    {
	case 0:
	    *attribute = gc->values.function;
	    break;
	case 1:
	    *attribute = gc->values.plane_mask;
	    break;
	case 2:
	    *attribute = gc->values.foreground;
	    break;
	case 3:
	    *attribute = gc->values.background;
	    break;
	case 4:
	    *attribute = gc->values.line_width;
	    break;
	case 5:
	    *attribute = gc->values.line_style;
	    break;
	case 6:
	    *attribute = gc->values.cap_style;
	    break;
	case 7:
	    *attribute = gc->values.join_style;
	    break;
	case 8:
	    *attribute = gc->values.fill_style;
	    break;
	case 9:
	    *attribute = gc->values.fill_rule;
	    break;
	case 10:
	    *attribute = gc->values.tile;
	    break;
	case 11:
	    *attribute = gc->values.stipple;
	    break;
	case 12:
	    *attribute = gc->values.ts_x_origin;
	    break;
	case 13:
	    *attribute = gc->values.ts_y_origin;
	    break;
	case 14:
	    *attribute = gc->values.font;
	    break;
	case 15:
	    *attribute = gc->values.subwindow_mode;
	    break;
	case 16:
	    *attribute = gc->values.graphics_exposures;
	    break;
	case 17:
	    *attribute = gc->values.clip_x_origin;
	    break;
	case 18:
	    *attribute = gc->values.clip_y_origin;
	    break;
	case 19:
	    *attribute = gc->values.clip_mask;
	    break;
	case 20:
	    *attribute = gc->values.dash_offset;
	    break;
	case 21: 
	    *attribute = (unsigned char)(gc->values.dashes);
	    break;
	case 22:
	    *attribute = gc->values.arc_mode;
	    break;
	case 23:
	    *attribute = gc->rects;
	    break;
	case 24:
	    *attribute = gc->dashes;
	    break;
	default: 
	    return FALSE;
	    break;
    }
    return TRUE;
}


/*****************************************************************/
/******** GETGCATTRIBUTE

  xcGetGCAttribute (+GC, +AttributeId, -Val)

  get the value of the attribute id of GC.

 */

int xcGetGCAttribute ()
     
{
    include_var_builtin (3);
    ptr_definition types[3];
    int attr;


    types[0] = real;
    types[1] = real;
    types[2] = real;

    begin_builtin (xcGetGCAttribute, 3, 2, types);

    if (GetGCAttribute (val[0], val[1], &attr))
    {
	unify_real_result (args[2], (REAL) attr);
	success = TRUE;
    }
    else
    {
	Errorline ("could not get gc attribute in %P.\n", g);
	success = FALSE;
    }

    end_builtin ();
}



/*****************************************************************/
/******** SETGCATTRIBUTE */

static int SetGCAttribute (display, gc, attributeId, attribute)

Display *display;
GC gc;
int attributeId, attribute;

{
    XGCValues attributes;
    unsigned long attributesMask = 0;


    switch (attributeId) 
    {
	case 0:
	    attributes.function = attribute;
	    attributesMask |= GCFunction;
	    break;
	case 1:
	    attributes.plane_mask = attribute;
	    attributesMask |= GCPlaneMask;
	    break;
	case 2:
	    attributes.foreground = attribute;
	    attributesMask |= GCForeground;
	    break;
	case 3:
	    attributes.background = attribute;
	    attributesMask |= GCBackground;
	    break;
	case 4:
	    attributes.line_width = attribute;
	    attributesMask |= GCLineWidth;
	    break;
	case 5:
	    attributes.line_style = attribute;
	    attributesMask |= GCLineStyle;
	    break;
	case 6:
	    attributes.cap_style = attribute;
	    attributesMask |= GCCapStyle;
	    break;
	case 7:
	    attributes.join_style = attribute;
	    attributesMask |= GCJoinStyle;
	    break;
	case 8:
	    attributes.fill_style = attribute;
	    attributesMask |= GCFillStyle;
	    break;
	case 9:
	    attributes.fill_rule = attribute;
	    attributesMask |= GCFillRule;
	    break;
	case 10:
	    attributes.tile = attribute;
	    attributesMask |= GCTile;
	    break;
	case 11:
	    attributes.stipple = attribute;
	    attributesMask |= GCStipple;
	    break;
	case 12:
	    attributes.ts_x_origin = attribute;
	    attributesMask |= GCTileStipXOrigin;
	    break;
	case 13:
	    attributes.ts_y_origin = attribute;
	    attributesMask |= GCTileStipYOrigin;
	    break;
	case 14:
	    attributes.font = attribute;
	    attributesMask |= GCFont;
	    break;
	case 15:
	    attributes.subwindow_mode = attribute;
	    attributesMask |= GCSubwindowMode;
	    break;
	case 16:
	    attributes.graphics_exposures = attribute;
	    attributesMask |= GCGraphicsExposures;
	    break;
	case 17:
	    attributes.clip_x_origin = attribute;
	    attributesMask |= GCClipXOrigin;
	    break;
	case 18:
	    attributes.clip_y_origin = attribute;
	    attributesMask |= GCClipYOrigin;
	    break;
	case 19:
	    attributes.clip_mask = attribute;
	    attributesMask |= GCClipMask;
	    break;
	case 20:
	    attributes.dash_offset = attribute;
	    attributesMask |= GCDashOffset;
	    break;
	case 21: 
	    attributes.dashes = (char)(0xFF & attribute);
	    attributesMask |= GCDashList;
	    break;
	case 22:
	    attributes.arc_mode = attribute;
	    attributesMask |= GCArcMode;
	    break;
    	default: 
	    return FALSE;
	    break;
    }

    XChangeGC (display, gc, attributesMask, &attributes);
    return TRUE;
}


/*****************************************************************/
/******** SETGCATTRIBUTE

  xcSetGCAttribute (+Display, +GC, +AttributeId, +Val)

  set the value of the attribute id of GC.

 */

int xcSetGCAttribute ()
     
{
    include_var_builtin (4);
    ptr_definition types[4];


    types[0] = real;
    types[1] = real;
    types[2] = real;
    types[3] = real;

    begin_builtin (xcSetGCAttribute, 4, 4, types);

    if (SetGCAttribute (val[0], val[1], val[2], val[3]))
        success = TRUE;
    else
    {
	Errorline ("could not set gc attribute in %P.\n", g);
	success = FALSE;
    }

    end_builtin ();
}



/*****************************************************************/
/******** DESTROYGC

  xcDestroyGC (+Connection, +GC)

  destroys a graphic context.

 */

int xcDestroyGC ()
     
{
    include_var_builtin (2);
    ptr_definition types[2];


    types[0] = real;
    types[1] = real;

    begin_builtin (xcDestroyGC, 2, 2, types);

    XFreeGC (val[0], val[1]);
    success = TRUE;

    end_builtin ();
}

/*****************************************************************/
/******** REQUESTCOLOR

  xcRequestColor (+Connection, +ColorMap, +Red, +Green, +Blue, -Pixel)

  get the closest color to (Red,Green,Blue) in the ColorMap

 */

int xcRequestColor ()
     
{
    include_var_builtin (6);
    ptr_definition types[6];
    int j;
    XColor color;


    for (j=0; j<6; j++)
        types[j] = real;

    begin_builtin (xcRequestColor, 6, 5, types);

    color.red = (val[2]) << 8;
    color.green = (val[3]) << 8;
    color.blue = (val[4]) << 8;
    color.flags = DoRed|DoGreen|DoBlue;

    if (XAllocColor (val[0], val[1], &color))
    {
	unify_real_result (args[5], (REAL) color.pixel);
	success = TRUE;
    }
    else
    {
	Errorline ("could not request a color in %P.\n", g);
	success = FALSE;
    }

    end_builtin ();
}


/*****************************************************************/
/******** REQUESTNAMEDCOLOR

  xcRequestNamedColor (+Connection, +ColorMap, +Name, -Pixel)

  get the color corresponding to Name in the ColorMap

 */

int xcRequestNamedColor ()
     
{
    include_var_builtin (4);
    ptr_definition types[4];
    int j;
    XColor cell, rgb;

    types[0] = real;
    types[1] = real;
    types[2] = quoted_string;
    types[3] = real; /* 18.12 */

    begin_builtin (xcRequestNamedColor, 4, 3, types);

    if (XAllocNamedColor (val[0], val[1], val[2], &cell, &rgb))
    {
	unify_real_result (args[3], (REAL) cell.pixel);
	success = TRUE;
    }
    else
    {
	Errorline ("could not request a named color in %P.\n", g);
	success = FALSE;
    }

    end_builtin ();
}


/*****************************************************************/
/******** FREECOLOR

  xcFreeColor (+Connection, +ColorMap, +Pixel)

  free the color in the colormap

 */

int xcFreeColor ()
     
{
    include_var_builtin (3);
    ptr_definition types[3];
    int j;
    unsigned long pixel;


    for (j=0; j<3; j++)
        types[j] = real;

    begin_builtin (xcFreeColor, 3, 3, types);

    pixel = val[2];
    XFreeColors (val[0], val[1], &pixel, 1, 0);
    success = TRUE;

    end_builtin ();
}


/*****************************************************************/
/******** DrawLine
  
  xcDrawLine (+Connection, +Drawable, +X0, +Y0, +X1, +Y1,
              +Function, +Color, +LineWidth)

  draw a line (X0,Y0) -> (X1,Y1)
  
 */

int xcDrawLine()
     
{
    include_var_builtin (9);
    ptr_definition types[9];
    int j;
    GC gc;


    for (j = 0; j < 9; j++)
        types[j] = real;
    types[1] = xdrawable;

    begin_builtin (xcDrawLine, 9, 9, types);

    gc = DrawableGC (args[1]);
    x_set_gc (val[0], gc, val[6], val[7], val[8], xDefaultFont);

    XDrawLine ((Display *) val[0], (Window) val[1], gc, /* Display, Window, GC */
	       val[2], val[3], val[4], val[5]);         /* X0, Y0, X1, Y1 */

    x_record_line (WindowDisplayList (args[1]), DRAW_LINE, 
		   val[2], val[3], val[4], val[5],
		   val[6], val[7], val[8]);

    XSync (val[0], 0);
    success = TRUE;

    end_builtin ();
}

/*****************************************************************/
/******** DrawArc

  xcDrawArc (+Connection, +Drawable, +X, +Y, +Width, +Height, +StartAngle, +ArcAngle,
             +Function, +Color, +LineWidth)

  draw arc (see X Vol.2 page 135 for the meanings of the arguments).

 */

int xcDrawArc()
     
{
    include_var_builtin (11);
    ptr_definition types[11];
    int j;
    GC gc;


    for (j = 0; j < 11; j++)
        types[j] = real;
    types[1] = xdrawable;

    begin_builtin (xcDrawArc, 11, 11, types);

    gc = DrawableGC (args[1]);
    x_set_gc (val[0], gc, val[8], val[9], val[10], xDefaultFont);

    XDrawArc ((Display *) val[0], (Window) val[1], gc, /* Display, Window, GC */
	      val[2], val[3], val[4], val[5],          /* X, Y, Width, Height */
	      val[6], val[7]);                         /* StartAngle, ArcAngle */

    x_record_arc (WindowDisplayList (args[1]), DRAW_ARC,
		  val[2], val[3], val[4], val[5],
		  val[6], val[7], val[8], val[9], val[10]);

    XSync (val[0], 0);
    success = TRUE;

    end_builtin ();
}


/*****************************************************************/
/******** DrawRectangle

  xcDrawRectangle (+Connection, +Drawable, +X, +Y, +Width, +Height,
                   +Function, +Color, +LineWidth)

  draw a rectangle.

 */

int xcDrawRectangle()
     
{
    include_var_builtin (9);
    ptr_definition types[9];
    int j;
    GC gc;


    for (j = 0; j < 9; j++)
        types[j] = real;
    types[1] = xdrawable;

    begin_builtin (xcDrawRectangle, 9, 9, types);

    gc = DrawableGC (args[1]);
    x_set_gc (val[0], gc, val[6], val[7], val[8], xDefaultFont);

    XDrawRectangle ((Display *) val[0], (Window) val[1], gc, /* Display, Window, GC */
		    val[2], val[3], val[4], val[5]);         /* X, Y, Width, Height */

    x_record_rectangle (WindowDisplayList (args[1]), DRAW_RECTANGLE,
		        val[2], val[3], val[4], val[5],
			val[6], val[7], val[8]);

    XSync (val[0], 0);
    success = TRUE;

    end_builtin ();
}


/*****************************************************************/
/******** FillRectangle

  xcFillRectangle (+Connection, +Drawable, +X, +Y, +Width, +Height,
                   +Function, +Color)

  fill a rectangle.

 */

int xcFillRectangle()
     
{
    include_var_builtin (8);
    ptr_definition types[8];
    int j;
    GC gc;


    for (j = 0; j < 8; j++)
        types[j] = real;
    types[1] = xdrawable;

    begin_builtin (xcFillRectangle, 8, 8, types);

    gc = DrawableGC (args[1]);
    x_set_gc (val[0], gc, val[6], val[7], xDefaultLineWidth, xDefaultFont); 

    XFillRectangle ((Display *) val[0], (Window) val[1], gc, /* Display, Window, GC */
		    val[2], val[3], val[4], val[5]);         /* X, Y, Width, Height */

    x_record_rectangle (WindowDisplayList (args[1]), FILL_RECTANGLE,
		        val[2], val[3], val[4], val[5],
			val[6], val[7], 
			xDefaultLineWidth);

    XSync (val[0], 0);
    success = TRUE;

    end_builtin ();
}


/*****************************************************************/
/******** FillArc

  xcFillArc (+Connection, +Drawable, +X, +Y, +Width, +Height, +StartAngle, +ArcAngle,
             +Function, +Color)
  fill an arc.

 */

int xcFillArc()
     
{
    include_var_builtin (10);
    ptr_definition types[10];
    int j;
    GC gc;


    for (j = 0; j < 10; j++)
        types[j] = real;
    types[1] = xdrawable;

    begin_builtin (xcFillArc, 10, 10, types);

    gc = DrawableGC (args[1]);
    x_set_gc (val[0], gc, val[8], val[9], xDefaultLineWidth, xDefaultFont);

    XFillArc ((Display *) val[0], (Window) val[1], gc, /* Display, Window, GC */
	      val[2], val[3], val[4], val[5],          /* X, Y, Width, Height */
	      val[6], val[7]);                         /* StartAngle, ArcAngle */

    x_record_arc (WindowDisplayList (args[1]), FILL_ARC,
		  val[2], val[3], val[4], val[5],
		  val[6], val[7], val[8], val[9], 
		  xDefaultLineWidth);

    XSync (val[0], 0);
    success = TRUE;

    end_builtin ();
}


/*****************************************************************/
/******** PointsAlloc

  xcPointsAlloc (+NbPoints, -Points)

  allocate n points
*/
 
int xcPointsAlloc ()

{
    include_var_builtin (2);
    ptr_definition types[2];
    long Points;


    types[0] = real;
    types[1] = real;

    begin_builtin (xcPointsAlloc, 2, 1, types);
    Points = (long) malloc ((val [0]) * 2 * sizeof(short));
    unify_real_result (args[1], (REAL) Points);

    success = TRUE;

    end_builtin ();
}


/*****************************************************************/
/******** CoordPut

  xcCoordPut (+Points, +N, +Coord)

  put nth coordinate in Points
*/
 
int xcCoordPut ()

{
    include_var_builtin (3);
    ptr_definition types[3];
    short *Points;

    types[0] = real;
    types[1] = real;
    types[2] = real;

    begin_builtin (xcCoordPut, 3, 3, types);
    
    Points = (short *) val [0];
    Points += val[1];
    *Points = val[2];

    success = TRUE;

    end_builtin ();
}


/*****************************************************************/
/******** PointsFree

  xcPointsFree (+Points)

  free points
*/
 
int xcPointsFree ()

{
    include_var_builtin (1);
    ptr_definition types[1];


    types[0] = real;

    begin_builtin (xcPointsFree, 1, 1, types);
    free (val [0]);
    success = TRUE;

    end_builtin ();
}


/*****************************************************************/
/******** DrawPolygon

  xcDrawPolygon (+Connection, +Drawable, +Points, +NbPoints, 
                 +Function, +Color, +LineWidth)

  draw a polygon.

 */

int xcDrawPolygon()
     
{
    include_var_builtin (7);
    ptr_definition types[7];
    int j;
    GC gc;


    for (j = 0; j < 7; j++)
        types[j] = real;
    types[1] = xdrawable;

    begin_builtin (xcDrawPolygon, 7, 7, types);

    gc = DrawableGC (args[1]);
    x_set_gc (val[0], gc, val[4], val[5], val[6], xDefaultFont); 

    XDrawLines   ((Display *) val[0], (Window) val[1], gc, /* Display, Window, GC */
		  val[2], val[3], CoordModeOrigin);        /* Points, NbPoints, mode */

    x_record_polygon (WindowDisplayList (args[1]), DRAW_POLYGON,
		      val[2], val[3], val[4], val[5], val[6]);

    XSync (val[0], 0);
    success = TRUE;

    end_builtin ();
}


/*****************************************************************/
/******** FillPolygon

  xcFillPolygon (+Connection, +Drawable, +Points, +NbPoints, +Function, +Color)

  fill a polygon.

 */

int xcFillPolygon()
     
{
    include_var_builtin (6);
    ptr_definition types[6];
    int j;
    GC gc;


    for (j = 0; j < 6; j++)
        types[j] = real;
    types[1] = xdrawable;

    begin_builtin (xcFillPolygon, 6, 6, types);

    gc = DrawableGC (args[1]);
    x_set_gc (val[0], gc, val[4], val[5], xDefaultLineWidth, xDefaultFont); 

    XFillPolygon ((Display *) val[0], (Window) val[1], gc, /* Display, Window, GC */
		  val[2], val[3],                          /* Points, NbPoints */
		  Complex, CoordModeOrigin);               /* shape, mode */

    x_record_polygon (WindowDisplayList (args[1]), FILL_POLYGON,
		      val[2], val[3], val[4], val[5],
		      xDefaultLineWidth);

    XSync (val[0], 0);
    success = TRUE;

    end_builtin ();
}


/*****************************************************************/
/******** LoadFont

  xcLoadFont (+Connection, +Name, -Font)

  load a font.

 */

int xcLoadFont()
     
{
    include_var_builtin (3);
    ptr_definition types[3];
    Font font;


    types[0] = real;
    types[1] = quoted_string;
    types[2] = real;

    begin_builtin (xcLoadFont, 3, 2, types);

    if (font = XLoadFont (val[0], val[1]))
    {
	unify_real_result (args[2], (REAL) font);
	XSync (val[0], 0);
	success = TRUE;
    }
    else
    {
	Errorline ("could not load a font in %P.\n", g);
	success = FALSE;
    }

    end_builtin ();
}



/*****************************************************************/
/******** UnloadFont

  xcUnloadFont (+Connection, +Font)

  unload a font.

 */

int xcUnloadFont()
     
{
    include_var_builtin (2);
    ptr_definition types[2];


    types[0] = real;
    types[1] = real; /* 18.12 */

    begin_builtin (xcUnloadFont, 2, 2, types);

    XUnloadFont (val[0], val[1]);
    XSync (val[0], 0);
    success = TRUE;

    end_builtin ();
}



/*****************************************************************/
/******** DrawString

  xcDrawString (+Connection, +Drawable, +X, +Y, String,
                +Font, +Function, +Color)

  Print the string (only foreground).

*/

int xcDrawString()
{
    include_var_builtin (8);
    ptr_definition types[8];
    int j;
    GC gc;

    
    for (j = 0; j < 8; j++)
        types[j] = real;
    types[1] = xdrawable;
    types[4] = quoted_string;

    begin_builtin (xcDrawString, 8, 8, types);

    gc = DrawableGC (args[1]);
    x_set_gc (val[0], gc, val[6], val[7], xDefaultLineWidth, val[5]);

    XDrawString ((Display *) val[0], (Window) val[1], gc,  /* Display, Window, GC */
		 val[2], val[3], val[4],                   /* X, Y *//* String */
		 strlen ((char *) val[4]));                /* Lenght */

    x_record_string (WindowDisplayList (args[1]), DRAW_STRING,
		     val[2], val[3],       /* X, Y */
		     (char *) val[4],      /* String */
		     val[5],               /* Font */
		     val[6], val[7]);      /* Function, Color */

    XSync (val[0], 0);
    success = TRUE;

    end_builtin ();
}


/*****************************************************************/
/******** DrawImageString

  xcDrawImageString (+Connection, +Drawable, +X, +Y, String,
                     +Font, +Function, +Color)

  Print the string (foreground+background).

*/

int xcDrawImageString()
{
    include_var_builtin (8);
    ptr_definition types[8];
    int j;
    GC gc;

    
    for (j = 0; j < 8; j++)
        types[j] = real;
    types[1] = xdrawable;
    types[4] = quoted_string;

    begin_builtin (xcDrawImageString, 8, 8, types);

    gc = DrawableGC (args[1]);
    x_set_gc (val[0], gc, val[6], val[7], xDefaultLineWidth, val[5]);

    XDrawImageString (val[0], val[1], gc,           /* Display, Window, GC */
		      val[2], val[3],               /* X, Y */
		      val[4],                       /* String */
		      strlen ((char *) val[4]));    /* Lenght */

    x_record_string (WindowDisplayList (args[1]), DRAW_IMAGE_STRING,
		     val[2], val[3],                /* X, Y */
		     (char *) val[4],               /* String */
		     val[5],                        /* Font */
		     val[6], val[7]);               /* Function, Color */

    XSync (val[0], 0);
    success = TRUE;

    end_builtin ();
}


/*****************************************************************/
/******** SYNC

  xcSync (+Connection, +Discard)

  flush the output of the connection.

 */

int xcSync ()
     
{
    include_var_builtin (2);
    ptr_definition types[2];


    types[0] = real;
    types[1] = real;

    begin_builtin (xcSync, 2, 2, types);

    XSync (val[0], val[1]);
    success = TRUE;

    end_builtin ();
}



/*****************************************************************/
/******** EVENTtoPSITERM */

static ptr_psi_term xcEventToPsiTerm (event)

XEvent *event;

{
    ptr_psi_term psiEvent, psi_str;
    char buffer[10];
    char *str = " ";
    KeySym keysym;

/* - not used - jch - Wed Aug  5 20:10:44 MET DST 1992
    int n;
    XComposeStatus status;
*/


    psiEvent = stack_psi_term (4);
    stack_add_int_attr (psiEvent, "display", event->xany.display);
    stack_add_int_attr (psiEvent, "window", event->xany.window);

    switch (event->type)
    {
        case KeyPress:
        case KeyRelease:
	    psiEvent->type = xkeyboard_event;
	    stack_add_int_attr (psiEvent, "x", event->xkey.x);
	    stack_add_int_attr (psiEvent, "y", event->xkey.y);
	    stack_add_int_attr (psiEvent, "state", event->xkey.state);

	    buffer[0] = 0;
	    *str = 0;
	    /* n = XLookupString (event, buffer, sizeof(buffer), &keysym, &status); */
	    XLookupString (event, buffer, sizeof(buffer), &keysym, NULL);

	    stack_add_int_attr (psiEvent, "keycode", buffer[0]);

	    if (keysym == XK_Return || keysym == XK_KP_Enter || keysym == XK_Linefeed)
	        *str = CR;
	    else
	    if (keysym == XK_BackSpace || keysym == XK_Delete)
	        *str = BS;
	    else
	    if (isascii(buffer[0]))
	    /* if (isalnum (buffer[0]) || isspace (buffer[0])) 8.10 */
		*str = buffer[0];

	    stack_add_int_attr (psiEvent, "char", *str);
	    break;

	case ButtonPress:
	case ButtonRelease:
	    psiEvent->type = xmouse_button;
	    stack_add_int_attr (psiEvent, "x", event->xbutton.x);
	    stack_add_int_attr (psiEvent, "y", event->xbutton.y);
	    stack_add_int_attr (psiEvent, "state", event->xbutton.state);
	    stack_add_int_attr (psiEvent, "button", event->xbutton.button);
	    break;

	case Expose:
	    psiEvent->type = xexpose_event;
	    stack_add_int_attr (psiEvent, "width", event->xexpose.width);
	    stack_add_int_attr (psiEvent, "height", event->xexpose.height);
	    break;

	case DestroyNotify:
	    psiEvent->type = xdestroy_event;
	    break;

        default:
	    psiEvent->type = xevent;
	    break;
    }

    return psiEvent;
}


/*****************************************************************/

/* some stuff to handle a psi-list */

#define PsiList_FirstPsiElt(psiList) (psiList)
#define PsiList_IsEmpty(psiList) ((psiList) == NULL)
#define PsiElt_Next(psiElt) ((ptr_list)(psiElt)->value)->cdr
#define PsiElt_PsiTerm(psiElt) ((ptr_list)(psiElt)->value)->car


ptr_psi_term PsiList_LastPsiElt (psiList)
ptr_psi_term psiList;
{
    assert (psiList);

    while (PsiElt_Next (psiList) != NULL)
        psiList = PsiElt_Next (psiList);

    return psiList;
}


ptr_psi_term PsiList_AppendPsiTerm (psiList, psiTerm)
ptr_psi_term psiList, psiTerm;
{
    ptr_psi_term newElt, lastPsiElt;


    newElt = makePsiTerm (alist);
    newElt->value = (GENERIC)(STACK_ALLOC(list));
    PsiElt_PsiTerm (newElt) = psiTerm;
    PsiElt_Next (newElt) = NULL;

    if (PsiList_IsEmpty (psiList))
	return newElt;

    lastPsiElt = PsiList_LastPsiElt (psiList);
    /* Trailing 9.10 */
    push_ptr_value_global(psi_term_ptr, &PsiElt_Next (lastPsiElt));
    PsiElt_Next (lastPsiElt) = newElt;
    return psiList;
}


int PsiList_EnumPsiElt (psiList, proc, closure)
ptr_psi_term psiList;
int (*proc)();
int *closure;
{
    int	notInterrupted = TRUE;

    while (notInterrupted && psiList != NULL)
    {
	notInterrupted = (*proc)(psiList, closure);
	psiList = PsiElt_Next (psiList);
    }

    return notInterrupted;
}


int PsiList_EnumPsiTerm (psiList, proc, closure)
ptr_psi_term psiList;
int (*proc)();
int *closure;
{
    ptr_psi_term psiNext;
    int	notInterrupted = TRUE;

    while (notInterrupted && psiList != NULL)
    {
	/* save the next because the current could be removed 
	   (eg: xcFlushEvents) */
	psiNext = PsiElt_Next (psiList); 
	notInterrupted = (*proc)(PsiElt_PsiTerm (psiList), closure);
	psiList = psiNext;
    }

    return notInterrupted;
}


/* 9.10 Rewritten to do correct trailing */
void PsiList_RemovePsiTerm (psiList, psiTerm)
ptr_psi_term *psiList, psiTerm;
{
    ptr_psi_term *psiNext, *psiCur;

    assert (!PsiList_IsEmpty (*psiList));

    psiCur=psiList;
    psiNext= &PsiElt_Next(*psiList);

    while (PsiElt_PsiTerm(*psiCur)!=psiTerm) {
       psiCur=psiNext;
       psiNext= &PsiElt_Next(*psiNext);
    }

    push_ptr_value_global(psi_term_ptr, psiCur);
    *psiCur = *psiNext;

}


/*****************************************************************/
/* Static */
/* return FALSE if the events are matching */

static int x_union_event (psiEvent, closure)

ptr_psi_term psiEvent;
EventClosure *closure;

{
    return !(GetIntAttr (psiEvent, "display") == closure->display
	 && GetIntAttr (psiEvent, "window") == closure->window
	 && (GetIntAttr (psiEvent, "mask") & closure->mask) != 0);
}


/*****************************************************************/
/******** GetEvent

  xcGetEvent (+Display, +Window, +Mask)

  return an event matching the mask in the window.
  if no event residuate the call else return a null event.

 */

int xcGetEvent ()

{
    include_var_builtin (3);
    ptr_definition types[3];
    XEvent event;
    ptr_psi_term psiEvent;
    ptr_psi_term eventElt;
    EventClosure eventClosure;


    types[0] = real;
    types[1] = xwindow;
    types[2] = real;

    begin_builtin (xcGetEvent, 3, 3, types);

    if (!xevent_existing)
    {
#if 0
	if (XCheckWindowEvent (val[0], val[1], val[2], &event)
	    && event.xany.window == val[1])
	{
	    /* return a psi-term containing the event */
	    psiEvent = xcEventToPsiTerm (&event);
	}
	else /* no event */
#endif
	{
	    /* warning if a same event is already waiting */
	    eventClosure.display = val[0];
	    eventClosure.window  = val[1];
	    eventClosure.mask    = val[2];
	    if (!PsiList_EnumPsiTerm (xevent_list, x_union_event, &eventClosure))
	        infoline ("*** Warning: you are already waiting for same events in the same window !"); 

	    /* transform the request in a psi-term */
	    eventElt = stack_psi_term (4);
	    stack_add_int_attr (eventElt, "display", val[0]);
	    stack_add_int_attr (eventElt, "window", val[1]);
	    stack_add_int_attr (eventElt, "mask", val[2]);

	    /* add the request in the list of waiting events */
	    if (PsiList_IsEmpty (xevent_list))
	        push_ptr_value_global (psi_term_ptr, &xevent_list);
	    xevent_list = PsiList_AppendPsiTerm (xevent_list, eventElt);

	    /* residuate the call */
	    residuate (eventElt);

	    /* return a psi-term containing an `empty' event */
	    psiEvent = stack_psi_term (4);
	    psiEvent->type = xevent;
	}
    }
    else
    {
	/* get the event built by x_exist_event */
	psiEvent = GetPsiAttr (xevent_existing, "event");

	push_ptr_value_global (psi_term_ptr, &xevent_existing);
	xevent_existing = NULL;
    }

    push_goal (unify, psiEvent, aim->b, NULL);

    success = TRUE;

    end_builtin ();
}


/*****************************************************************/
/* Static */
/* remove the event from the queue if matching */

static int x_flush_event (eventElt, closure)
ptr_psi_term eventElt;
EventClosure *closure;
{
    ptr_psi_term psiEvent;


    psiEvent = PsiElt_PsiTerm (eventElt);
    if  (GetIntAttr (psiEvent, "display") == closure->display
      && GetIntAttr (psiEvent, "window") == closure->window
      && (GetIntAttr (psiEvent, "mask") & closure->mask) != 0)
    {
	/* 9.10 */
	/* if (xevent_list == eventElt) */
	/*     push_ptr_value_global (psi_term_ptr, &xevent_list); */
        /* xevent_list = PsiList_RemovePsiTerm (xevent_list, psiEvent); */
        PsiList_RemovePsiTerm (&xevent_list, psiEvent);
    }

    return TRUE;
}


/*****************************************************************/
/******** FlushEvents

  xcFlushEvents (+Display, +Window, +Mask)

  flush all residuated events matching (display, window, mask).

 */

int xcFlushEvents ()

{
    include_var_builtin (3);
    ptr_definition types[3];
    EventClosure eventClosure;


    types[0] = real;
    types[1] = xwindow;
    types[2] = real;

    begin_builtin (xcFlushEvents, 3, 3, types);

    eventClosure.display = val[0];
    eventClosure.window  = val[1];
    eventClosure.mask    = val[2];
    PsiList_EnumPsiElt (xevent_list, x_flush_event, &eventClosure);

    success = TRUE;

    end_builtin ();
}

#if 0

/*****************************************************************/
/******** xcSendEvent

  xcSendEvent (+Display, +Window, +Event)

  send the event to the specified window

 */

int xcSendEvent ()

{
    include_var_builtin (3);
    ptr_definition types[3];
    XEvent event;
    ptr_psi_term psiEvent;
    ptr_node nodeAttr;
    ptr_psi_term psiValue;
    

    types[0] = real;
    types[1] = xwindow;
    types[2] = xevent;

    begin_builtin (xcSendEvent, 3, 3, types);

    if (xcPsiEventToEvent (val[2], &event))
    {
	XSendEvent (val[0], val[1], False, ?, &event);
	success = TRUE;
    }
    else
    {
	Errorline ("%P is not an event in %P.", val[2], g);
	success = FALSE;
    }

    end_builtin ();
}

#endif

/*****************************************************************/
/******** SETUPBUILTINS

  Set up the X built-in predicates.

 */

void x_setup_builtins ()
     
{  
    raw_setup_builtins (); /* to move in life.c */

    XSetErrorHandler (x_handle_error);
    XSetIOErrorHandler (x_handle_fatal_error);

    xevent = update_symbol ("event");
    xkeyboard_event = update_symbol ("keyboard_event");
    xmouse_button = update_symbol ("mouse_button");
    xexpose_event = update_symbol ("expose_event");
    xdestroy_event = update_symbol ("destroy_event");

    xdisplay = update_symbol ("display");
    xdrawable = update_symbol ("drawable");
    xwindow = update_symbol ("window");
    xpixmap = update_symbol ("pixmap");

    xgc = update_symbol ("graphic_context");
    xdisplaylist = update_symbol ("display_list");

    new_built_in ("xcOpenConnection",      predicate, xcOpenConnection);
    new_built_in ("xcDefaultRootWindow",      predicate, xcDefaultRootWindow);
    new_built_in ("xcGetScreenAttribute",  predicate, xcGetScreenAttribute);
    new_built_in ("xcGetConnectionAttribute",  predicate, xcGetConnectionAttribute);
    new_built_in ("xcCloseConnection",     predicate, xcCloseConnection);

    new_built_in ("xcCreateSimpleWindow",  predicate, xcCreateSimpleWindow);
#if 0
    new_built_in ("xcCreateWindow",        predicate, xcCreateWindow);
#endif

    new_built_in ("xcSetStandardProperties",  predicate, xcSetStandardProperties);
    new_built_in ("xcGetWindowGeometry",   predicate, xcGetWindowGeometry);
    new_built_in ("xcSetWindowGeometry",   predicate, xcSetWindowGeometry);
    new_built_in ("xcGetWindowAttribute",  predicate, xcGetWindowAttribute);
    new_built_in ("xcSetWindowAttribute",  predicate, xcSetWindowAttribute);
    new_built_in ("xcMapWindow",           predicate, xcMapWindow);
    new_built_in ("xcUnmapWindow",         predicate, xcUnmapWindow);
    new_built_in ("xcSelectInput",         predicate, xcSelectInput);
    new_built_in ("xcRefreshWindow",       predicate, xcRefreshWindow);
    new_built_in ("xcPostScriptWindow",    predicate, xcPostScriptWindow);
    new_built_in ("xcDestroyWindow",       predicate, xcDestroyWindow);

    new_built_in ("xcCreateGC",            predicate, xcCreateGC);
    new_built_in ("xcGetGCAttribute",      predicate, xcGetGCAttribute);
    new_built_in ("xcSetGCAttribute",      predicate, xcSetGCAttribute);
    new_built_in ("xcDestroyGC",           predicate, xcDestroyGC);

    new_built_in ("xcDrawLine",            predicate, xcDrawLine);
    new_built_in ("xcDrawArc",             predicate, xcDrawArc);
    new_built_in ("xcDrawRectangle",       predicate, xcDrawRectangle);
    new_built_in ("xcDrawPolygon",         predicate, xcDrawPolygon);

    new_built_in ("xcLoadFont",            predicate, xcLoadFont);
    new_built_in ("xcUnloadFont",          predicate, xcUnloadFont);
    new_built_in ("xcDrawString",          predicate, xcDrawString);
    new_built_in ("xcDrawImageString",     predicate, xcDrawImageString);

    new_built_in ("xcRequestColor",        predicate, xcRequestColor);
    new_built_in ("xcRequestNamedColor",   predicate, xcRequestNamedColor);
    new_built_in ("xcFreeColor",           predicate, xcFreeColor);

    new_built_in ("xcFillRectangle",       predicate, xcFillRectangle);
    new_built_in ("xcFillArc",             predicate, xcFillArc);
    new_built_in ("xcFillPolygon",         predicate, xcFillPolygon);

    new_built_in ("xcPointsAlloc",         predicate, xcPointsAlloc);
    new_built_in ("xcCoordPut",            predicate, xcCoordPut);
    new_built_in ("xcPointsFree",          predicate, xcPointsFree);

    new_built_in ("xcSync",                predicate, xcSync);
    new_built_in ("xcGetEvent",            function,  xcGetEvent);
    new_built_in ("xcFlushEvents",         predicate, xcFlushEvents);
}


/*****************************************************************/
/* not a built-in */
/* called by what_next_aim in login.c */

static int WaitNextEvent (ptreventflag)
int *ptreventflag;
{
    int nfds, readfd, writefd, exceptfd;
    struct timeval timeout;
    int charflag = FALSE, nbchar;
    char c = 0;


    *ptreventflag = FALSE;
    timeout.tv_sec = 0;
    timeout.tv_usec = 100000;

    do
    {
	readfd = (1<<stdin_fileno);
	writefd = 0;
	exceptfd = 0;
	nfds = select (32, &readfd, &writefd, &exceptfd, &timeout);
	if (nfds == -1)
	{
#if 0
	    /* not an error, but a signal has been occured */
	    /* handle_interrupt(); does not work */
	    exit();
#endif
	    if (errno != EINTR) 
	    {
	        Errorline ("in select: interruption error.\n");
                exit_life (TRUE);
	    }
	    else 
		interrupt();
	}
        
	else
	if (nfds == 0)
	{
#ifdef X11
	    if (x_exist_event ())
	    {
		*ptreventflag = TRUE;
		start_of_line = TRUE;
	    }		
#endif
	}
	else
	{
	    if ((readfd & (1<<stdin_fileno)) != 0)
	    {
#if 0
		if ((nbchar = read (stdin_fileno, &c, 1)) == -1)
		{
		    Errorline ("in select: keyboard error.\n");
		    exit_life (TRUE);
		}

		/* see manpage of read */
		if (nbchar == 0)
		    c = EOF;
#endif
		c = fgetc (input_stream);
		charflag = TRUE;
	    }
	    else
	    {
		Errorline ("select error.\n");
		exit_life (TRUE);
	    }
	}
    } while (!(charflag || *ptreventflag));

    return c;
}

/*****************************************/


int x_read_stdin_or_event (ptreventflag)
int *ptreventflag;
{
    int c = 0;


    *ptreventflag = FALSE;
  
    if (c = saved_char) /* not an error ;-) */
    {
	saved_char = old_saved_char;
	old_saved_char=0;
    }
    else
    {
	if (feof (input_stream))
	    c = EOF;
	else 
	{
	    if (start_of_line) 
	    {
		start_of_line = FALSE;
		line_count ++ ;
		Infoline ("%s",prompt); /* 21.1 */
		fflush (output_stream);
	    }

	    c = WaitNextEvent (ptreventflag);

	    if (*ptreventflag)
	    {
		if (verbose) printf ("<X event>");
		if (NOTQUIET) printf ("\n"); /* 21.1 */
	    }
      
	    if (c == EOLN)
	        start_of_line = TRUE;
	}
    }

    return c;
}


/*****************************************************************/
/* Static */
/* returns TRUE if the mask matches the type */

static int mask_match_type (mask, type)
int mask, type;
{
    int i;

    for (i=0; mask && i<23; i++)
        if (mask & (1L<<i))
	    if (x_types[i] == type)
	        return TRUE;

    return FALSE;
}


/*****************************************************************/
/* Static */
/* returns the psi-event of the list corresponding to the existing event */

static ptr_psi_term x_what_psi_event (beginSpan, endSpan, eventType)
ptr_psi_term beginSpan, endSpan;
int eventType;
{
    if (beginSpan == endSpan)
        return PsiElt_PsiTerm (beginSpan);
    else
    if (mask_match_type (GetIntAttr (PsiElt_PsiTerm (beginSpan), "mask"),
			 eventType))
        return PsiElt_PsiTerm (beginSpan);
    else
        return x_what_psi_event (PsiElt_Next(beginSpan), 
			     endSpan, eventType);
}


/*****************************************************************/
/* Static */
/* builds xevent_existing */

static void x_build_existing_event (event, beginSpan, endSpan, eventType)
XEvent *event;
ptr_psi_term beginSpan, endSpan;
int eventType;
{
    ptr_psi_term psiEvent;


    /* get the event from the list */
    psiEvent = x_what_psi_event (beginSpan, endSpan, eventType);

    /* put the event on the waiting event */
    bk_stack_add_psi_attr (psiEvent, "event", xcEventToPsiTerm (event));

    /* set the global */
    if (xevent_existing)
        infoline ("*** Warning: xevent_existing non null in x_build_existing_event ?");
    push_ptr_value_global (psi_term_ptr, &xevent_existing);
    xevent_existing = psiEvent;

    /* remove the event from the list */
    /* 9.10 */
    /* if (PsiElt_PsiTerm (xevent_list) == psiEvent) */
    /*     push_ptr_value_global (psi_term_ptr, &xevent_list); */
    /* xevent_list = PsiList_RemovePsiTerm (xevent_list, psiEvent); */
    PsiList_RemovePsiTerm (&xevent_list, psiEvent);
}


/*****************************************************************/
/* Static */
/* get the next span of waiting events */

static int x_next_event_span (eventElt, eventClosure)
ptr_psi_term eventElt;
EventClosure *eventClosure;
{
    ptr_psi_term psiEvent;
    int display, window, mask;
    XEvent event;


    psiEvent = PsiElt_PsiTerm (eventElt);
    display = GetIntAttr (psiEvent, "display");
    window = GetIntAttr (psiEvent, "window");
    mask = GetIntAttr (psiEvent, "mask");

    if (eventClosure->display == NULL)
    {
	/* new span */
	eventClosure->display = display;
	eventClosure->window = window;
	eventClosure->mask = mask;
	eventClosure->beginSpan = eventElt;
	return TRUE;
    }
    else
    if (eventClosure->display == display
     && eventClosure->window == window)
    {
	/* same span */
	eventClosure->mask |= mask;
	return TRUE;
    }
    else
    /* a next span begins, check the current span */
    Repeat:
    if (XCheckWindowEvent (eventClosure->display, eventClosure->window,
			   eventClosure->mask, &event)
	&& event.xany.window == eventClosure->window)
    {
	/* 9.10 */
        /* printf("Event type = %d.\n", event.type); */
	if ((event.type==Expose || event.type==GraphicsExpose)
            && event.xexpose.count!=0) {
          /* printf("Expose count = %d.\n",  event.xexpose.count); */
          goto Repeat;
        }

	/* build a psi-term containing the event */
	x_build_existing_event (&event, 
				eventClosure->beginSpan, 
				eventElt, event.type); 
	return FALSE; /* stop ! we have an existing event !! */
    }
    else
    {
	/* init the new span */
	eventClosure->display = display;
	eventClosure->window = window;
	eventClosure->mask = mask;
	eventClosure->beginSpan = eventElt;
	return TRUE;
    }
}


/*****************************************************************/
/* not a built-in */
/* used by main_prove() and what_next() */

int x_exist_event ()
{
    XEvent event, exposeEvent;
    ptr_psi_term eventElt;
    EventClosure eventClosure;


    if (xevent_existing)
        return TRUE;

    if (PsiList_IsEmpty (xevent_list))
        return FALSE;

    /* traverse the list of waiting events */
    eventClosure.display = NULL;
    if (!PsiList_EnumPsiElt (xevent_list, x_next_event_span, &eventClosure))
        return TRUE;

    /* check the last span */
    if (XCheckWindowEvent (eventClosure.display,
			   eventClosure.window,
			   eventClosure.mask,
			   &event)
	&& event.xany.window == eventClosure.window)
    {
	if (event.type == Expose)
	    while (XCheckWindowEvent (eventClosure.display,
				      eventClosure.window,
				      ExposureMask,
				      &exposeEvent))
	        ; /* that is continue until no expose event */

	/* build a psi-term containing the event */
	x_build_existing_event (&event,
				eventClosure.beginSpan, 
				PsiList_LastPsiElt (xevent_list), 
				event.type);
	return TRUE;
    }
    else
        return FALSE;
}


/*****************************************************************/
/* used when backtracking a created window in order to destroy the window */

void x_destroy_window (display, window)

Display *display;
Window window;

{
/* we need the psi-term window (not the value) to get the display list, the pixmap ...
   jch - Fri Aug  7 15:29:14 MET DST 1992

    FreeWindow (display, window);
*/
    XDestroyWindow (display, window);
    XSync (display, 0);
}


/*****************************************************************/
/* used when backtracking a xcUnmapWindow in order to show the window */

void x_show_window (display, window)

int display, window;

{
    XMapWindow (display, window);
    XSync (display, 0);
}


/*****************************************************************/
/* used when backtracking a xcMapWindow in order to hide the window */

void x_hide_window (display, window)

int display, window;

{
    XUnmapWindow (display, window);
    XSync (display, 0);
}


/*****************************************************************/
/* not used anymore, but interesting */

ptr_goal GoalFromPsiTerm (psiTerm)

ptr_psi_term psiTerm;

{
    ptr_residuation resid;
    ptr_goal aim;
    

    if (psiTerm == NULL)
    {
	perr ("GoalFromPsiTerm: psiTerm is *null* ?");
        return FALSE;
    }

    if ((resid = psiTerm->resid) == NULL)
    {
	perr ("GoalFromPsiTerm: psiTerm has *no* residuate functions ?");
        return FALSE;
    }

    if (resid->next != NULL)
    {
	perr ("GoalFromPsiTerm: psiTerm has *several* residuate functions ?");
        return FALSE;
    }

    if ((aim = resid->goal) == NULL)
    {
	perr ("GoalFromPsiTerm: psiTerm has *no goal* ?");
        return FALSE;
    }

    return aim;
}


#endif
