/* Copyright 1991 Digital Equipment Corporation.
** All Rights Reserved.
*****************************************************************/

#ifdef X11

extern ptr_psi_term xevent_list, xevent_existing;

extern ptr_definition xevent, xkeyboard_event, xmouse_button, 
                      xexpose_event, xdestroy_event, 
                      xdisplay, xdrawable, xwindow, xpixmap, 
                      xgc, xdisplaylist;

extern int x_window_creation;

extern void 	x_setup_builtins ();
extern int	x_exist_event ();
extern int 	x_read_stdin_or_event ();
extern void 	x_destroy_window();
extern void 	x_show_window();
extern void 	x_hide_window();

#endif
