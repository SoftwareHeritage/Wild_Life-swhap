# DIGITAL EQUIPMENT CORPORATION  CONFIDENTIAL AND PROPRIETARY
# Makefile for a typical library package requiring mips/ultrix split
# Last modified on Fri Mar 18 18:03:44 MET 1994 by rmeyer 
#      modified on Tue Feb 15 12:23:46 MET 1994 by dumant 
#      modified on Thu Oct 28 06:02:52 1993 by Rmeyer 
#      modified on Thu Jun 18 08:57:12 PDT 1992 by vanroy 
#      modified on Mon May 18 18:53:39 MET DST 1992 by herve  
#      modified on Tue Apr 23 15:16:52 1991 by Hassan 
# Sep. 13, 1993 by vanroy: 'make all' and 'make public' have been
# carefully separated.  The latter creates an independent wild_life
# system in $(PUBLICDIR).  Note that to make this work, the 'SETUP'
# replacement (sed commands) has been duplicated and called from
# the appropriate places.


# Edit this file as appropriate for your system.
#
# It comes with a pretty standard config, but you may need to make some
# changes. 
#

#***************************************************************************
# Which compiler to use: "cc" strongly recommended.

CC       = cc $(KEY)

# Digital's ANSI-compliant C compiler, generates better code on MIPS
#CC       = c89 -common $(KEY)

#CC       = gcc $(KEY)
# For some reason, Wild-LIFE won't run when compiled with 'gcc' on SUNs. It
# used to however. Now you can't even debug it using "-g" !!
# The funny thing is: 'gcc' works fine on Mips & Alpha.



#
# Flags for the compiler:
#
CCFLAGS     = -O2 $(MACROS)

#
# Compile-time macros, effect when -Defined:
#

# -DX11
# to compile with X predicates
#
# -DUNIF_DEBUG
# if defined causes the 'debug' mode to show matching and unification sub-goals
#
# -DGARBCOL
# if defined will cause the garbage collector to be called when memory is low
#
# -DNORAW
# if the raw terminal input file won't compile on your system.
# Note: on SUNs for some reason this file includes some things twice. This
# doesn't seem to matter.

# MEMORY is the number of words that the system will allocate.
# Because of the half-space GC, Wild-LIFE will actually allocate twice that
# many words. So on a 32-bit system, multiply by 8 to obtain the real memory
# usage in bytes.
# This can be overridden by the command line argument: "-memoryNNNNNNNN"

# Very big version
#MEMORY = 16777216

# Normal version
MEMORY = 2097152

# Teeny version
#MEMORY = 524288

# Add any other -Ds to this line:
MACROS      = -DX11 -DGARBCOL -DALLOC_WORDS=$(MEMORY)

# -DUNIF_DEBUG -DARITY

LOADFLAGS = -lm -lX11
# '-lm' for mathematical functions
# '-lX11' if '-DX11' is used.
# '-ldnet' for 'gcc' on Ultrix.



#***************************************************************
PACKAGE = Life

PROGRAM    = wild_life
XOBJECT    = xpred.o xdisplaylist.o
PROGOBJECT = print.o token.o trees.o parser.o info.o login.o copy.o \
             error.o built_ins.o types.o memory.o lefun.o interrupt.o \
	     templates.o list.o raw.o modules.o hash_table.o \
 	     bi_sys.o bi_math.o bi_type.o lub.o arity.o $(XOBJECT)

XSOURCE	   = xpred.c xdisplaylist.c
XINCLUDE   = xpred.h xdisplaylist.h

PROGSOURCE = $(XSOURCE) \
             print.c token.c trees.c parser.c login.c copy.c \
             error.c built_ins.c types.c memory.c lefun.c interrupt.c \
	     templates.c raw.c list.c modules.c hash_table.c \
             bi_sys.c bi_math.c bi_type.c lub.c arity.c lib.c 
PROGINCLUDE = $(XINCLUDE) \
             print.h token.h trees.h parser.h login.h copy.h \
             error.h built_ins.h types.h memory.h lefun.h interrupt.h \
	     templates.h raw.h list.h modules.h

OTHERSOURCE = life.c info.c
OTHERINCLUDE = info.h c_life.h extern.h

PROGSOURCELIFE = built_ins.lf term_expansion.lf onlinedoc.lf

MANPAGE    = $(PROGRAM).1

# All the files that need to be checked out to recreate the system:
CHECKS = README \
	 LICENSE \
	 .set_up_basis \
	 life_icon \
	 $(PROGSOURCE) \
	 $(PROGINCLUDE) \
	 $(OTHERSOURCE) \
	 $(OTHERINCLUDE) \
	 $(PROGSOURCELIFE) \
	 $(MANPAGE)

SRC	= ../src

LIBO    =
LIBA    = c_life.a
LIBOBJECT  = $(PROGOBJECT)

LINKS   = *.h *.c 


BIN     = $(PROGRAM)
LIB     = $(LIBO) $(LIBA) 




# DATADIR     = $(PACKAGE)Dir
SETUPDIR    = `pwd`
PUBLICDIR   = /udir/rmeyer/LIFE/PUBLIC
SETUP       = $(SETUPDIR)/.set_up
PUBLICSETUP = $(PUBLICDIR)/.set_up
# Please don't change this so we can tell which release you are using.
DATE        = Fri Mar 18 18:25:20 MET 1994
VERSION     = 1.0


FASTCCFLAGS = -O4 $(MACROS)


# Entry to bring the package up to date
#    The "make all" entry should be the first real entry
#    This section also includes the entries to rebuild everything
#    in each subdirectory.  These entries will normally be the same.

all: $(LIBA) $(PROGRAM) .set_up
	@echo
	@echo "Life generation done"
	@echo

public: public_liba public_life.o .public_set_up
	$(CC) -o $(PROGRAM) life.o  $(LIBA) $(LOADFLAGS)
	cp c_life.a c_life.h wild_life $(PUBLICDIR)
	cp .public_set_up $(PUBLICDIR)/.set_up
	cp $(PROGSOURCELIFE) $(PUBLICDIR)
	cp -r Tools $(PUBLICDIR)
	cp -r Examples $(PUBLICDIR)
	cp -r Lib $(PUBLICDIR)
	touch life.c lib.c .set_up

$(PROGRAM): $(LIBA) life.o
	$(CC) -o $(PROGRAM) life.o  $(LIBA) $(LOADFLAGS)

.public_set_up: .set_up_basis
	sed -e "s%+SETUPDIR+%$(PUBLICDIR)%g" < .set_up_basis > .public_set_up

.set_up: .set_up_basis
	sed -e "s%+SETUPDIR+%$(SETUPDIR)%g" < .set_up_basis > .set_up

# To create a 'fast' Life, i.e. to use the highest optimization level in
# the compiler.  For this, all .c files must be compiled together.
fast:	.set_up
	sed -e "s/+VERSION+/$(VERSION)/" \
	    -e "s/+DATE+/$(RELEASE)/" < info.c > Info.c
	sed -e "s%+SETUP+%$(SETUP)%" < life.c > Life.c

	$(CC) $(FASTCCFLAGS) -o fast_life $(PROGSOURCE) $(FASTLOADFLAGS)
	rm -f Life.c
	rm -f Info.c
	@echo
	@echo "Fast Life generation done"
	@echo
	
# ***************************************************************
# RCS

# Check out (without lock) all files necessary for building the system:
checkout:
	@(for f in $(CHECKS); do 	\
	     if [ ! -f $$f ]; then 	\
	        co $$f; 		\
	     else :; 			\
	     fi; 			\
	  done)


# Check in all files that have been checked out with lock (i.e., that
# potentially have been modified):
checkin:
	@(for f in $(CHECKS); do 	\
	      if [ -w $$f ]; then 	\
	         ci $$f; 		\
	      else :; 			\
	      fi; 			\
	  done)
	@(co Makefile)

# ***************************************************************
# Miscellaneous

lint:
	lint $(CFLAGS) *.c $(LOADFLAGS) > lint.lst


# ***************************************************************
# Standard entries to remove files from the directories
#    tidy    -- eliminate unwanted files
#    scratch -- delete derived files in preparation for rebuild

TIDIES =    -name ',*' \
         -o -name '@*' \
         -o -name '*~' \
         -o -name '.,*' \
         -o -name '.emacs_[0-9]*' \
         -o -name 'core' \
         -o -name 'a.out' \
         -o -name 'gmon.out' \
         -o -name 'gmonnub.out' \
         -o -name '*.pp'

tidy:
	find ./ \( $(TIDIES) \) -exec rm -f {} \;

scratch: tidy
	rm -f *.o *.a *.d core



.c.o:
	$(CC) $(CCFLAGS) -c $*.c

.s.o:
	$(AS) $(ASFLAGS) $*.s

# ***************************************************************

life.o: life.c extern.h trees.h print.h parser.h info.h login.h lefun.h \
	built_ins.h types.h copy.h token.h interrupt.h error.h modules.h
	sed -e "s%+SETUP+%$(SETUP)%" < life.c > Life.c
	$(CC) $(CCFLAGS) -c Life.c
	mv Life.o life.o # ; rm -f Life.c

lib.o: lib.c extern.h trees.h print.h parser.h info.h login.h lefun.h \
	built_ins.h types.h copy.h token.h interrupt.h error.h modules.h
	sed -e "s%+SETUP+%$(SETUP)%" < lib.c > Lib.c
	$(CC) $(CCFLAGS) -c Lib.c
	mv Lib.o lib.o # ; rm -f Lib.c

public_life.o: life.c extern.h trees.h print.h parser.h info.h login.h lefun.h \
	built_ins.h types.h copy.h token.h interrupt.h error.h modules.h
	sed -e "s%+SETUP+%$(PUBLICSETUP)%" < life.c > Life.c
	$(CC) $(CCFLAGS) -c Life.c
	mv Life.o life.o # ; rm -f Life.c

public_lib.o: lib.c extern.h trees.h print.h parser.h info.h login.h lefun.h \
	built_ins.h types.h copy.h token.h interrupt.h error.h modules.h
	sed -e "s%+SETUP+%$(PUBLICSETUP)%" < lib.c > Lib.c
	$(CC) $(CCFLAGS) -c Lib.c
	mv Lib.o lib.o # ; rm -f Lib.c

info.o: *.c *.h # compile theFri Mar 18 18:25:20 MET 1994if something has been changed
	@echo Don\'t be surprised, info is compiled "for "Fri Mar 18 18:25:20 MET 1994" because" something has changed
	sed -e "s/+VERSION+/$(VERSION)/" \
	    -e "s/+DATE+/$(DATE)/" < info.c > Info.c
	$(CC) $(CCFLAGS) -c Info.c
	mv Info.o info.o ; rm -f Info.c




# ***************************************************************
# Entry to reconstruct a library archive
#   The may-be-empty field is present to make this parse if LIBA=""

$(LIBA): $(LIBOBJECT) lib.o
	-rm -f $(LIBA)
	ar cr $(LIBA) $(LIBOBJECT) lib.o
	ranlib $(LIBA)

public_liba: $(LIBOBJECT) public_lib.o
	-rm -f $(LIBA)
	ar cr $(LIBA) $(LIBOBJECT) lib.o
	ranlib $(LIBA)



# profiling
prof:
	cc $(CFLAGS) -o proflife *.c $(LOADFLAGS) 
	pixie -o proflife.pixie proflife 
	proflife.pixie
	prof -pixie -proc proflife > result 
	rm -f proflife.* 
	lpr result



# ***************************************************************
# Dependencies

depend:
	makedepend $(PROGSOURCE)



# Anything past the following line will be deleted
# DO NOT DELETE THIS LINE -- make depend depends on it.
