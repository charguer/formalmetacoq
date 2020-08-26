############################################################################
# You can define your own path to COQBIN and to TLC by creating a file called
# "settings.sh" and placing the right definitions into it, e.g.
#
# TLC=~/tlc/trunk/
# COQBIN=/var/tmp/coq-8.5/bin/
#
# Note that COQBIN should be the same as that used to compile TLC.
# Make sure to do "make clean" after any change to "settings.sh".

-include settings.sh


############################################################################
# STABLE DEVELOPMENTS

DEV_BASE :=\
  Classic \
  Coind \
	

#######################################################

PWD := $(shell pwd)

V := $(addprefix $(PWD)/, $(DEV_BASE:=.v))

V_AUX := $(wildcard $(TLC)/*.v)


##############################################################
# Rules

all: vo

COQINCLUDE := -R $(TLC) TLC -R $(PWD) TUTO 

include $(TLC)/Makefile.coq


