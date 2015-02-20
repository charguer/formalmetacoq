############################################################################
# You can define your own path to COQBIN and to TLC by creating a file called
# "settings.sh" and placing the right definitions into it, e.g.
#
# TLC=~/tlc/trunk
# COQBIN=/var/tmp/coq-8.3pl2/bin/
#
# Note that TLC should have no leading slash, whereas COQBIN should have one.
# Note that if you rebind COQBIN you need to do the same in the TLC folder.
# Note that if you add a settings.sh file, you will need to do "make depend".

# Default paths for TLC and COQBIN are as follows:

TLC=tlc
COQBIN=

-include settings.sh


#######################################################

TLC_SRC=$(wildcard $(TLC)/*.v)
TLC_VO=$(TLC_SRC:.v=.vo)

#######################################################

INCLUDES=-I . -I $(TLC) 
COQC=$(COQBIN)coqc $(INCLUDES)
COQDEP=$(COQBIN)coqdep $(INCLUDES) 

#######################################################

# DEV_SRC=$(wildcard *.v)
# DEV_SRC:=$(filter-out bin.v, $(DEV_SRC))

DEV_LAMBDA=\
	Lambda_Syntax \
	Lambda_Big \
	Lambda_Pretty \
	Lambda_Combi \
	Lambda_Indexed \
	Lambda_PrettyErr \
	Lambda_CombiErr \
	Lambda_Typing \
	Lambda_Typing_PrettyErr_Sound \
	Lambda_Typing_CombiErr_Sound 
 #	Lambda_Trace \

DEV_LAMBDAEXN=\
	LambdaExn_Syntax \
	LambdaExn_Big \
	LambdaExn_Pretty \
	LambdaExn_Combi 


DEV_LAMBDAEXNERR=\
	LambdaExn_Interp \
	LambdaExn_CombiErr \
	LambdaExn_BigErr \
	LambdaExn_Interp_CombiErr_Match \
	LambdaExn_Interp_BigErr_Match

DEV_CORECAML=\
	CoreCaml_Syntax \
	CoreCaml_Pretty \
	CoreCaml_Small \
	CoreCaml_Big

#	CoreCaml_Interp \

DEV_LAMBDAEXNSUM=\
	LambdaExnSum_Syntax \
	LambdaExnSum_Pretty \
	LambdaExnSum_Combi \
	LambdaExnSum_Small \
	LambdaExnSum_Big \
	LambdaExnSum_EncodeExn \
	LambdaExnSum_EncodeExn_Big_Correct 

#	LambdaExnSum_EncodeExn_Combi_Correct \
#	LambdaExnSum_EncodeExn_Small_Correct \

DEV_COMMAND=\

#	Command_Syntax \
#	Command_Pretty \
#	Command_Small \

# TODO: sort at the end
DEV_BASE=\
	Common \
	$(DEV_CORECAML) \
	$(DEV_COMMAND) \
	$(DEV_LAMBDAEXNSUM) \
	$(DEV_LAMBDAEXNERR) \
	$(DEV_LAMBDAEXN) \
	$(DEV_LAMBDA)

#	$(DEV_MINIML) \


DEV_SRC=$(DEV_BASE:=.v)

#######################################################

DEPS=$(DEV_SRC) $(TLC_SRC)

#######################################################

.PHONY: all tlc depend clean
.SUFFIXES: .v .vo


#######################################################	

all: $(DEV_SRC:.v=.vo) 
	

#######################################################

.v.vo : .depend
	$(COQC) -I $(TLC) $<

#######################################################

init: 
	chmod +x open.sh

#######################################################
# DEPEND

depend: .depend

.depend : $(DEPS) Makefile
	$(COQDEP) $(DEPS) > .depend

ifeq ($(findstring $(MAKECMDGOALS),depend clean),)
include .depend
endif


#######################################################
# CLEAN

clean:
	bash -c "rm -f *.{vo,deps,dot,glob,ml,mli,cmi,cmx}"
	@rm -f .depend

