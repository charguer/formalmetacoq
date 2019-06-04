
# You can define your own path to COQBIN and to TLC by creating a file called
# "settings.sh" and placing the right definitions into it, e.g.
#
# TLC=~/tlc/trunk/
# COQBIN=/var/tmp/coq-8.5/bin/
#
# Note that COQBIN should be the same as that used to compile TLC.
# Make sure to do "make clean" after any change to "settings.sh".

-include settings.sh

#######################################################

DEV_LAMBDA :=\
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

DEV_LAMBDAEXN :=\
	LambdaExn_Syntax \
	LambdaExn_Big \
	LambdaExn_Pretty \
	LambdaExn_Combi 


DEV_LAMBDAEXNERR :=\
	LambdaExn_Interp \
	LambdaExn_CombiErr \
	LambdaExn_BigErr \
	LambdaExn_Interp_CombiErr_Match \
	LambdaExn_Interp_BigErr_Match

DEV_CORECAML :=\
	CoreCaml_Syntax \
	CoreCaml_Pretty \
	CoreCaml_Small \
	CoreCaml_Big

#	CoreCaml_Interp \

DEV_LAMBDAEXNSUM :=\
	LambdaExnSum_Syntax \
	LambdaExnSum_Pretty \
	LambdaExnSum_Combi \
	LambdaExnSum_Small \
	LambdaExnSum_Big \
	LambdaExnSum_EncodeExn \
	LambdaExnSum_EncodeExn_Big_Correct 

#	LambdaExnSum_EncodeExn_Combi_Correct \
#	LambdaExnSum_EncodeExn_Small_Correct \

DEV_COMMAND :=\

#	Command_Syntax \
#	Command_Pretty \
#	Command_Small \

# TODO: sort at the end
DEV_BASE :=\
	Common \
	LibHeap \
	$(DEV_CORECAML) \
	$(DEV_COMMAND) \
	$(DEV_LAMBDAEXNSUM) \
	$(DEV_LAMBDAEXNERR) \
	$(DEV_LAMBDAEXN) \
	$(DEV_LAMBDA)

#	$(DEV_MINIML) \


#######################################################

PWD := $(shell pwd)

V := $(addprefix $(PWD)/, $(DEV_BASE:=.v))

V_AUX := $(wildcard $(TLC)/*.v)


##############################################################
# Rules

all: proof

COQFLAGS := -W -implicit-core-hint-db,-undeclared-scope
COQINCLUDE := -R $(TLC) TLC -R $(PWD) PRETTY 

include $(TLC)/Makefile.coq




