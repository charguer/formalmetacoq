SUBDIRS=tuto ln pretty

default: all

$(SUBDIRS)::
	$(MAKE) -C $@ $(MAKECMDGOALS)

all proofs vo vos vok clean : $(SUBDIRS)

