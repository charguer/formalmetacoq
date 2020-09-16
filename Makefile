SUBDIRS=tuto ln pretty

default: all

$(SUBDIRS)::
	$(MAKE) -C $@ $(MAKECMDGOALS)

all clean : $(SUBDIRS)

