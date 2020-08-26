
all:
	make -C tuto
	make -C ln
	make -C pretty

clean:
	make -C tuto clean
	make -C ln clean
	make -C pretty clean
