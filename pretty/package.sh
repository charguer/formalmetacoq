rm -Rf prettybigstep
mkdir prettybigstep
cp *.v prettybigstep
cp Makefile prettybigstep
cp README.txt prettybigstep
cp open.sh prettybigstep
mkdir prettybigstep/tlc
cp ~/tlc/trunk/*.v prettybigstep/tlc
rm prettybigstep/tlc/bin.v
tar -czf prettybigstep.tar.gz prettybigstep
cd prettybigstep
make -j
