COQBIN=
TLC=
if [ -f settings.sh ]
then
    source settings.sh 
fi
${COQBIN}coqide -R ${TLC} TLC -R . LN $*
