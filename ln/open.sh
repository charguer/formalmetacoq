COQBIN=
TLC=
if [ -f settings.sh ]
then
    source settings.sh
fi
${COQBIN}coqide -async-proofs off -async-proofs-command-error-resilience off -R ${TLC} TLC -R . LN $*
