#/usr/bin/env bash
files=(piforall/pi-forall.cabal benchmark/LICENSE piforall/LICENSE)

sed -i 's/Noe De Santo\|Stephanie Weirich\|University of Pennsylvania/ANONYMIZED/ig' ${files[*]}
sed -i 's/ndesanto@seas.upenn.edu\|sweirich@cis.upenn.edu\|sweirich@seas.upenn.edu/anon@anon.com/ig' ${files[*]}