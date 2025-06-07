#/usr/bin/env bash
files=(**/*.cabal **/TODO.md piforall/test/Main.hs)

echo "ANONYMIZED" > rebound/LICENSE
echo "ANONYMIZED" > piforall/LICENSE
echo "ANONYMIZED" > benchmark/LICENSE

sed -i 's/ndesanto@seas.upenn.edu\|sweirich@cis.upenn.edu\|sweirich@seas.upenn.edu/anon@anon.com/ig' ${files[*]}
sed -i 's/Noe De Santo\|Stephanie Weirich\|sweirich\|ef55\|University of Pennsylvania/ANONYMIZED/ig' ${files[*]}

zip -r artifact.zip README.md rebound/ piforall/ benchmark/