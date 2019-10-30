dir=$PWD
cd ~/projects/TPTP
dom=
prf=$(vampire --proof tptp "Problems/"${1:0:3}/$1)
neprf=${prf//!=/\\=}
cd $dir
echo "$neprf" > ${1%??}