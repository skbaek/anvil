dir=$PWD
cd ~/projects/TPTP
prf=$(vampire --proof tptp "Problems/"${1:0:3}/$1)
neprf=${prf//!=/\\=}
cd $dir
echo "$neprf" > ${2}
echo "$neprf"