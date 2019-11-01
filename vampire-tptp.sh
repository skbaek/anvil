prf=$(vampire --proof tptp $1)
neprf=${prf//!=/\\=}
echo "$neprf" > ${1%??}