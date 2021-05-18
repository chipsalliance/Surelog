#!/bin/sh

cat <<EOF
#ifndef ASM_OFFSETS_H
#define ASM_OFFSETS_H
/* Derived from $1 by make_offsets.sh */

$(grep '#define' $1)
#endif /* ASM_OFFSETS_H */
EOF
