
/*============================================================================

This C source file is part of the Berkeley HardFloat IEEE Floating-Point
Arithmetic Package, Release 1, by John R. Hauser.

Copyright 2019 The Regents of the University of California.  All rights
reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

 1. Redistributions of source code must retain the above copyright notice,
    this list of conditions, and the following disclaimer.

 2. Redistributions in binary form must reproduce the above copyright notice,
    this list of conditions, and the following disclaimer in the documentation
    and/or other materials provided with the distribution.

 3. Neither the name of the University nor the names of its contributors may
    be used to endorse or promote products derived from this software without
    specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS "AS IS", AND ANY
EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE, ARE
DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE FOR ANY
DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

=============================================================================*/

#include <stdbool.h>
#include <stdint.h>
#include <ctype.h>
#include <stdlib.h>
#include <stdio.h>
#include "testCommon.h"

/*----------------------------------------------------------------------------
*----------------------------------------------------------------------------*/

bool readHex128( uint64_t *ptr )
{
    int ch;
    uint_fast64_t out64, out0;
    int numDigits, digit;

    do {
        ch = fgetc( stdin );
    } while ( isspace( ch ) );
    out64 = 0;
    out0  = 0;
    numDigits = 0;
    for (;;) {
        if ( ('0' <= ch) && (ch <= '9') ) {
            digit = ch - '0';
        } else if ( ('A' <= ch) && (ch <= 'F') ) {
            digit = ch - ('A' - 10);
        } else if ( ('a' <= ch) && (ch <= 'f') ) {
            digit = ch - ('a' - 10);
        } else {
            break;
        }
        ++numDigits;
        if ( 32 < numDigits ) return false;
        out64 = out64<<4 | out0>>60;
        out0  = out0<<4  | digit;
        ch = fgetc( stdin );
    }
    if ( !numDigits ) return false;
    ptr[1] = out64;
    ptr[0] = out0;
    return true;

}

/*----------------------------------------------------------------------------
*----------------------------------------------------------------------------*/

int_fast32_t recF16FromF16( uint16_t in, bool addRandomness )
{
    bool sign;
    int exp, fract;

    sign = in>>15 & 1;
    exp = in>>10 & 0x1F;
    fract = in & 0x3FF;
    if ( exp == 0x1F ) {
        if ( fract ) {
            exp = 0x38;
        } else {
            exp = 0x30;
            if ( addRandomness ) fract = rand() & 0x3FF;
        }
        if ( addRandomness ) exp |= rand() & 7;
    } else {
        if ( exp == 0 ) {
            if ( fract < 4 ) {
                if ( !fract ) {
                    if ( addRandomness ) exp = rand() & 7;
                    goto done;
                }
                exp -= 8;
                fract <<= 8;
            } else if ( fract < 0x40 ) {
                exp -= 4;
                fract <<= 4;
            }
            if ( fract < 0x100 ) {
                exp -= 2;
                fract <<= 2;
            }
            if ( !(fract & 0x200) ) {
                --exp;
                fract <<= 1;
            }
            fract = (fract<<1) - 0x400;
        }
        exp += 0x011;
    }
 done:
    return (int_fast32_t)sign<<16 | (int_fast32_t)exp<<10 | fract;

}

/*----------------------------------------------------------------------------
*----------------------------------------------------------------------------*/

int_fast64_t recF32FromF32( uint32_t in, bool addRandomness )
{
    bool sign;
    int exp;
    int_fast32_t fract;

    sign = in>>31 & 1;
    exp = in>>23 & 0xFF;
    fract = in & 0x7FFFFF;
    if ( exp == 0xFF ) {
        if ( fract ) {
            exp = 0x1C0;
        } else {
            exp = 0x180;
            if ( addRandomness ) {
                fract = (((uint_fast32_t)rand()<<15) + rand()) & 0x7FFFFF;
            }
        }
        if ( addRandomness ) exp |= rand() & 0x3F;
    } else {
        if ( exp == 0 ) {
            if ( fract < 0x80 ) {
                if ( !fract ) {
                    if ( addRandomness ) exp = rand() & 0x3F;
                    goto done;
                }
                exp -= 16;
                fract <<= 16;
            } else if ( fract < 0x8000 ) {
                exp -= 8;
                fract <<= 8;
            }
            if ( fract < 0x80000 ) {
                exp -= 4;
                fract <<= 4;
            }
            if ( fract < 0x200000 ) {
                exp -= 2;
                fract <<= 2;
            }
            if ( !(fract & 0x400000) ) {
                --exp;
                fract <<= 1;
            }
            fract = (fract<<1) - 0x800000;
        }
        exp += 0x081;
    }
 done:
    return (int_fast64_t)sign<<32 | (int_fast64_t)exp<<23 | fract;

}

/*----------------------------------------------------------------------------
*----------------------------------------------------------------------------*/

void f64ToRecF64( uint64_t in, bool addRandomness, uint64_t *outPtr )
{
    bool sign;
    int exp;
    int_fast64_t fract;

    sign = in>>63 & 1;
    exp = in>>52 & 0x7FF;
    fract = in & UINT64_C( 0xFFFFFFFFFFFFF );
    if ( exp == 0x7FF ) {
        if ( fract ) {
            exp = 0xE00;
        } else {
            exp = 0xC00;
            if ( addRandomness ) {
                fract =
                    (((uint_fast64_t)rand()<<45) + ((uint_fast64_t)rand()<<30)
                         + ((uint_fast64_t)rand()<<15) + rand())
                        & UINT64_C( 0xFFFFFFFFFFFFF );
            }
        }
        if ( addRandomness ) exp |= rand() & 0x1FF;
    } else {
        if ( exp == 0 ) {
            if ( fract < 0x100000 ) {
                if ( !fract ) {
                    if ( addRandomness ) exp = rand() & 0x1FF;
                    goto done;
                }
                exp -= 32;
                fract <<= 32;
            }
            if ( fract < INT64_C( 0x1000000000 ) ) {
                exp -= 16;
                fract <<= 16;
            }
            if ( fract < INT64_C( 0x100000000000 ) ) {
                exp -= 8;
                fract <<= 8;
            }
            if ( fract < INT64_C( 0x1000000000000 ) ) {
                exp -= 4;
                fract <<= 4;
            }
            if ( fract < INT64_C( 0x4000000000000 ) ) {
                exp -= 2;
                fract <<= 2;
            }
            if ( !(fract & INT64_C( 0x8000000000000 )) ) {
                --exp;
                fract <<= 1;
            }
            fract = (fract<<1) - INT64_C( 0x10000000000000 );
        }
        exp += 0x401;
    }
 done:
    outPtr[1] = sign;
    outPtr[0] = (uint_fast64_t)exp<<52 | fract;

}

/*----------------------------------------------------------------------------
*----------------------------------------------------------------------------*/

void
 f128ToRecF128( const uint64_t *inPtr, bool addRandomness, uint64_t *outPtr )
{
    uint_fast64_t in64;
    bool sign;
    int exp;
    int_fast64_t fract64;
    uint_fast64_t fract0;

    in64 = inPtr[1];
    sign = in64>>63 & 1;
    exp = in64>>48 & 0x7FFF;
    fract64 = in64 & UINT64_C( 0xFFFFFFFFFFFF );
    fract0 = inPtr[0];
    if ( exp == 0x7FFF ) {
        if ( fract64 | fract0 ) {
            exp = 0xE000;
        } else {
            exp = 0xC000;
            if ( addRandomness ) {
                fract64 =
                    (((uint_fast64_t)rand()<<45) + ((uint_fast64_t)rand()<<30)
                         + ((uint_fast64_t)rand()<<15) + rand())
                        & UINT64_C( 0xFFFFFFFFFFFF );
                fract0 =
                    ((uint_fast64_t)rand()<<60) + ((uint_fast64_t)rand()<<45)
                        + ((uint_fast64_t)rand()<<30)
                        + ((uint_fast64_t)rand()<<15) + rand();
            }
        }
        if ( addRandomness ) exp |= rand() & 0x1FFF;
    } else {
        if ( exp == 0 ) {
            if ( !fract64 && (fract0 < UINT64_C( 0x1000000000000 )) ) {
                if ( !fract0 ) {
                    if ( addRandomness ) exp = rand() & 0x1FFF;
                    goto done;
                }
                exp -= 64;
                fract64 = fract0;
                fract0  = 0;
            }
            if ( fract64 < 0x10000 ) {
                exp -= 32;
                fract64 = fract64<<32 | (int_fast64_t)(fract0>>32);
                fract0 <<= 32;
            }
            if ( fract64 < INT64_C( 0x100000000 ) ) {
                exp -= 16;
                fract64 = fract64<<16 | (int_fast64_t)(fract0>>48);
                fract0 <<= 16;
            }
            if ( fract64 < INT64_C( 0x10000000000 ) ) {
                exp -= 8;
                fract64 = fract64<<8 | (int_fast64_t)(fract0>>56);
                fract0 <<= 8;
            }
            if ( fract64 < INT64_C( 0x100000000000 ) ) {
                exp -= 4;
                fract64 = fract64<<4 | (int_fast64_t)(fract0>>60);
                fract0 <<= 4;
            }
            if ( fract64 < INT64_C( 0x400000000000 ) ) {
                exp -= 2;
                fract64 = fract64<<2 | (int_fast64_t)(fract0>>62);
                fract0 <<= 2;
            }
            if ( !(fract64 & INT64_C( 0x800000000000 )) ) {
                --exp;
                fract64 = fract64<<1 | (int_fast64_t)(fract0>>63);
                fract0 <<= 1;
            }
            fract64 =
                ((fract64<<1) - INT64_C( 0x1000000000000 ))
                    | (int_fast64_t)(fract0>>63);
            fract0 <<= 1;
        }
        exp += 0x4001;
    }
 done:
    outPtr[2] = sign;
    outPtr[1] = (uint_fast64_t)exp<<48 | fract64;
    outPtr[0] = fract0;

}

/*----------------------------------------------------------------------------
*----------------------------------------------------------------------------*/

bool sameRecF16( int_fast32_t a, int_fast32_t b, bool checkNaNs )
{
    int top4A, top4B, top3ExpA;

    if ( a == b ) return true;
    top4A = a>>13;
    top4B = b>>13;
    top3ExpA = top4A & 7;
    if ( top4A != top4B ) {
        return (top3ExpA == 7) && ((top4B & 7) == 7) && !checkNaNs;
    }
    if ( top3ExpA == 6 ) return true;
    if ( top3ExpA == 7 ) {
        if ( !checkNaNs ) return true;
    } else {
        if ( top3ExpA != 0 ) return false;
    }
    return ((a & 0x3FF) == (b & 0x3FF));

}

/*----------------------------------------------------------------------------
*----------------------------------------------------------------------------*/

bool sameRecF32( int_fast64_t a, int_fast64_t b, bool checkNaNs )
{
    int top4A, top4B, top3ExpA;

    if ( a == b ) return true;
    top4A = a>>29;
    top4B = b>>29;
    top3ExpA = top4A & 7;
    if ( top4A != top4B ) {
        return (top3ExpA == 7) && ((top4B & 7) == 7) && !checkNaNs;
    }
    if ( top3ExpA == 6 ) return true;
    if ( top3ExpA == 7 ) {
        if ( !checkNaNs ) return true;
    } else {
        if ( top3ExpA != 0 ) return false;
    }
    return ((a & 0x7FFFFF) == (b & 0x7FFFFF));

}

/*----------------------------------------------------------------------------
*----------------------------------------------------------------------------*/

bool sameRecF64( const uint64_t *aPtr, const uint64_t *bPtr, bool checkNaNs )
{
    uint_fast64_t a0, b0;
    int top3ExpA, top3ExpB;

    a0 = aPtr[0];
    b0 = bPtr[0];
    if ( aPtr[1] != bPtr[1] ) {
        return (a0>>61 == 7) && (b0>>61 == 7) && !checkNaNs;
    }
    if ( a0 == b0 ) return true;
    top3ExpA = a0>>61;
    top3ExpB = b0>>61;
    if ( top3ExpA != top3ExpB ) return false;
    if ( top3ExpA == 6 ) return true;
    if ( top3ExpA == 7 ) {
        if ( !checkNaNs ) return true;
    } else {
        if ( top3ExpA != 0 ) return false;
    }
    return
        ((a0 & UINT64_C( 0xFFFFFFFFFFFFF ))
             == (b0 & UINT64_C( 0xFFFFFFFFFFFFF )));

}

/*----------------------------------------------------------------------------
*----------------------------------------------------------------------------*/

bool sameRecF128( const uint64_t *aPtr, const uint64_t *bPtr, bool checkNaNs )
{
    uint_fast64_t a64, a0, b64, b0;
    int top3ExpA, top3ExpB;

    a64 = aPtr[1];
    b64 = bPtr[1];
    if ( aPtr[2] != bPtr[2] ) {
        return (a64>>61 == 7) && (b64>>61 == 7) && !checkNaNs;
    }
    a0  = aPtr[0];
    b0  = bPtr[0];
    if ( (a64 == b64) && (a0 == b0) ) return true;
    top3ExpA = a64>>61;
    top3ExpB = b64>>61;
    if ( top3ExpA != top3ExpB ) return false;
    if ( top3ExpA == 6 ) return true;
    if ( top3ExpA == 7 ) {
        if ( !checkNaNs ) return true;
    } else {
        if ( top3ExpA != 0 ) return false;
    }
    return
        (a0 == b0)
            && ((a64 & UINT64_C( 0xFFFFFFFFFFFF ))
                    == (b64 & UINT64_C( 0xFFFFFFFFFFFF )));

}

