
/*============================================================================

This C++ source file is part of the Berkeley HardFloat IEEE Floating-Point
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

#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <verilated.h>
#include "config.h"
#include "testCommon.h"
#include unitVHeader

/*----------------------------------------------------------------------------
*----------------------------------------------------------------------------*/

int main( int argc, char *argv[] )
{
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    int control, roundingMode;
    char *ptr;
    ptr = argv[1];
    if ( !ptr || !*ptr ) goto argsError;
    control = strtol( ptr, &ptr, 16 );
    if ( *ptr ) goto argsError;
    ptr = argv[2];
    if ( !ptr || !*ptr ) goto argsError;
    roundingMode = strtol( ptr, &ptr, 10 );
    if ( *ptr ) {
 argsError:
        fputs(
            "test-" stringify( unitName ) ": Invalid arguments.\n", stderr );
        return EXIT_FAILURE;
    }
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    fprintf(
        stderr,
        "Testing '" stringify( unitName ) "', control %X, rounding mode %d:\n",
        control,
        roundingMode
    );
    VAppend( unitName ) *modulePtr = new VAppend( unitName );
    modulePtr->control = control;
    modulePtr->roundingMode = roundingMode;
    long long errorCount = 0;
    long long count = 0;
    int partialCount = 0;
    for (;;) {
        /*--------------------------------------------------------------------
        *--------------------------------------------------------------------*/
        unsigned long long a, b, expectOut;
        int expectExceptionFlags;
        if (
            scanf(
                "%llx %llx %llx %x", &a, &b, &expectOut, &expectExceptionFlags
            ) < 4
        ) {
            break;
        }
        ++partialCount;
        if ( partialCount == 10000 ) {
            count += 10000;
            fprintf( stderr, "\r%7lld", count );
            partialCount = 0;
        }
        uint64_t recA[2], recB[2], recExpectOut[2];
        f64ToRecF64( a, true, recA );
        f64ToRecF64( b, true, recB );
        f64ToRecF64( expectOut, false, recExpectOut );
        /*--------------------------------------------------------------------
        *--------------------------------------------------------------------*/
        modulePtr->a[2] = recA[1];
        modulePtr->a[1] = recA[0]>>32;
        modulePtr->a[0] = recA[0];
        modulePtr->b[2] = recB[1];
        modulePtr->b[1] = recB[0]>>32;
        modulePtr->b[0] = recB[0];
        modulePtr->eval();
        uint64_t recOut[2];
        recOut[1] = modulePtr->out[2];
        recOut[0] = (uint_fast64_t)modulePtr->out[1]<<32 | modulePtr->out[0];
        int exceptionFlags = modulePtr->exceptionFlags;
        if (
            !sameRecF64( recOut, recExpectOut, CHECKNANS )
                || (exceptionFlags != expectExceptionFlags)
        ) {
            fputc( '\r', stderr );
            if ( !errorCount ) {
                printf(
"Errors found in '" stringify( unitName ) "', control %X, rounding mode %d:\n",
                    control,
                    roundingMode
                );
            }
            printf(
                "%X%016llX %X%016llX  => %X%016llX %02X\n"
                "\texpected %X%016llX %02X\n",
                (unsigned int)recA[1],
                (unsigned long long)recA[0],
                (unsigned int)recB[1],
                (unsigned long long)recB[0],
                (unsigned int)recOut[1],
                (unsigned long long)recOut[0],
                exceptionFlags,
                (unsigned int)recExpectOut[1],
                (unsigned long long)recExpectOut[0],
                expectExceptionFlags
            );
            ++errorCount;
            if ( errorCount == maxNumErrors ) {
                count += partialCount;
                goto errorStop;
            }
        }
    }
    count += partialCount;
    fputs( "\r                        \r", stderr );
    if ( errorCount ) goto errorStop;
    printf(
        "In %lld tests, no errors found in '" stringify( unitName )
            "', control %X, rounding mode %d.\n",
        count,
        control,
        roundingMode
    );
    return 0;
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
 errorStop:
    fprintf(
        stderr, "--> In %lld tests, %lld errors found.\n", count, errorCount );
    return EXIT_FAILURE;

}

