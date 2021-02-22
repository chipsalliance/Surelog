
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

#include <stdbool.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <verilated.h>
#include "config.h"
#include "testCommon.h"
#include "VdivSqrtRecF128_small_sqrt.h"

enum { maxNumCyclesToDelay = 113 + 10 };

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
            "test-divSqrtRecF128_small_sqrt: Invalid arguments.\n", stderr );
        return EXIT_FAILURE;
    }
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    fprintf(
        stderr,
        "Testing 'divSqrtRecF128_small_sqrt', control %X, rounding mode %d:\n",
        control,
        roundingMode
    );
    VdivSqrtRecF128_small_sqrt *modulePtr = new VdivSqrtRecF128_small_sqrt;
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    modulePtr->control = control;
    modulePtr->inValid = 0;
    modulePtr->roundingMode = roundingMode;
    modulePtr->clock = 1;
    modulePtr->nReset = 0;
    modulePtr->eval();
    modulePtr->nReset = 1;
    modulePtr->eval();
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    uint64_t queue_recA[5][3], queue_expectOut[5][2];
    int queue_expectExceptionFlags[5];
    long long errorCount = 0;
    long long count = 0;
    int partialCount = 0;
    bool moreIn = true;
    int queueCount = 0;
    int delayCountdown = 0;
    while ( moreIn || queueCount ) {
        /*--------------------------------------------------------------------
        *--------------------------------------------------------------------*/
        if ( modulePtr->inReady ) {
            modulePtr->inValid = 0;
            if ( 0 < delayCountdown ) {
                --delayCountdown;
                if ( !delayCountdown ) modulePtr->inValid = 1;
            } else {
                if ( moreIn ) {
                    uint64_t a[2], expectOut[2];
                    int expectExceptionFlags;
                    if ( !readHex128( a ) || !readHex128( expectOut ) ) {
                        goto notMoreIn;
                    }
                    if ( scanf( "%x", &expectExceptionFlags ) < 1 ) {
                 notMoreIn:
                        moreIn = false;
                    } else {
                        uint64_t recA[3];
                        f128ToRecF128( a, true, recA );
                        modulePtr->a[4] = recA[2];
                        modulePtr->a[3] = recA[1]>>32;
                        modulePtr->a[2] = recA[1];
                        modulePtr->a[1] = recA[0]>>32;
                        modulePtr->a[0] = recA[0];
                        ++queueCount;
                        memmove(
                            &queue_recA[1],
                            &queue_recA[0],
                            12 * sizeof(uint64_t)
                        );
                        queue_recA[0][0] = recA[0];
                        queue_recA[0][1] = recA[1];
                        queue_recA[0][2] = recA[2];
                        memmove(
                            &queue_expectOut[1],
                            &queue_expectOut[0],
                            8 * sizeof(uint64_t)
                        );
                        queue_expectOut[0][0] = expectOut[0];
                        queue_expectOut[0][1] = expectOut[1];
                        memmove(
                            &queue_expectExceptionFlags[1],
                            &queue_expectExceptionFlags[0],
                            4 * sizeof(int)
                        );
                        queue_expectExceptionFlags[0] = expectExceptionFlags;
                        delayCountdown = rand() % maxNumCyclesToDelay;
                        if ( !delayCountdown ) modulePtr->inValid = 1;
                    }
                }
            }
        }
        /*--------------------------------------------------------------------
        *--------------------------------------------------------------------*/
        if ( modulePtr->outValid ) {
            if ( !queueCount ) {
                fputs( "--> Spurious 'outValid'.\n", stderr );
                return EXIT_FAILURE;
            }
            ++partialCount;
            if ( partialCount == 10000 ) {
                count += 10000;
                fprintf( stderr, "\r%7lld", count );
                partialCount = 0;
            }
            --queueCount;
            uint64_t recOut[3];
            recOut[2] = modulePtr->out[4];
            recOut[1] =
                (uint_fast64_t)modulePtr->out[3]<<32 | modulePtr->out[2];
            recOut[0] =
                (uint_fast64_t)modulePtr->out[1]<<32 | modulePtr->out[0];
            int exceptionFlags = modulePtr->exceptionFlags;
            uint64_t recExpectOut[3];
            f128ToRecF128( queue_expectOut[queueCount], false, recExpectOut );
            int expectExceptionFlags = queue_expectExceptionFlags[queueCount];
            if (
                !sameRecF128( recOut, recExpectOut, true )
                    || (exceptionFlags != expectExceptionFlags)
            ) {
                fputc( '\r', stderr );
                if ( !errorCount ) {
                    printf(
"Errors found in 'divSqrtRecF128_small_sqrt', control %X, rounding mode %d:\n",
                        control,
                        roundingMode
                    );
                }
                printf(
                    "%X%016llX%016llX  => %X%016llX%016llX %02X\n"
                    "\texpected %X%016llX%016llX %02X\n",
                    (unsigned int)queue_recA[queueCount][2],
                    (unsigned long long)queue_recA[queueCount][1],
                    (unsigned long long)queue_recA[queueCount][0],
                    (unsigned int)recOut[2],
                    (unsigned long long)recOut[1],
                    (unsigned long long)recOut[0],
                    exceptionFlags,
                    (unsigned int)recExpectOut[2],
                    (unsigned long long)recExpectOut[1],
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
        /*--------------------------------------------------------------------
        *--------------------------------------------------------------------*/
        modulePtr->clock = 0;
        modulePtr->eval();
        modulePtr->clock = 1;
        modulePtr->eval();
    }
    count += partialCount;
    fputs( "\r                        \r", stderr );
    if ( errorCount ) goto errorStop;
    printf(
        "In %lld tests, no errors found in 'divSqrtRecF128_small_sqrt', "
            "control %X, rounding mode %d.\n",
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

