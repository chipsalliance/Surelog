
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
#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <verilated.h>
#include "config.h"
#include "testCommon.h"
#include "VdivSqrtRecF32_small_div.h"

enum { maxNumCyclesToDelay = 24 + 10 };

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
        fputs( "test-divSqrtRecF32_small_div: Invalid arguments.\n", stderr );
        return EXIT_FAILURE;
    }
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    fprintf(
        stderr,
        "Testing 'divSqrtRecF32_small_div', control %X, rounding mode %d:\n",
        control,
        roundingMode
    );
    VdivSqrtRecF32_small_div *modulePtr = new VdivSqrtRecF32_small_div;
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
    long long queue_recA[5], queue_recB[5];
    unsigned long queue_expectOut[5];
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
                    unsigned long a, b, expectOut;
                    int expectExceptionFlags;
                    if (
                        scanf(
                            "%lx %lx %lx %x",
                            &a,
                            &b,
                            &expectOut,
                            &expectExceptionFlags
                        ) < 4
                    ) {
                        moreIn = false;
                    } else {
                        long long recA = recF32FromF32( a, true );
                        long long recB = recF32FromF32( b, true );
                        modulePtr->a = recA;
                        modulePtr->b = recB;
                        ++queueCount;
                        memmove(
                            &queue_recA[1],
                            &queue_recA[0],
                            4 * sizeof(long long)
                        );
                        queue_recA[0] = recA;
                        memmove(
                            &queue_recB[1],
                            &queue_recB[0],
                            4 * sizeof(long long)
                        );
                        queue_recB[0] = recB;
                        memmove(
                            &queue_expectOut[1],
                            &queue_expectOut[0],
                            4 * sizeof(unsigned long)
                        );
                        queue_expectOut[0] = expectOut;
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
            long long recOut = modulePtr->out;
            int exceptionFlags = modulePtr->exceptionFlags;
            long long recExpectOut =
                recF32FromF32( queue_expectOut[queueCount], false );
            int expectExceptionFlags = queue_expectExceptionFlags[queueCount];
            if (
                !sameRecF32( recOut, recExpectOut, true )
                    || (exceptionFlags != expectExceptionFlags)
            ) {
                fputc( '\r', stderr );
                if ( !errorCount ) {
                    printf(
  "Errors found in 'divSqrtRecF32_small_div', control %X, rounding mode %d:\n",
                        control,
                        roundingMode
                    );
                }
                printf(
                    "%09llX %09llX  => %09llX %02X  expected %09llX %02X\n",
                    queue_recA[queueCount],
                    queue_recB[queueCount],
                    recOut,
                    exceptionFlags,
                    recExpectOut,
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
        "In %lld tests, no errors found in 'divSqrtRecF32_small_div', "
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

