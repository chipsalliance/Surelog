
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

#include <stdlib.h>
#include <stdio.h>
#include <verilated.h>
#include <time.h>
#include "config.h"
#include "testCommon.h"
#include "VmulAddRecF16.h"


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
        fputs( "test-mulAddRecF16: Invalid arguments.\n", stderr );
        return EXIT_FAILURE;
    }
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    fprintf(
        stderr,
        "Testing 'mulAddRecF16', control %X, rounding mode %d:\n",
        control,
        roundingMode
    );
    VmulAddRecF16 *modulePtr = new VmulAddRecF16;
    modulePtr->control = control;
    modulePtr->op = 0;
    modulePtr->roundingMode = roundingMode;
    long long errorCount = 0;
    long long count = 0;
    int partialCount = 0;
    for (;;) {
        /*--------------------------------------------------------------------
        *--------------------------------------------------------------------*/
        unsigned int a, b, c, expectOut;
        int expectExceptionFlags;
        if (
            scanf(
                "%x %x %x %x %x", &a, &b, &c, &expectOut, &expectExceptionFlags
            ) < 5
        ) {
            break;
        }
        ++partialCount;
        if ( partialCount == 10000 ) {
            count += 10000;
            fprintf( stderr, "\r%7lld", count );
            partialCount = 0;
        }
        long recA = recF16FromF16( a, true );
        long recB = recF16FromF16( b, true );
        long recC = recF16FromF16( c, true );
        long recExpectOut = recF16FromF16( expectOut, false );
        /*--------------------------------------------------------------------
        *--------------------------------------------------------------------*/
        modulePtr->a = recA;
        modulePtr->b = recB;
        modulePtr->c = recC;
        modulePtr->eval();
        long recOut = modulePtr->out;
        int exceptionFlags = modulePtr->exceptionFlags;
        if (
            !sameRecF16( recOut, recExpectOut, true )
                || (exceptionFlags != expectExceptionFlags)
        ) {
            fputc( '\r', stderr );
            if ( !errorCount ) {
                printf(
             "Errors found in 'mulAddRecF16', control %X, rounding mode %d:\n",
                    control,
                    roundingMode
                );
            }
            printf(
                "%05lX %05lX %05lX  => %05lX %02X  expected %05lX %02X\n",
                recA,
                recB,
                recC,
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

    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    // Integer multiplication test.
    fprintf( stderr, "Starting integer multiplication test...\n");
    srand(time(nullptr));

    modulePtr->op = 4;
    modulePtr->eval();
    for(int i = 0; i < 10000; ++i){
        uint16_t a = rand();
        uint16_t b = rand();
        uint16_t c = a * b;
        modulePtr->a = a;
        modulePtr->b = b;
        modulePtr->eval();
        if(modulePtr->out_imul != c){
            fprintf( stderr, "opA = %d, opB = %d, opC = %d act=%d \n", a, b, c, modulePtr->out_imul );
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
        "In %lld tests, no errors found in 'mulAddRecF16', "
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

