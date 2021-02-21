
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
#include "config.h"
#include "testCommon.h"
#include "Vf32ToRecF32.h"

/*----------------------------------------------------------------------------
*----------------------------------------------------------------------------*/

int main( int argc, char *argv[] )
{
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
    fputs( "Testing 'f32ToRecF32'\n", stderr );
    Vf32ToRecF32 *modulePtr = new Vf32ToRecF32;
    long long errorCount = 0;
    long long count = 0;
    int partialCount = 0;
    for (;;) {
        /*--------------------------------------------------------------------
        *--------------------------------------------------------------------*/
        unsigned long in;
        if ( scanf( "%lx", &in ) < 1 ) break;
        ++partialCount;
        if ( partialCount == 10000 ) {
            count += 10000;
            fprintf( stderr, "\r%7lld", count );
            partialCount = 0;
        }
        long long expectOut = recF32FromF32( in, false );
        /*--------------------------------------------------------------------
        *--------------------------------------------------------------------*/
        modulePtr->in = in;
        modulePtr->eval();
        long long out = modulePtr->out;
        if ( !sameRecF32( out, expectOut, true ) ) {
            fputc( '\r', stderr );
            if ( !errorCount ) {
                fputs( "Errors found in 'f32ToRecF32'\n", stdout );
            }
            printf(
                "%08lX  => %09llX  expected %09llX\n", in, out, expectOut );
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
    printf( "In %lld tests, no errors found in 'f32ToRecF32'.\n", count );
    return 0;
    /*------------------------------------------------------------------------
    *------------------------------------------------------------------------*/
 errorStop:
    fprintf(
        stderr, "--> In %lld tests, %lld errors found.\n", count, errorCount );
    return EXIT_FAILURE;

}

