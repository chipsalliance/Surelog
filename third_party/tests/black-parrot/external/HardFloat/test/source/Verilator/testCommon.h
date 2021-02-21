
/*============================================================================

This C++ header file is part of the Berkeley HardFloat IEEE Floating-Point
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

#ifndef testCommon_h
#define testCommon_h 1

#include <stdbool.h>
#include <stdint.h>

#define stringifyZ( a ) #a
#define stringify( a ) stringifyZ( a )

#define VAppendZ( a ) V##a
#define VAppend( a ) VAppendZ( a )

extern "C" {

    bool readHex128( uint64_t * );

    int_fast32_t recF16FromF16( uint16_t, bool );
    int_fast64_t recF32FromF32( uint32_t, bool );
    void f64ToRecF64( uint64_t, bool, uint64_t * );
    void f128ToRecF128( const uint64_t *, bool, uint64_t * );

    bool sameRecF16( int_fast32_t, int_fast32_t, bool );
    bool sameRecF32( int_fast64_t, int_fast64_t, bool );
    bool sameRecF64( const uint64_t *, const uint64_t *, bool );
    bool sameRecF128( const uint64_t *, const uint64_t *, bool );

}

#endif

