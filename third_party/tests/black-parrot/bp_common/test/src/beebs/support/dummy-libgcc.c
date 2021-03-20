/* Dummyy libgcc for the benchmarks

   Copyright (C) 2018 Embecosm Limited

   Contributor: Jeremy Bennett <jeremy.bennett@embecosm.com>

   This file is part of the Bristol/Embecosm Embedded Benchmark Suite.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.

   SPDX-License-Identifier: GPL-3.0-or-later */

/* The purpose of this library is to measure the size of code excluding target
   dependent libgcc code. It only makes sense if it is used with
   -gc-sections. */


/* Missing ARM emulation functions */

#ifdef __arm__

unsigned long long
__aeabi_ui2d (unsigned int value __attribute__ ((unused)) )
{
  return 0;
}

float
__aeabi_ui2f (unsigned int value __attribute__ ((unused)) )
{
  return 0;
}

double
__aeabi_dmul (double FirstValue __attribute__ ((unused)) ,
	      double SecondValue __attribute__ ((unused)) )
{
  return 0.0;
}


unsigned int
__aeabi_d2uiz (double Value __attribute__ ((unused)) )
{
  return 0;
}


double
__aeabi_dadd (double FirstValue __attribute__ ((unused)),
	      double SecondValue __attribute__ ((unused)) )
{
  return 0.0;
}


double
__aeabi_dsub (double FirstValue __attribute__ ((unused)),
	      double SecondValue __attribute__ ((unused)) )
{
  return 0.0;

}


int
__aeabi_d2iz (double Value __attribute__ ((unused)) )
{
  return 0;
}


double
__aeabi_ddiv (double Dividend __attribute__ ((unused)),
	      double Divisor __attribute__ ((unused)) )
{
  return 0.0;
}


int
__aeabi_dcmplt (double Left __attribute__ ((unused)),
		double Right __attribute__ ((unused)) )
{
  return 0;
}


int
__aeabi_dcmpeq (double Left __attribute__ ((unused)),
		double Right __attribute__ ((unused)) )
{
  return 0;
}


int
__aeabi_dcmpge (double Left __attribute__ ((unused)),
		double Right __attribute__ ((unused)) )
{
  return  0;
}


int
__aeabi_dcmple (double Left __attribute__ ((unused)),
		double Right __attribute__ ((unused)) )
{
  return  0;
}


int
__aeabi_dcmpun (double a __attribute__ ((unused)),
		double b __attribute__ ((unused)) )
{
  return 0;
}


double
__aeabi_i2d (int Value __attribute__ ((unused)) )
{
  return 0.0;
}


int
__aeabi_dcmpgt (double Left __attribute__ ((unused)),
		double Right __attribute__ ((unused)))
{
  return 0;
}


float
__aeabi_fadd (float FirstValue __attribute__ ((unused)),
	      float SecondValue __attribute__ ((unused)) )
{
  return 0.0;
}


int
__aeabi_fcmpeq (float Left __attribute__ ((unused)),
		float Right __attribute__ ((unused)) )
{
  return 0;
}


int
__aeabi_fcmpge (float Left __attribute__ ((unused)),
		float Right __attribute__ ((unused)) )
{
  return  0;
}


int
__aeabi_fcmple (float Left __attribute__ ((unused)),
		float Right __attribute__ ((unused)) )
{
  return  0;
}


int
__aeabi_fcmpgt (float Left __attribute__ ((unused)),
		float Right __attribute__ ((unused)))
{
  return 0;
}


int
__aeabi_fcmplt (float Left __attribute__ ((unused)),
		float Right __attribute__ ((unused)) )
{
  return 0;
}


float
__aeabi_fsub (float FirstValue __attribute__ ((unused)),
	      float SecondValue __attribute__ ((unused)) )
{
  return 0.0;
}


float
__aeabi_i2f (int Value __attribute__ ((unused)) )
{
  return 0.0;
}


float
__aeabi_fmul (float FirstValue __attribute__ ((unused)) ,
	      float SecondValue __attribute__ ((unused)) )
{
  return 0.0;
}


float
__aeabi_fdiv (float Dividend __attribute__ ((unused)),
	      float Divisor __attribute__ ((unused)) )
{
  return 0.0;
}


int
__aeabi_f2iz (float Value __attribute__ ((unused)) )
{
  return 0;
}


unsigned int
__aeabi_f2uiz (float Value __attribute__ ((unused)) )
{
  return 0;
}


float
__aeabi_d2f (double Value __attribute__ ((unused)) )
{
  return 0.0;
}


double
__aeabi_f2d (float Value __attribute__ ((unused)) )
{
  return 0.0;
}


typedef struct { unsigned long long int quot;
  unsigned long long int rem;} uldivmod_t;

uldivmod_t
__aeabi_uldivmod(unsigned long long int numerator __attribute__ ((unused)),
		 unsigned long long int denominator __attribute__ ((unused)) )
{
  uldivmod_t v = {0, 0};

  return v;
}

#else /* !__ARM__ */

/* Generic libgcc functions */

double
__adddf3 (double a __attribute__ ((unused)),
	  double b __attribute__ ((unused)) )
{
  return  0.0;
}


float
__addsf3 (float a __attribute__ ((unused)),
	  float b __attribute__ ((unused)) )
{
  return  0.0;
}


long double
__addtf3 (long double a __attribute__ ((unused)),
	  long double b __attribute__ ((unused)) )
{
  return  0.0;
}


double
__divdf3 (double a __attribute__ ((unused)),
	  double b __attribute__ ((unused)) )
{
  return  0.0;
}


float
__divsf3 (float a __attribute__ ((unused)),
	  float b __attribute__ ((unused)) )
{
  return  0.0;
}


int
__divsi3 (int a __attribute__ ((unused)),
	  int b __attribute__ ((unused)) )
{
  return  0;
}


int
__mulsi3 (int a __attribute__ ((unused)),
	  int b __attribute__ ((unused)) )
{
  return  0;
}


long double
__divtf3 (long double a __attribute__ ((unused)),
	  long double b __attribute__ ((unused)) )
{
  return  0.0;
}


int
__eqdf2 (double a __attribute__ ((unused)),
	 double b __attribute__ ((unused)) )
{
  return  0;
}


int
__eqsf2 (float a __attribute__ ((unused)),
	 float b __attribute__ ((unused)) )
{
  return  0;
}


long double
__extenddftf2 (double a __attribute__ ((unused)) )
{
  return  0.0;
}


double
__extendsfdf2 (float a __attribute__ ((unused)) )
{
  return  0.0;
}


int
__fixdfsi (double a __attribute__ ((unused)) )
{
  return  0;
}


int
__fixsfsi (float a __attribute__ ((unused)) )
{
  return  0;
}


unsigned int
__fixunsdfsi (double a __attribute__ ((unused)) )
{
  return  0;
}


unsigned int
__fixunssfsi (float a __attribute__ ((unused)) )
{
  return  0;
}


double
__floatsidf (int i __attribute__ ((unused)) )
{
  return  0.0;
}


float
__floatsisf (int i __attribute__ ((unused)) )
{
  return  0.0;
}


double
__floatunsidf (unsigned int i __attribute__ ((unused)) )
{
  return  0.0;
}


float
__floatunsisf (unsigned int i __attribute__ ((unused)) )
{
  return  0.0;
}


int
__gedf2 (double a __attribute__ ((unused)),
	 double b __attribute__ ((unused)) )
{
  return  0;
}


int
__gesf2 (float a __attribute__ ((unused)),
	 float b __attribute__ ((unused)) )
{
  return  0;
}


int
__gtdf2 (double a __attribute__ ((unused)),
	 double b __attribute__ ((unused)) )
{
  return  0;
}


int
__gtsf2 (float a __attribute__ ((unused)),
	 float b __attribute__ ((unused)) )
{
  return  0;
}


int
__ledf2 (double a __attribute__ ((unused)),
	 double b __attribute__ ((unused)) )
{
  return  0;
}


int
__lesf2 (float a __attribute__ ((unused)),
	 float b __attribute__ ((unused)) )
{
  return  0;
}


int
__ltdf2 (double a __attribute__ ((unused)),
	 double b __attribute__ ((unused)) )
{
  return  0;
}


int
__ltsf2 (float a __attribute__ ((unused)),
	 float b __attribute__ ((unused)) )
{
  return  0;
}


int
__lttf2 (long double a __attribute__ ((unused)),
	 long double b __attribute__ ((unused)) )
{
  return  0;
}


double
__muldf3 (double a __attribute__ ((unused)),
	  double b __attribute__ ((unused)) )
{
  return  0.0;
}


float
__mulsf3 (float a __attribute__ ((unused)),
	  float b __attribute__ ((unused)) )
{
  return  0.0;
}


long double
__multf3 (long double a __attribute__ ((unused)),
	  long double b __attribute__ ((unused)) )
{
  return  0.0;
}


int
__nedf2 (double a __attribute__ ((unused)),
	 double b __attribute__ ((unused)) )
{
  return  0;
}


int
__nesf2 (float a __attribute__ ((unused)),
	 float b __attribute__ ((unused)) )
{
  return  0;
}


double
__subdf3 (double a __attribute__ ((unused)),
	  double b __attribute__ ((unused)) )
{
  return  0.0;
}


float
__subsf3 (float a __attribute__ ((unused)),
	  float b __attribute__ ((unused)) )
{
  return  0.0;
}


long double
__subtf3 (long double a __attribute__ ((unused)),
	  long double b __attribute__ ((unused)) )
{
  return  0.0;
}


float
__truncdfsf2 (double a __attribute__ ((unused)) )
{
  return  0.0;
}


double
__trunctfdf2 (long double a __attribute__ ((unused)) )
{
  return  0.0;
}


unsigned long
__udivdi3 (unsigned long a __attribute__ ((unused)),
	   unsigned long b __attribute__ ((unused)) )
{
  return  0.0;
}


unsigned long
__umoddi3 (unsigned long a __attribute__ ((unused)),
	   unsigned long b __attribute__ ((unused)) )
{
  return  0.0;
}


int
__unorddf2 (double a __attribute__ ((unused)),
	    double b __attribute__ ((unused)) )
{
  return  0;
}


int
__unordsf2 (float a __attribute__ ((unused)),
	    float b __attribute__ ((unused)) )
{
  return  0;
}


#endif	/* __arm__ */

#ifdef __riscv
void __riscv_save_0 () {}
void __riscv_save_1 () {}
void __riscv_save_2 () {}
void __riscv_save_3 () {}
void __riscv_save_4 () {}
void __riscv_save_5 () {}
void __riscv_save_6 () {}
void __riscv_save_7 () {}
void __riscv_save_8 () {}
void __riscv_save_9 () {}
void __riscv_save_10 () {}
void __riscv_save_11 () {}
void __riscv_save_12 () {}
void __riscv_restore_0 () {}
void __riscv_restore_1 () {}
void __riscv_restore_2 () {}
void __riscv_restore_3 () {}
void __riscv_restore_4 () {}
void __riscv_restore_5 () {}
void __riscv_restore_6 () {}
void __riscv_restore_7 () {}
void __riscv_restore_8 () {}
void __riscv_restore_9 () {}
void __riscv_restore_10 () {}
void __riscv_restore_11 () {}
void __riscv_restore_12 () {}
#endif

/*
   Local Variables:
   mode: C++
   c-file-style: "gnu"
   End:
*/
