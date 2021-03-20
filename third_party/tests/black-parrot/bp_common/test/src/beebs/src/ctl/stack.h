/* This file is part of the Bristol/Embecosm Embedded Benchmark Suite.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program. If not, see <http://www.gnu.org/licenses/>. */

/*****************************************************************************
 * FILE: stack.h                                                             *
 * AUTHOR: Toni Schornboeck <schornboeck@c-plusplus.de>                      *
 *****************************************************************************
 * Implementierung eines FixedSize Stack fuer die CTL                        *
 *****************************************************************************
 * Diese Datei darf frei unter der                                           *
 * GPL (http://www.gnu.org/copyleft/gpl.html) verwendet werden.              *
 *****************************************************************************/

#include "ctl.h"

#define MAKE_STACK(type)							\
struct CTL_##type##STACK {							\
	type*	value;									\
	size_t	size;									\
	size_t	first;									\
	size_t	alloc;									\
};													\
													\
typedef struct CTL_##type##STACK ctl_##type##Stack;	\
													\
ctl_##type##Stack* ctl_##type##StackInitSize(int BlockSize)\
{													\
	ctl_##type##Stack* s=malloc_beebs(sizeof(ctl_##type##Stack));\
	if(!s)											\
	{												\
		return NULL;								\
	}												\
	s->alloc		= BlockSize;					\
	s->value		= malloc_beebs(BlockSize*sizeof(type));\
	if(!s->value)									\
	{												\
		return NULL;								\
	}												\
	s->first		= 0;							\
	s->size			= 0;							\
	return s;										\
}													\
													\
ctl_##type##Stack* ctl_##type##StackInit(void)		\
{													\
	return ctl_##type##StackInitSize(CTL_SIZE);		\
}													\
													\
ctl_##type##Stack* ctl_##type##StackInitCopy(ctl_##type##Stack* stack)\
{													\
	ctl_##type##Stack* s=malloc_beebs(sizeof(ctl_##type##Stack));\
	if(!s)											\
	{												\
		return NULL;								\
	}												\
	s->alloc		= stack->alloc;					\
	s->value		= malloc_beebs(stack->alloc*sizeof(type));\
	if(!s->value)									\
	{												\
		return NULL;								\
	}												\
	s->first		= stack->first;					\
	s->size			= stack->size;					\
	return s;										\
}													\
													\
void ctl_##type##StackFree(ctl_##type##Stack* s)	\
{													\
	free_beebs(s->value);									\
	free_beebs(s);										\
}													\
													\
int ctl_##type##StackPush(ctl_##type##Stack* s, type value)\
{													\
	if(++s->size>s->alloc)							\
	{												\
		s->size=s->alloc;							\
	}												\
	if(++s->first==s->size)							\
	{												\
		s->first=0;									\
	}												\
	s->value[s->first]=value;						\
	return 0;										\
}													\
													\
int ctl_##type##StackPop(ctl_##type##Stack* s, type* value)\
{													\
	if(s->size==0)									\
	{												\
		ctl_errno=CTL_OUT_OF_RANGE;					\
		return 1;									\
	}												\
													\
	if(value)*value=s->value[s->first];				\
	--s->size;										\
	if(s->size)										\
	{												\
		if(!s->first)								\
		{											\
			s->first=s->size-1;						\
			return 0;								\
		}											\
		--s->first;									\
	}												\
	return 0;										\
}

