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
 * FILE: ctl.h                                                               *
 * AUTHOR: Toni Schornboeck <schornboeck@c-plusplus.de>                      *
 *****************************************************************************
 * Das zentrale File der CTL                                                 *
 *****************************************************************************
 * Diese Datei darf frei unter der                                           *
 * GPL (http://www.gnu.org/copyleft/gpl.html) verwendet werden.              *
 *****************************************************************************/

#ifndef CTL_STANDARD_HEADER__
#define CTL_STANDARD_HEADER__
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>
#include <ctype.h>
#include <stdio.h>

#ifndef CTL_SIZE
#define	CTL_SIZE			100
#endif

#ifndef CTL_GROWFACTOR
#define CTL_GROWFACTOR		0.7
#endif

#ifdef	CTL_NORANGECHECK
#define	CTL_RANGE(x)		if(0)
#else
#define	CTL_RANGE(x)		if(x)
#endif

#define	CTL_OUT_OF_MEMORY	100
#define	CTL_WRONG_VALUE		101
#define	CTL_OUT_OF_RANGE	102
#define CTL_NOT_FOUND		103

struct CTL_STRUCT {
	size_t	BlockSize;
};
typedef struct CTL_STRUCT ctl_struct;

unsigned int ctl_errno;
unsigned int ctl_warning;

int ctl_SetBlockSize(ctl_struct* its, size_t BlockSize)
{
	if(BlockSize<1)
	{
		ctl_errno=CTL_WRONG_VALUE;
		return 1;
	}
	its->BlockSize=BlockSize;
	return 0;
}

#define CTL_GROW_ALLOC_SIZE(its) its->BlockSize=((size_t)(its->alloc+its->alloc*CTL_GROWFACTOR))

#endif
