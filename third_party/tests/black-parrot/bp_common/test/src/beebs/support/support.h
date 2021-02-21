/* Copyright (C) 2014 Embecosm Limited and the University of Bristol

   Contributor James Pallister <james.pallister@bristol.ac.uk>

   This file is part of BEEBS

   This program is free software; you can redistribute it and/or modify it
   under the terms of the GNU General Public License as published by the Free
   Software Foundation; either version 3 of the License, or (at your option)
   any later version.

   This program is distributed in the hope that it will be useful, but WITHOUT
   ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
   FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
   more details.

   You should have received a copy of the GNU General Public License along with
   this program.  If not, see <http://www.gnu.org/licenses/>.  */

#ifndef SUPPORT_H
#define SUPPORT_H

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

/* Include board support header if we have one */

#ifdef HAVE_BOARDSUPPORT_H
#include "boardsupport.h"
#endif

/* Board repeat factor may be set in the board support header, if not, we
   define a default */
//By default was 4096
#ifndef BOARD_REPEAT_FACTOR
#define BOARD_REPEAT_FACTOR 2
#endif

/* Include chip support header if we have one */

#ifdef HAVE_CHIPSUPPORT_H
#include "chipsupport.h"
#endif

/* Scaling factors may defined when compiling benchmarks. If not we set it to
   zero, which means no scaling and then leads to the REPEAT_FACTOR for the
   program. */

#ifndef CALIB_SCALE
#define CALIB_SCALE 0
#endif

// The overall repeat factor is scaled by the command-line given
// CALIB_SCALE.

#define REPEAT_FACTOR (((CALIB_SCALE) > 0)                         \
                       ? (BOARD_REPEAT_FACTOR) >> (CALIB_SCALE)    \
		       : (BOARD_REPEAT_FACTOR) << (-CALIB_SCALE))

/* Benchmarks must implement verify_benchmark, which must return -1 if no
   verification is done. */

int verify_benchmark (int result);

/* Standard functions implemented for each board */

void initialise_board (void);
void start_trigger (void);
void stop_trigger (void);

/* Every benchmark implements this as its entry point. Don't allow it to be
   inlined! */

int benchmark (void) __attribute__ ((noinline));

#endif	/* SUPPORT_H */

/*
   Local Variables:
   mode: C++
   c-file-style: "gnu"
   End:
*/
