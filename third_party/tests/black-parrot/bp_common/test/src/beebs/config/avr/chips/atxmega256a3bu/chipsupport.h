/* Chip support for AVR atxmega256a3bu.

   Copyright (C) 2014 Embecosm Limited and the University of Bristol

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

#ifndef CHIPSUPPORT_H
#define CHIPSUPPORT_H

#define PIN_INIT(port, number)                  \
  PORT ## port . OUTCLR |= (1 << number);       \
  PORT ## port . DIRSET |= (1 << number);

#define PIN_SET(port, number)                   \
  PORT ## port . OUTSET |= (1 << number);

#define PIN_CLEAR(port, number)                 \
  PORT ## port . OUTCLR |= (1 << number);

#endif
