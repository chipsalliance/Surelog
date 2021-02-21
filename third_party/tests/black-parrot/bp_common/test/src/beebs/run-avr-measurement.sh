#!/bin/sh

# BEEBS Top Level Run script for AVR
# Copyright (C) 2014 Embecosm Limited

# Contributor Simon Cook <simon.cook@embecosm.com>
# Contributor Pierre Langlois <pierre.langlois@embecosm.com>

# This file is part of BEEBS

# This program is free software: you can redistribute it and/or modify it
# under the terms of the GNU Lesser General Public License as published by the
# Free Software Foundation, either version 3 of the License, or (at your
# option) any later version.

# This program is distributed in the hope that it will be useful, but WITHOUT
# ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
# FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Lesser General Public License
# for more details.

# You should have received a copy of the GNU Lesser General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.

# The arguments have the following meaning.

# Invocation Syntax

#     run-avr-measurement.sh [--target-board <board>]

# --target-board <board>
# --avrdude <program>
# --avrdude-flags <val>
# --energytool-serial <val>
# --energytool-pin <val>
# --energytool-point <val>
# --energy-data <file>
# --timeout <val>

# Default values for testing, overriden by their respective options.
AVRDUDE="/opt/avrdude/bin/avrdude"
AVRDUDE_FLAGS="-carduino -patmega328p -C /opt/avrdude/etc/avrdude.conf -P/dev/ttyUSB0 -D"

ENERGYTOOL_SERIAL="EE00"
ENERGYTOOL_PIN="PA1"
ENERGYTOOL_POINT=3

REPEAT_FACTOR=1

TARGET_BOARD=avr-avrdude

ENERGY_DATA="energy.csv"

TIMEOUT=120

# Parse options
until
opt=$1
case ${opt} in
  --target-board)
    shift
    TARGET_BOARD=$1
    ;;

  --mcu)
    shift
    AVR_MCU="$1"
    ;;

  --avrdude)
    shift
    AVRDUDE="$1"
    ;;

  --avrdude-flags)
    shift
    AVRDUDE_FLAGS="$1"
    ;;

  --energytool-serial)
    shift
    ENERGYTOOL_SERIAL="$1"
    ;;

  --energytool-pin)
    shift
    ENERGYTOOL_PIN="$1"
    ;;

  --energytool-point)
    shift
    ENERGYTOOL_POINT="$1"
    ;;

  --energy-data)
    shift
    ENERGY_DATA="$1"
    ;;

  --timeout)
    shift
    TIMEOUT="$1"
    ;;

  ?*)
    echo "Usage: ./run-avr-measurement.sh [--target-board <board>]"
    echo "                                [--avrdude <program>]"
    echo "                                [--avrdude-flags <val>]"
    echo "                                [--energytool-serial <val>]"
    echo "                                [--energytool-pin <val>]"
    echo "                                [--energytool-point <val>]"
    echo "                                [--energy-data <file>]"
    echo "                                [--timeout <val>]"

    exit 1
    ;;
  *)
    ;;
esac
[ "x${opt}" = "x" ]
do
    shift
done

export AVRDUDE
export AVRDUDE_FLAGS

export ENERGYTOOL_SERIAL
export ENERGYTOOL_PIN
export ENERGYTOOL_POINT

export ENERGY_DATA

export TIMEOUT

make RUNTESTFLAGS="--target_board=${TARGET_BOARD} measure.exp" check
