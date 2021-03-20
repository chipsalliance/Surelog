#!/usr/bin/env python2

# Copyright (C) 2014 Embecosm Limited and University of Bristol
#
# Contributor James Pallister <james.pallister@bristol.ac.uk>
#
# This file is part of the Bristol/Embecosm Embedded Benchmark Suite.
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program. If not, see <http://www.gnu.org/licenses/>.

import pyenergy
import sys
from time import sleep

if len(sys.argv) is not 4:
  sys.stderr.write("Usage: energytool.py SERIAL POINT PIN")
  sys.exit(1)

serial_port = sys.argv[1]
trigger_pin = sys.argv[3]

try:
  measurement_point = int(sys.argv[2])
except ValueError:
  sys.exit(1)

try:
  em = pyenergy.EnergyMonitor(serial_port)
  em.connect()

  em.enableMeasurementPoint(measurement_point)
  em.setTrigger(trigger_pin, measurement_point)
except RuntimeError:
  sys.exit(1)


while not em.measurementCompleted():
  sleep(0.1)

m = em.getMeasurement(measurement_point)

# Print out the measurement using csv.
print "{:f},{:f},{:f},{:f},{:f}".format(m.energy, m.time, m.avg_power, m.avg_current, m.avg_voltage)
