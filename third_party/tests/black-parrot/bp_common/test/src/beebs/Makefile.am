# Top level Makefile.am for building a BEEBS benchmark
#
# Copyright (C) 2013 Embecosm Limited and University of Bristol
# Copyright (C) 2018 Embecosm Limited
#
# Contributor: James Pallister <james.pallister@bristol.ac.uk>
# Contributor: Jeremy Bennett <jeremy.bennett@embecosm.com>
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
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.

# SPDX-License-Identifier: GPL-3.0-or-later

ACLOCAL_AMFLAGS = -I m4

SUBDIRS = doc support src testsuite

EXTRA_DIST= config

# Clean up any test results
distclean-local:
	-rm -fr results/
