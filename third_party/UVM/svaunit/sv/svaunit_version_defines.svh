/******************************************************************************
 * (C) Copyright 2015 AMIQ Consulting
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * NAME:        svaunit_version_defines.svh
 * PROJECT:     svaunit
 * Description: Macros used in project
 *******************************************************************************/

`ifndef SVAUNIT_VERSION_DEFINES_SVH
`define SVAUNIT_VERSION_DEFINES_SVH

// Version numbers to be used in creating version strings for printing
// or programmatic testing against version numbers
`define SVAUNIT_NAME SVAUNIT
`define SVAUNIT_MAJOR_REV 3
`define SVAUNIT_MINOR_REV 2

// SVAUNIT_VERSION_STRING print as "SVAUNIT - M.m"
`define SVAUNIT_VERSION_STRING `"`SVAUNIT_NAME``-```SVAUNIT_MAJOR_REV``.```SVAUNIT_MINOR_REV`"

`endif
