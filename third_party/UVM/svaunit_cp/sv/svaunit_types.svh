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
 * NAME:        svaunit_types.svh
 * PROJECT:     svaunit
 * Description: Types used in svaunit
 *******************************************************************************/

`ifndef SVAUNIT_TYPES_SVH
`define SVAUNIT_TYPES_SVH

// Definition of status type
typedef enum bit[1: 0] {SVAUNIT_FAIL = 0, SVAUNIT_PASS = 1, SVAUNIT_DID_NOT_RUN = 2} svaunit_status_type;

// Definition of status type - it is used for an SVA; corresponds to the fact that that SVA was tested or not
typedef enum bit {SVAUNIT_NOT_TESTED = 0, SVAUNIT_WAS_TESTED = 1} svaunit_sva_tested_type;

// Definition of state type
typedef enum int {
   SVAUNIT_IDLE = 0,
   SVAUNIT_START = `SVAUNIT_VPI_CB_ASSERTION_START,
   SVAUNIT_SUCCESS = `SVAUNIT_VPI_CB_ASSERTION_SUCCESS,
   SVAUNIT_FAILURE = `SVAUNIT_VPI_CB_ASSERTION_FAILURE,
   SVAUNIT_STEP_SUCCESS = `SVAUNIT_VPI_CB_ASSERTION_STEP_SUCCESS,
   SVAUNIT_STEP_FAILURE = `SVAUNIT_VPI_CB_ASSERTION_STEP_FAILURE,
   SVAUNIT_DISABLE = `SVAUNIT_VPI_CB_ASSERTION_DISABLE,
   SVAUNIT_ENABLE = `SVAUNIT_VPI_CB_ASSERTION_ENABLE,
   SVAUNIT_RESET = `SVAUNIT_VPI_CB_ASSERTION_RESET,
   SVAUNIT_KILL = `SVAUNIT_VPI_CB_ASSERTION_KILL
} svaunit_concurrent_assertion_state_type;

`endif
