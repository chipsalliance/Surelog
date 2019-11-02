/******************************************************************************
 * (C) Copyright 2014 AMIQ Consulting
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
 * NAME:        amiq_eth_ve_top.cpp
 * PROJECT:     amiq_eth
 * Description: This file instantiate all the necessary C classes and connects
 * 				the C ports to the System-Verilog ports
 *******************************************************************************/

#ifndef __AMIQ_ETH_VE_TOP_CPP
//protection against multiple includes
#define __AMIQ_ETH_VE_TOP_CPP

#include "uvmc.h"
#include "amiq_eth_ve_consumer.cpp"
#include "amiq_eth_ve_producer.cpp"

using namespace uvmc;

int sc_main(int argc, char* argv[])
{
	amiq_eth_ve_consumer consumer("consumer");
	amiq_eth_ve_producer producer("producer");

	consumer.out_sc2sc.bind(producer);

	uvmc_connect(consumer.in,"sv2sc_connection");
	uvmc_connect(producer.out,"sc2sv_connection");
  sc_start();
  return 0;
}

#endif
