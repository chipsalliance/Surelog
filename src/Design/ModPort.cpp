/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   ModPort.cpp
 * Author: alain
 * 
 * Created on January 31, 2020, 9:46 PM
 */
#include "SourceCompile/SymbolTable.h"
#include "Signal.h"
#include "ModPort.h"

using namespace SURELOG;

ModPort::~ModPort()
{
}

Signal* ModPort::getPort(std::string& name) {
  for (Signal& sig : m_ports) {
    if (sig.getName() == name) {
      return &sig;
    }
  }
  return NULL;
}  