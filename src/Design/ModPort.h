/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   ModPort.h
 * Author: alain
 *
 * Created on January 31, 2020, 9:46 PM
 */
#include <vector>

#include "SourceCompile/SymbolTable.h"
#include "Signal.h"

#ifndef MODPORT_H
#define MODPORT_H
namespace SURELOG {

class ModuleDefinition;

class ModPort {
public:
  ModPort(ModuleDefinition* parent, const std::string& name) : m_parent(parent), m_name(name) {}
  virtual ~ModPort();
  const std::string& getName() { return m_name; } 
  void addSignal(Signal& sig) { m_ports.push_back(sig); }  
  std::vector<Signal>& getPorts() { return m_ports; }
  Signal* getPort(std::string& name);  
  ModuleDefinition* getParent () { return m_parent; }  
private:
  ModuleDefinition* m_parent;
  std::string m_name;  
  std::vector<Signal> m_ports;
};
};

#endif /* MODPORT_H */

