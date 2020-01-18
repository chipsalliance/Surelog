/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   UhdmWriter.cpp
 * Author: alain
 * 
 * Created on January 17, 2020, 9:13 PM
 */
#include "Design/Design.h"
#include "UhdmWriter.h"
#include "uhdm.h"

using namespace SURELOG;
using namespace UHDM;

UhdmWriter::~UhdmWriter()
{
}

bool UhdmWriter::write(std::string uhdmFile) {
  Serializer::purge();
  if (m_design) {
    design* d = designFactory::make();
    std::string designName = "unnamed";
    auto topLevelModules = m_design->getTopLevelModuleInstances();
    for (auto inst : topLevelModules) {
      designName = inst->getModuleName();
      break;
    }
    d->set_vpiName(designName);
    auto modules = m_design->getModuleDefinitions();
    VectorOfmodule* v1 = VectorOfmoduleFactory::make();
    for (auto modNamePair : modules) {
      ModuleDefinition* mod = modNamePair.second;
      if (mod->getFileContents().size() && 
          mod->getType() == VObjectType::slModule_declaration) {
        FileContent* fC = mod->getFileContents()[0];
        module* m = moduleFactory::make();
        m->set_vpiParent(d);
        m->set_uhdmParentType(uhdmdesign);
        m->set_vpiName(mod->getName());    
        m->set_vpiFile(fC->getFileName());
        m->set_vpiLineNo(fC->Line(mod->getNodeIds()[0]));
        v1->push_back(m);      
      }
    }
    d->set_allModules(v1);
  }
  Serializer::save(uhdmFile);
  return true;
}
 