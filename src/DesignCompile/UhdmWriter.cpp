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
#include "Testbench/ClassDefinition.h"
#include "Design/Design.h"
#include "UhdmWriter.h"
#include "uhdm.h"

using namespace SURELOG;
using namespace UHDM;

UhdmWriter::~UhdmWriter()
{
}

bool UhdmWriter::write(std::string uhdmFile) {
  Serializer s;
  if (m_design) {
    design* d = s.MakeDesign();
    std::string designName = "unnamed";
    auto topLevelModules = m_design->getTopLevelModuleInstances();
    for (auto inst : topLevelModules) {
      designName = inst->getModuleName();
      break;
    }
    d->VpiName(designName);
    // Modules
    auto modules = m_design->getModuleDefinitions();
    VectorOfmodule* v1 = s.MakeModuleVec();
    for (auto modNamePair : modules) {
      ModuleDefinition* mod = modNamePair.second;
      if (mod->getFileContents().size() && 
          mod->getType() == VObjectType::slModule_declaration) {
        FileContent* fC = mod->getFileContents()[0];
        module* m = s.MakeModule();
        m->VpiParent(d);
        m->VpiName(mod->getName());    
        m->VpiFile(fC->getFileName());
        m->VpiLineNo(fC->Line(mod->getNodeIds()[0]));
        v1->push_back(m);      
      }
    }
    d->AllModules(v1);
    
    // Packages
    auto packages = m_design->getPackageDefinitions();
    VectorOfpackage* v2 = s.MakePackageVec();
    for (auto packNamePair : packages) {
      Package* pack = packNamePair.second;
      if (pack->getFileContents().size() && 
          pack->getType() == VObjectType::slPackage_declaration) {
        FileContent* fC = pack->getFileContents()[0];
        package* p = s.MakePackage();
        p->VpiParent(d);
        p->VpiName(pack->getName());
        if (fC) {
          // Builtin package has no file 
          p->VpiFile(fC->getFileName());
          p->VpiLineNo(fC->Line(pack->getNodeIds()[0]));
        }
        v2->push_back(p);      
      }
    }
    d->AllPackages(v2);
    
    // Programs
    auto programs = m_design->getProgramDefinitions();
    VectorOfprogram* v3 = s.MakeProgramVec();
    for (auto progNamePair : programs) {
      Program* prog = progNamePair.second;
      if (prog->getFileContents().size() && 
          prog->getType() == VObjectType::slProgram_declaration) {
        FileContent* fC = prog->getFileContents()[0];
        program* p = s.MakeProgram();
        p->VpiParent(d);
        p->VpiName(prog->getName());    
        p->VpiFile(fC->getFileName());
        p->VpiLineNo(fC->Line(prog->getNodeIds()[0]));
        v3->push_back(p);      
      }
    }
    d->AllPrograms(v3);
    
    // Classes
    auto classes = m_design->getClassDefinitions();
    VectorOfclass_defn* v4 = s.MakeClass_defnVec();
    for (auto classNamePair : classes) {
      ClassDefinition* classDef = classNamePair.second;
      if (classDef->getFileContents().size() && 
          classDef->getType() == VObjectType::slClass_declaration) {
        FileContent* fC = classDef->getFileContents()[0];
        class_defn* c = s.MakeClass_defn();
        c->VpiParent(d);
        c->VpiName(classDef->getName());
        if (fC) {
          // Builtin classes have no file
          c->VpiFile(fC->getFileName());
          c->VpiLineNo(fC->Line(classDef->getNodeIds()[0]));
        }
        v4->push_back(c);      
      }
    }
    d->AllClasses(v4);
    
  }
  s.Save(uhdmFile);
  return true;
}
 
