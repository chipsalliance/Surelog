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
#include <map>

#include "SourceCompile/SymbolTable.h"
#include "Library/Library.h"
#include "Design/FileContent.h"
#include "ErrorReporting/Error.h"
#include "ErrorReporting/Location.h"
#include "ErrorReporting/Error.h"
#include "ErrorReporting/ErrorDefinition.h"
#include "ErrorReporting/ErrorContainer.h"
#include "SourceCompile/CompilationUnit.h"
#include "SourceCompile/PreprocessFile.h"
#include "SourceCompile/CompileSourceFile.h"
#include "CommandLine/CommandLineParser.h"
#include "SourceCompile/ParseFile.h"
#include "Testbench/ClassDefinition.h"
#include "SourceCompile/Compiler.h"
#include "DesignCompile/CompileDesign.h"
#include "DesignCompile/ResolveSymbols.h"
#include "DesignCompile/DesignElaboration.h"
#include "DesignCompile/UVMElaboration.h"
#include "DesignCompile/CompilePackage.h"
#include "DesignCompile/CompileModule.h"
#include "DesignCompile/CompileFileContent.h"
#include "DesignCompile/CompileProgram.h"
#include "DesignCompile/CompileClass.h"
#include "DesignCompile/Builtin.h"
#include "DesignCompile/PackageAndRootElaboration.h"
#include "surelog.h"
#include "UhdmWriter.h"
#include "uhdm.h"
#include "vpi_visitor.h"

using namespace SURELOG;
using namespace UHDM;

UhdmWriter::~UhdmWriter()
{
}

unsigned int getVpiDirection(VObjectType type)
{
  unsigned int direction = vpiInput;
  if (type == VObjectType::slPortDir_Inp)
    direction = vpiInput;
  else if (type == VObjectType::slPortDir_Out)
    direction = vpiOutput;
  else if (type == VObjectType::slPortDir_Inout)
    direction = vpiInout;
  return direction;
}

static std::map<ModPort*, modport*> modPortMap;
static std::map<DesignComponent*, BaseClass*> componentMap;
    
void writePorts(std::vector<Signal>& orig_ports, VectorOfport* dest_ports,
        Serializer& s) {
  for (auto& orig_port : orig_ports ) {
    port* dest_port = s.MakePort();
    dest_port->VpiName(orig_port.getName());
    unsigned int direction = getVpiDirection(orig_port.getDirection());
    dest_port->VpiDirection(direction);
    dest_port->VpiLineNo(orig_port.getFileContent()->Line(orig_port.getNodeId()));
    dest_port->VpiFile(orig_port.getFileContent()->getFileName());
    if (ModPort* orig_modport = orig_port.getModPort()) {
      ref_obj* ref = s.MakeRef_obj();
      dest_port->Low_conn(ref);
      std::map<ModPort*, modport*>::iterator itr = modPortMap.find(orig_modport);
      if (itr != modPortMap.end()) {
        ref->Actual_group((*itr).second);
      }
    } else if (ModuleDefinition* orig_interf = orig_port.getInterfaceDef()) {
      ref_obj* ref = s.MakeRef_obj();
      dest_port->Low_conn(ref);
      std::map<DesignComponent*, BaseClass*>::iterator itr = componentMap.find(orig_interf);
      if (itr != componentMap.end()) {
        ref->Actual_group((*itr).second);
      }
    }
    dest_ports->push_back(dest_port);
  }
}


void writeModule(ModuleDefinition* mod, module* m, Serializer& s) {
  // Ports
  std::vector<Signal>& orig_ports = mod->getPorts();
  VectorOfport* dest_ports = s.MakePortVec();
  writePorts(orig_ports, dest_ports, s);
  m->Ports(dest_ports);
}

void writeInterface(ModuleDefinition* mod, interface* m, Serializer& s) {
  // Ports
  std::vector<Signal>& orig_ports = mod->getPorts();
  VectorOfport* dest_ports = s.MakePortVec();
  writePorts(orig_ports, dest_ports, s);
  m->Ports(dest_ports);
  // Modports
  ModuleDefinition::ModPortSignalMap& orig_modports = mod->getModPortSignalMap();
  VectorOfmodport* dest_modports = s.MakeModportVec();
  for (auto& orig_modport : orig_modports ) {
    modport* dest_modport = s.MakeModport();
    modPortMap.insert(std::make_pair(&orig_modport.second, dest_modport));
    dest_modport->VpiName(orig_modport.first);
    VectorOfio_decl* ios = s.MakeIo_declVec();
    for (auto& sig : orig_modport.second.getPorts()) {
      io_decl* io = s.MakeIo_decl();
      io->VpiName(sig.getName());
      unsigned int direction = getVpiDirection(sig.getDirection());
      io->VpiDirection(direction);
      ios->push_back(io);
    }
    dest_modport->Io_decls(ios);
    dest_modports->push_back(dest_modport);
  }
  m->Modports(dest_modports);
}

void writeProgram(Program* mod, program* m, Serializer& s) {
  // Ports
  std::vector<Signal>& orig_ports = mod->getPorts();
  VectorOfport* dest_ports = s.MakePortVec();
  writePorts(orig_ports, dest_ports, s);
  m->Ports(dest_ports);
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
     
    // Packages
    auto packages = m_design->getPackageDefinitions();
    VectorOfpackage* v2 = s.MakePackageVec();
    for (auto packNamePair : packages) {
      Package* pack = packNamePair.second;
      if (pack->getFileContents().size() && 
          pack->getType() == VObjectType::slPackage_declaration) {
        FileContent* fC = pack->getFileContents()[0];
        package* p = s.MakePackage();
        componentMap.insert(std::make_pair(pack, p));
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
    VectorOfprogram* uhdm_programs = s.MakeProgramVec();
    for (auto progNamePair : programs) {
      Program* prog = progNamePair.second;
      if (prog->getFileContents().size() && 
          prog->getType() == VObjectType::slProgram_declaration) {
        FileContent* fC = prog->getFileContents()[0];
        program* p = s.MakeProgram();
        componentMap.insert(std::make_pair(prog, p)); 
        p->VpiParent(d);
        p->VpiName(prog->getName());    
        p->VpiFile(fC->getFileName());
        p->VpiLineNo(fC->Line(prog->getNodeIds()[0]));
        writeProgram(prog, p, s);
        uhdm_programs->push_back(p);      
      }
    }
    d->AllPrograms(uhdm_programs);
    
    // Classes
    auto classes = m_design->getClassDefinitions();
    VectorOfclass_defn* v4 = s.MakeClass_defnVec();
    for (auto classNamePair : classes) {
      ClassDefinition* classDef = classNamePair.second;
      if (classDef->getFileContents().size() && 
          classDef->getType() == VObjectType::slClass_declaration) {
        FileContent* fC = classDef->getFileContents()[0];
        class_defn* c = s.MakeClass_defn();
        componentMap.insert(std::make_pair(classDef, c));  
        DesignComponent* parent = classDef->getContainer();
        std::map<DesignComponent*, BaseClass*>::iterator itr = 
                componentMap.find(parent);
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

    // Interfaces
    auto modules = m_design->getModuleDefinitions();
    VectorOfinterface* uhdm_interfaces = s.MakeInterfaceVec();
    for (auto modNamePair : modules) {
      ModuleDefinition* mod = modNamePair.second;
      if (mod->getFileContents().size() == 0) {
        // Built-in primitive
      } else if (mod->getType() == VObjectType::slInterface_declaration) {
        FileContent* fC = mod->getFileContents()[0];
        interface* m = s.MakeInterface();
        componentMap.insert(std::make_pair(mod, m));
        m->VpiParent(d);
        m->VpiName(mod->getName());    
        m->VpiFile(fC->getFileName());
        m->VpiLineNo(fC->Line(mod->getNodeIds()[0]));
        uhdm_interfaces->push_back(m); 
        writeInterface(mod, m, s);
      }
    }
    d->AllInterfaces(uhdm_interfaces);
    
    // Modules
    VectorOfmodule* uhdm_modules = s.MakeModuleVec();
    for (auto modNamePair : modules) {
      ModuleDefinition* mod = modNamePair.second;
      if (mod->getFileContents().size() == 0) {
        // Built-in primitive
      } else if (mod->getType() == VObjectType::slModule_declaration) {
        FileContent* fC = mod->getFileContents()[0];
        module* m = s.MakeModule();
        componentMap.insert(std::make_pair(mod, m));
        m->VpiParent(d);
        m->VpiName(mod->getName());    
        m->VpiFile(fC->getFileName());
        m->VpiLineNo(fC->Line(mod->getNodeIds()[0]));
        uhdm_modules->push_back(m); 
        writeModule(mod, m, s);
      }
    }
    d->AllModules(uhdm_modules);
    
    // Repair parent relationship
    for (auto classNamePair : classes) {
      ClassDefinition* classDef = classNamePair.second;
      DesignComponent* parent = classDef->getContainer();
      std::map<DesignComponent*, BaseClass*>::iterator itr =
              componentMap.find(parent);
      if (itr != componentMap.end()) {
        std::map<DesignComponent*, BaseClass*>::iterator itr2 =
                componentMap.find(classDef);
        (*itr2).second->VpiParent((*itr).second);
      }
    }     
  }
  s.Save(uhdmFile);
  
  if (m_compiler->getCommandLineParser()->getDebugUhdm()) {
    std::cout << "====== UHDM =======\n";
    const std::vector<vpiHandle>& restoredDesigns = s.Restore(uhdmFile);
    std::string restored = visit_designs(restoredDesigns);
    std::cout << restored;
    std::cout << "===================\n";

  }
  
  return true;
}
 
