#ifndef SURELOG_CONTAINERS_H
#define SURELOG_CONTAINERS_H
#pragma once

#include <cstdint>
#include <functional>
#include <map>
#include <string>
#include <vector>

namespace SURELOG {

class ClassDefinition;
class ModuleDefinition;
class Package;
class Program;
class MacroInfo;

typedef std::map<std::string, ModuleDefinition*> ModuleNameModuleDefinitionMap;
typedef std::multimap<std::string, Package*, std::less<>>
    PackageNamePackageDefinitionMultiMap;
typedef std::vector<Package*> PackageDefinitionVec;
typedef std::map<std::string, Program*, std::less<>>
    ProgramNameProgramDefinitionMap;

typedef std::multimap<std::string, ClassDefinition*, std::less<>>
    ClassNameClassDefinitionMultiMap;
typedef std::map<std::string, ClassDefinition*> ClassNameClassDefinitionMap;

typedef std::map<std::string, MacroInfo*, std::less<>> MacroStorage;
typedef std::map<std::string, MacroInfo*, std::less<>> MacroStorageRef;

}  // namespace SURELOG

#endif  // SURELOG_CONTAINERS_H
