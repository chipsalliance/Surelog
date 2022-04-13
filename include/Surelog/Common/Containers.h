#ifndef SURELOG_CONTAINERS_H
#define SURELOG_CONTAINERS_H
#pragma once

#include <cstdint>
#include <map>
#include <string>
#include <string_view>
#include <vector>

namespace SURELOG {

struct StringViewCompare {
  using is_transparent = void;

  constexpr bool operator()(std::string_view a, std::string_view b) const {
    return a < b;
  }
};

class ClassDefinition;
class ModuleDefinition;
class Package;
class Program;
class MacroInfo;

typedef std::map<std::string, ModuleDefinition*> ModuleNameModuleDefinitionMap;
typedef std::multimap<std::string, Package*, StringViewCompare>
    PackageNamePackageDefinitionMultiMap;
typedef std::vector<Package*> PackageDefinitionVec;
typedef std::map<std::string, Program*, StringViewCompare>
    ProgramNameProgramDefinitionMap;

typedef std::multimap<std::string, ClassDefinition*, StringViewCompare>
    ClassNameClassDefinitionMultiMap;
typedef std::map<std::string, ClassDefinition*> ClassNameClassDefinitionMap;

typedef std::map<std::string, MacroInfo*, StringViewCompare> MacroStorage;
typedef std::map<std::string, MacroInfo*, StringViewCompare> MacroStorageRef;

}  // namespace SURELOG

#endif  // SURELOG_CONTAINERS_H
