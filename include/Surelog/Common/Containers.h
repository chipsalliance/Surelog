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

using ModuleNameModuleDefinitionMap =
    std::map<std::string, ModuleDefinition *, StringViewCompare>;
using PackageNamePackageDefinitionMultiMap =
    std::multimap<std::string, Package *, StringViewCompare>;
using PackageDefinitionVec = std::vector<Package *>;
using ProgramNameProgramDefinitionMap =
    std::map<std::string, Program *, StringViewCompare>;

using ClassNameClassDefinitionMultiMap =
    std::multimap<std::string, ClassDefinition *, StringViewCompare>;
using ClassNameClassDefinitionMap =
    std::map<std::string, ClassDefinition *, StringViewCompare>;

using MacroStorage =
    std::map<std::string, std::vector<MacroInfo *>, StringViewCompare>;
using MacroStorageRef =
    std::map<std::string, std::vector<MacroInfo *>, StringViewCompare>;

}  // namespace SURELOG

#endif  // SURELOG_CONTAINERS_H
