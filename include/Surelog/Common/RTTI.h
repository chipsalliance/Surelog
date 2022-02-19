#ifndef SURELOG_RTTI_H
#define SURELOG_RTTI_H

#pragma once

#include <uhdm/RTTI.h>

namespace SURELOG {
using RTTI = UHDM::RTTI;
}

#define SURELOG_IMPLEMENT_RTTI(classType, baseType) \
  UHDM_IMPLEMENT_RTTI(classType, baseType)
#define SURELOG_IMPLEMENT_RTTI_2_BASES(classType, baseType1, baseType2) \
  UHDM_IMPLEMENT_RTTI_2_BASES(classType, baseType1, baseType2)
#define SURELOG_IMPLEMENT_RTTI_CAST_FUNCTIONS(fname, baseType) \
  UHDM_IMPLEMENT_RTTI_CAST_FUNCTIONS(fname, baseType)
#define SURELOG_IMPLEMENT_RTTI_VIRTUAL_CAST_FUNCTIONS(fname, baseType) \
  UHDM_IMPLEMENT_RTTI_VIRTUAL_CAST_FUNCTIONS(fname, baseType)

#endif  /// SURELOG_RTTI_H
