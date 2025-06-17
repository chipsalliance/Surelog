#ifndef SURELOG_SYMBOLID_H
#define SURELOG_SYMBOLID_H
#pragma once

#include <uhdm/SymbolId.h>

namespace SURELOG {

using uhdm::RawSymbolId;
using uhdm::SymbolId;
using uhdm::SymbolIdPP;

using uhdm::BadRawSymbol;
using uhdm::BadRawSymbolId;
using uhdm::BadSymbolId;

using uhdm::operator<<;

using uhdm::SymbolIdEqualityComparer;
using uhdm::SymbolIdHasher;
using uhdm::SymbolIdLessThanComparer;

using uhdm::SymbolIdSet;
using uhdm::SymbolIdUnorderedSet;
using uhdm::SymbolIdVector;

}  // namespace SURELOG

#endif  // SURELOG_SYMBOLID_H
