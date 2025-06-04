#ifndef SURELOG_SYMBOLID_H
#define SURELOG_SYMBOLID_H
#pragma once

#include <uhdm/SymbolId.h>

namespace SURELOG {

using uhdm::RawSymbolId;
using uhdm::SymbolId;
using uhdm::SymbolIdPP;

using uhdm::BadRawSymbolId;
using uhdm::BadRawSymbol;
using uhdm::BadSymbolId;

using uhdm::operator<<;

using uhdm::SymbolIdLessThanComparer;
using uhdm::SymbolIdHasher;
using uhdm::SymbolIdEqualityComparer;

using uhdm::SymbolIdSet;
using uhdm::SymbolIdUnorderedSet;
using uhdm::SymbolIdVector;

}  // namespace SURELOG

#endif  // SURELOG_SYMBOLID_H
