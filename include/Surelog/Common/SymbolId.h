#ifndef SURELOG_SYMBOLID_H
#define SURELOG_SYMBOLID_H
#pragma once

#include <uhdm/SymbolId.h>

namespace SURELOG {

using UHDM::RawSymbolId;
using UHDM::SymbolId;
using UHDM::SymbolIdPP;

using UHDM::BadRawSymbol;
using UHDM::BadRawSymbolId;
using UHDM::BadSymbolId;

using UHDM::operator<<;

using UHDM::SymbolIdEqualityComparer;
using UHDM::SymbolIdHasher;
using UHDM::SymbolIdLessThanComparer;

using UHDM::SymbolIdSet;
using UHDM::SymbolIdUnorderedSet;
using UHDM::SymbolIdVector;

}  // namespace SURELOG

#endif  // SURELOG_SYMBOLID_H
