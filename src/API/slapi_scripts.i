/* File: slapi_scripts.i */
%module slapi
%include "typemaps.i"
%include "std_string.i"
%include "std_vector.i"

%{
#include <Surelog/Common/SymbolId.h>
using SURELOG::RawNodeId;

#include <Surelog/SourceCompile/VObjectTypes.h>
using SURELOG::VObjectType;
%}

%template (UIntVector) std::vector<uint32_t>;
        
%include <Surelog/API/SLAPI.h>

