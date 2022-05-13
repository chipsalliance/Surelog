/* File: slapi_scripts.i */
%module slapi
%include "typemaps.i"
%include "std_string.i"
%include "std_vector.i"

%{
#include <Surelog/Common/SymbolId.h>
using SURELOG::RawNodeId;
%}

%template (UIntVector) std::vector<unsigned int>;
        
%include <Surelog/API/SLAPI.h>

