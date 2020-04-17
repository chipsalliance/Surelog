/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   UhdmWriter.h
 * Author: alain
 *
 * Created on January 17, 2020, 9:12 PM
 */

#ifndef UHDMWRITER_H
#define UHDMWRITER_H

#include <string>

namespace SURELOG {

class UhdmWriter {
public:
    UhdmWriter(CompileDesign* compiler, Design* design) : m_compileDesign(compiler), m_design(design) {}
    vpiHandle write(std::string uhdmFile);
    virtual ~UhdmWriter();

    static unsigned int getVpiDirection(VObjectType type);

    static unsigned int getVpiNetType(VObjectType type);

    static unsigned int getVpiOpType(VObjectType type);
    
private:
    CompileDesign* m_compileDesign;
    Design* m_design;
    
};

};

#endif /* UHDMWRITER_H */

