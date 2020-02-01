/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/*
 * File:   PortNetHolder.h
 * Author: alain
 *
 * Created on January 30, 2020, 8:31 PM
 */

#include "Design/Signal.h"

#ifndef PORTNETHOLDER_H
#define PORTNETHOLDER_H
namespace SURELOG {

class PortNetHolder {
public:
    PortNetHolder(){}
    virtual ~PortNetHolder();

    std::vector<Signal>& getPorts()
    {
        return m_ports;
    }

    std::vector<Signal>& getSignals()
    {
        return m_signals;
    }

protected:
    std::vector<Signal> m_ports;
    std::vector<Signal> m_signals;
};
};

#endif /* PORTNETHOLDER_H */

