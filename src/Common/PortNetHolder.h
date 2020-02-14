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

namespace UHDM {
class cont_assign;
};

namespace SURELOG {

class PortNetHolder {
public:
    PortNetHolder() : m_contAssigns(NULL) {}
    virtual ~PortNetHolder();

    std::vector<Signal*>& getPorts()
    {
        return m_ports;
    }

    std::vector<Signal*>& getSignals()
    {
        return m_signals;
    }

    std::vector<UHDM::cont_assign*>* getContAssigns()
    {
        return m_contAssigns;
    }

    void setContAssigns(std::vector<UHDM::cont_assign*>* cont_assigns)
    {
        m_contAssigns = cont_assigns;
    }

protected:
    std::vector<Signal*> m_ports;
    std::vector<Signal*> m_signals;
    std::vector<UHDM::cont_assign*>* m_contAssigns;
};
};

#endif /* PORTNETHOLDER_H */

