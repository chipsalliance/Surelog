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
#include "headers/uhdm_forward_decl.h"

#ifndef PORTNETHOLDER_H
#define PORTNETHOLDER_H

namespace SURELOG {

class PortNetHolder {
public:
    PortNetHolder() : m_contAssigns(NULL), m_processes(NULL), 
                      m_parameters(NULL), m_param_assigns(NULL), m_task_funcs(NULL) {}
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
    
    std::vector<UHDM::process_stmt*>* getProcesses()
    {
        return m_processes;
    }

    void setProcesses(std::vector<UHDM::process_stmt*>* processes)
    {
        m_processes = processes;
    }

    std::vector<UHDM::parameters*>* getParameters()
    {
        return m_parameters;
    }

    void setParameters(std::vector<UHDM::parameters*>* parameters)
    {
        m_parameters = parameters;
    }

    std::vector<UHDM::param_assign*>* getParam_assigns()
    {
        return m_param_assigns;
    }

    void setParam_assigns(std::vector<UHDM::param_assign*>* param_assigns)
    {
        m_param_assigns = param_assigns;
    }

    std::vector<UHDM::task_func*>* getTask_funcs()
    {
        return m_task_funcs;
    }

    void setTask_funcs(std::vector<UHDM::task_func*>* task_funcs)
    {
        m_task_funcs = task_funcs;
    }

protected:
    std::vector<Signal*> m_ports;
    std::vector<Signal*> m_signals;
    std::vector<UHDM::cont_assign*>* m_contAssigns;
    std::vector<UHDM::process_stmt*>* m_processes;
    std::vector<UHDM::parameters*>* m_parameters;
    std::vector<UHDM::param_assign*>* m_param_assigns;
    std::vector<UHDM::task_func*>* m_task_funcs;
};
};

#endif /* PORTNETHOLDER_H */

