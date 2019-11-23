
SLregisterNewErrorType("[WARN :PY0099]", "Instance \"%s\"", "");
SLoverrideSeverity("[WARN :PY0099]", "WARNING")

def recurseInstance(errors, design, instance):
    mod = SLgetInstanceDefinition(instance)
    print (SLgetInstanceName(instance), SLgetModuleName(mod))
    SLaddError(errors, "[WARN :PY0099]", SLgetInstanceFileName(instance), SLgetInstanceLine(instance), 0, SLgetInstanceName(instance))  
    nbdefs = SLgetnInstanceChildren(instance)
    for i in range(nbdefs):
        subinstance = SLgetInstanceChildren(instance,i)
        recurseInstance(errors, design, subinstance)


def slUserCallbackPerDesign (errors, design):

    nbdefs = SLgetnModuleDefinition(design)
    print (nbdefs)
    for i in range(nbdefs):
        mod = SLgetModuleDefinition(design, i)
        print (SLgetModuleName(mod), SLgetModuleFile(mod), SLgetModuleLine(mod))
        set = SLcollectAll(SLgetModuleFileContent(mod), SLgetModuleRootNode(mod), slModule_item, False)
        print (" ", set)

    nbdefs = SLgetnClassDefinition(design)
    print (nbdefs)   
    for i in range(nbdefs):
        mod = SLgetClassDefinition(design, i)
        print (SLgetClassName(mod), SLgetClassFile(mod), SLgetClassLine(mod), SLgetClassRootNode(mod))

    nbdefs = SLgetnTopModuleInstance(design)
    print (nbdefs)    
    for i in range(nbdefs):
        instance = SLgetTopModuleInstance(design,i)
        recurseInstance(errors, design, instance)
