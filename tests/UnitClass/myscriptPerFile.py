import slapi


SLregisterNewErrorType("[WARN :PY0100]", "Module Item \"%s\"", "");
SLoverrideSeverity("[WARN :PY0100]", "WARNING")


def slUserCallbackPerFile (errors, fileContent):
    root = SLgetRootNode (fileContent)
    print (SLgetFile (fileContent, root))
    #print (SLgetName (fileContent, root))
    print (SLgetLine (fileContent, root))
    print (SLgetChild (fileContent, root))
    type = SLgetType (fileContent, root)
    print ("Type:", type)
    print (type == slSource_text)
    print (type == slModule_declaration)
    set = SLcollectAll(fileContent, root, slModule_item, False)
    SLaddError(errors, "[WARN :PY0100]", SLgetFileName(fileContent), SLgetLine(fileContent, root), 0, SLgetName(fileContent, root))  

   
