# Sample listener used to test release tar file, used by release.tcl

SLregisterNewErrorType("[ERR  :PY0405]", "Module declaration \"%s\"", "");
SLoverrideSeverity("[ERR  :PY0405]", "ERROR")

def enterModule_nonansi_header(prog, ctx):
	SLaddErrorContext(prog, ctx, "[ERR  :PY0405]", SLgetText(prog, ctx)) 

def enterModule_ansi_header(prog, ctx):
	SLaddErrorContext(prog, ctx, "[ERR  :PY0405]", SLgetText(prog, ctx)) 
