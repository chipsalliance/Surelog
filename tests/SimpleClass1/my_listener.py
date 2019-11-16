# Sample listener used to test release tar file, used by release.tcl

SLregisterNewErrorType("[WARN :PY0403]", "Module declaration \"%s\"", "");
SLoverrideSeverity("[WARN :PY0403]", "WARNING")

def enterModule_nonansi_header(prog, ctx):
	SLaddErrorContext(prog, ctx, "[WARN :PY0403]", SLgetText(prog, ctx)) 

def enterModule_ansi_header(prog, ctx):
	SLaddErrorContext(prog, ctx, "[WARN :PY0403]", SLgetText(prog, ctx)) 
