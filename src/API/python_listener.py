# Sample listener

SLregisterNewErrorType("[NOTE :PY0403]", "Module declaration \"%s\"", "");
SLoverrideSeverity("[NOTE :PY0403]", "INFO")

def enterModule_nonansi_header(prog, ctx):
	SLaddErrorContext(prog, ctx, "[INFO :PY0403]", SLgetText(prog, ctx)) 

def enterModule_ansi_header(prog, ctx):
	SLaddErrorContext(prog, ctx, "[INFO :PY0403]", SLgetText(prog, ctx)) 
