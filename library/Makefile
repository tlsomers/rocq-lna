# Prefer `rocq makefile` when available, otherwise fall back to `coq_makefile`.
ROCQ := $(shell command -v rocq 2>nul || command -v rocq 2>/dev/null)
ifneq ($(ROCQ),)
MAKEFILE_TOOL := rocq makefile
else
MAKEFILE_TOOL := coq_makefile
endif

Makefile.coq:
	$(MAKEFILE_TOOL) -f _CoqProject -o Makefile.coq

# Forward most targets to Coq makefile (with some trick to make this phony)
%: Makefile.coq phony
	+@make -f Makefile.coq $@

clean: Makefile.coq
	+@make -f Makefile.coq clean

install: Makefile.coq
	+@make -f Makefile.coq install

all: Makefile.coq
	+@make -f Makefile.coq all
