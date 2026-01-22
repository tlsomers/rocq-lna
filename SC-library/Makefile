# Prefer `rocq makefile` when available, otherwise fall back to `coq_makefile`.
ROCQ := $(shell command -v rocq 2>nul || command -v rocq 2>/dev/null)
ifneq ($(ROCQ),)
MAKEFILE_TOOL := rocq makefile
else
MAKEFILE_TOOL := coq_makefile
endif

# This Makefile is a copy of the makefile created for the course Program Verification,
# which is located in a private repository.

# Forward most targets to Coq makefile (with some trick to make this phony)
%: Makefile.coq phony
	+@make -f Makefile.coq $@

all: Makefile.coq
	+@make -f Makefile.coq all
.PHONY: all

clean: Makefile.coq
	+@make -f Makefile.coq clean
	rm -f Makefile.coq
	rm -f Makefile.coq.conf
.PHONY: clean

Makefile.coq:
	$(MAKEFILE_TOOL) -f _CoqProject -o Makefile.coq

# Some files that do *not* need to be forwarded to Makefile.coq
Makefile: ;
_CoqProject: ;

# Phony wildcard targets
phony: ;
.PHONY: phony