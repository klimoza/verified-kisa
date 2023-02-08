COQMODULE := printer
COQMFFLAGS := -R $(OPAM_SWITCH_PREFIX)/lib/coq-variant/VST_aarch64_64/VST VST

ALLVFILES := printer_files/compiled_format.v verified_printer/Format.v proof/*.v

build: Makefile.coq
	$(MAKE) -f Makefile.coq

clean::
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	$(RM) $(wildcard Makefile.coq Makefile.coq.conf _CoqProject) 

_CoqProject:
	(echo $(COQMFFLAGS); \
         echo "-R . $(COQMODULE)"; \
	echo $(ALLVFILES)) > _CoqProject

Makefile.coq: _CoqProject
	coq_makefile -o Makefile.coq -f _CoqProject

-include Makefile.coq

.PHONY: build clean
