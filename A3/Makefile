.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
ifeq ($(wildcard Makefile.coq),)
	coq_makefile -f _CoqProject -o Makefile.coq
else
endif

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf
