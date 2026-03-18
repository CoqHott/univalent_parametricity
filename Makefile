all: Makefile.coq
	$(MAKE) -f Makefile.coq

install: all
	$(MAKE) -f Makefile.coq install

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq

Makefile.coq: _CoqProject
	$(COQBIN)rocq makefile -f _CoqProject -o Makefile.coq
