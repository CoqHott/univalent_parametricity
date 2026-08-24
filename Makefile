all: Makefile.coq
	$(MAKE) -f Makefile.coq

mathcomp: Makefile.mathcomp.coq
	$(MAKE) -f Makefile.mathcomp.coq

install: all
	$(MAKE) -f Makefile.coq install

install-mathcomp: mathcomp
	$(MAKE) -f Makefile.mathcomp.coq install

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq

clean-mathcomp: Makefile.mathcomp.coq
	$(MAKE) -f Makefile.mathcomp.coq clean
	rm -f Makefile.mathcomp.coq

Makefile.coq: _CoqProject
	$(COQBIN)rocq makefile -f _CoqProject -o Makefile.coq

Makefile.mathcomp.coq: _CoqProject.mathcomp
	$(COQBIN)rocq makefile -f _CoqProject.mathcomp -o Makefile.mathcomp.coq
