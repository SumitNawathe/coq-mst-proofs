COQMFFLAGS := -Q . MST
ALLVFILES := Sets.v Enumerated.v Vertices.v Arcs.v Connected.v Degrees.v Digraphs.v Dipaths.v Edges.v Graphs.v Paths.v Trees.v Acyclic.v MST.v Logic.v CustomNotations.v SetLogic.v Cuts.v

build: Makefile.coq
	$(MAKE) -f Makefile.coq

clean::
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	$(RM) $(wildcard Makefile.coq Makefile.coq.conf) imp.ml imp.mli imp1.ml imp1.mli imp2.ml imp2.mli

Makefile.coq:
	coq_makefile $(COQMFFLAGS) -o Makefile.coq $(ALLVFILES)

-include Makefile.coq

.PHONY: build clean