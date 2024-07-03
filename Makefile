DUNE ?= dune

.PHONY: bin install doc uninstall clean
bin:
	$(DUNE) build

install:
	cp _build/default/bin/main.exe .
	mv main.exe dolmen_skolemize

doc:
	$(DUNE) build @doc

uninstall:
	$(DUNE) uninstall

clean:
	dune clean
	rm -f dolmen_skolemize