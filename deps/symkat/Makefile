NAME=symkat
OCAMLBUILD=ocamlbuild -use-ocamlfind -pkg safa
OCAMLFIND=ocamlfind
OBJS=$(wildcard _build/*.cm* _build/*.a _build/*.o)
# OBJS=$(wildcard _build/*.{cmi,cmo,cma,cmx,cmxa,a,o})

ifndef PREFIX
  PREFIX=/usr/local
else
  PREFIX:=${PREFIX}
endif

standalone:
	$(OCAMLBUILD) $(NAME).native

install: bc-lib nc-lib standalone 
	@$(OCAMLFIND) install $(NAME) META $(OBJS)
	install $(NAME).native $(PREFIX)/bin/$(NAME)

uninstall:
	$(OCAMLFIND) remove $(NAME)
	rm -f ${PREFIX}/bin/$(NAME)

bench: 
	$(OCAMLBUILD) bench.native 
	time ./bench.native -ssf -ant
	time ./bench.native -ssf -ant -hk
	time ./bench.native -ssf -iyu
	time ./bench.native -ssf -iyu -hk
	time ./bench.native -ssf -brz
	time ./bench.native -ssf -brz -hk
	time ./bench.native -ant
	time ./bench.native -ant -hk
	time ./bench.native -iyu
	time ./bench.native -iyu -hk
	time ./bench.native -brz
	time ./bench.native -brz -hk

doc:
	$(OCAMLBUILD) $(NAME).docdir/index.html

clean:
	$(OCAMLBUILD) -clean 

bc-standalone:
	$(OCAMLBUILD) $(NAME).byte

bc-lib:
	$(OCAMLBUILD) $(NAME).cma

nc-lib:
	$(OCAMLBUILD) $(NAME).cmxa

tests:
	$(OCAMLBUILD) tests.native 
	./tests.native -ant
	./tests.native -iyu
	./tests.native -brz
	./tests.native -hk -ant
	./tests.native -hk -iyu
	./tests.native -hk -brz
	./tests.native -ssf -ant
	./tests.native -ssf -iyu
	./tests.native -ssf -brz
	./tests.native -ssf -hk -ant
	./tests.native -ssf -hk -iyu
	./tests.native -ssf -hk -brz
	./tests.native -con -ant
	./tests.native -con -iyu
	./tests.native -con -hk -ant
	./tests.native -con -hk -iyu
	./tests.native -con -ssf -ant
	./tests.native -con -ssf -iyu
	./tests.native -con -ssf -hk -ant
	./tests.native -con -ssf -hk -iyu
