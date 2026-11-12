.PHONY: all proofs generate test audit check benchmark-generate benchmark

# Audit every registered module, including modules not imported by the runner.
COQ_LIBRARIES = $(subst /,.,$(patsubst src/%.v,MkRedex.%,$(filter src/%.v,$(shell cat ../_CoqProject))))
all: mk-search demo

proofs:
	cd .. && coq_makefile -f _CoqProject -o Makefile.coq
	$(MAKE) -C .. -f Makefile.coq all

generate: proofs
	cd .. && rocq c -Q src MkRedex extract/Extract.v

search.cmi: generate
	ocamlc -c search.mli
search.cmo: search.cmi
	ocamlc -c search.ml
frontend.cmi: search.cmi frontend.mli
	ocamlc -c frontend.mli
frontend.cmo: frontend.cmi search.cmo frontend.ml
	ocamlc -c frontend.ml
mk-search: search.cmo frontend.cmo cli.ml
	ocamlc search.cmo frontend.cmo cli.ml -o mk-search
demo: search.cmo demo.ml
	ocamlc search.cmo demo.ml -o demo
interface-tests: search.cmo frontend.cmo interface_tests.ml
	ocamlc search.cmo frontend.cmo interface_tests.ml -o interface-tests

relation-tests: search.cmo frontend.cmo relation_tests.ml
	ocamlc search.cmo frontend.cmo relation_tests.ml -o relation-tests

test: all interface-tests relation-tests
	./demo
	./interface-tests
	./relation-tests
	sh ./test-cli.sh


audit: proofs
	cd .. && coqchk -silent -R src MkRedex $(COQ_LIBRARIES)

check: audit test

# Benchmarks are opt-in and do not lengthen the ordinary correctness checks.
benchmark-generate: proofs
	cd .. && rocq c -Q src MkRedex extract/BenchmarkExtract.v

benchmark_search.cmi: benchmark-generate
	ocamlc -c benchmark_search.mli
benchmark_search.cmo: benchmark_search.cmi
	ocamlc -c benchmark_search.ml
benchmark-bytecode: benchmark_search.cmo benchmark.ml
	ocamlc -I +unix unix.cma benchmark_search.cmo benchmark.ml -o benchmark-bytecode
benchmark_search.cmx: benchmark_search.cmi
	ocamlopt -c benchmark_search.ml
benchmark-native: benchmark_search.cmx benchmark.ml
	ocamlopt -I +unix unix.cmxa benchmark_search.cmx benchmark.ml -o benchmark-native

unifier-benchmark-bytecode: benchmark_search.cmo unifier_benchmark.ml
	ocamlc -I +unix unix.cma benchmark_search.cmo unifier_benchmark.ml -o unifier-benchmark-bytecode
unifier-benchmark-native: benchmark_search.cmx unifier_benchmark.ml
	ocamlopt -I +unix unix.cmxa benchmark_search.cmx unifier_benchmark.ml -o unifier-benchmark-native

benchmark: benchmark-bytecode
	./benchmark-bytecode
