all: expr miniml evaluation tests

expr: expr.ml
	ocamlbuild expr.byte

miniml: miniml.ml
	ocamlbuild miniml.byte

evaluation: evaluation.ml
	ocamlbuild evaluation.byte

tests: tests.ml
	ocamlbuild tests.byte

clean:
	rm -rf _build *.byte