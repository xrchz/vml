.PHONY: all clean
all: ocamltop_j ast.cmx

%.cmx: %.ml
	ocamlopt -c $<

ocamltop_j:
	exec ocamlmktop -o $@ -I `camlp5 -where` nums.cma unix.cma camlp5o.cma $(HOLLIGHT_DIR)/pa_j.cmo

clean:
	@rm ocamltop_j *.cmo *.cmi *.cmx
