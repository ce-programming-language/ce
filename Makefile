.PHONY: all build install clean test doc fmt lint release

all: build

build:
	dune build @all

install: build
	mkdir -p /usr/lib/ce
	cp -r ./std /usr/lib/ce
	dune install --prefix /usr/local

clean:
	dune clean

test:
	dune runtest

doc:
	dune build @doc

fmt:
	dune fmt

release: clean
	dune build --release
	dune install --prefix=./_build/release

dev-setup:
	opam install -y dune menhir sedlex ppx_deriving cmdliner fmt ocamlformat

help:
	@echo "CE-Lang Build Commands:"
	@echo "  make build       - Build the project"
	@echo "  make install     - Install ce compiler"
	@echo "  make clean       - Clean build artifacts"
	@echo "  make test        - Run tests"
	@echo "  make doc         - Generate documentation"
	@echo "  make fmt         - Format code"
	@echo "  make lint        - Lint code"
	@echo "  make release     - Build optimized release"
	@echo "  make dev-setup   - Setup development environment"
