# Source examples and checks; none resumes the paused research programme.
.DEFAULT_GOAL := help
PYTHON ?= python3
CARGO ?= cargo
LAKE ?= lake
PROTOC ?= protoc
SIBLING_ROOT ?= ..

.PHONY: help examples example-rust example-lean build-formal check-formal check-formal-partial check-protos check-paper-build

help:
	@echo 'examples              Run the Rust and Lean reading examples'
	@echo 'check-formal          Build Lean and require strict paper correspondence'
	@echo 'check-formal-partial  Build Lean and check registered open obligations'
	@echo 'check-protos          Compile headers with separate classical/quantum roots'
	@echo 'check-paper-build     Test bibliography and figure builds with real TeX tools'

examples: example-rust example-lean

example-rust:
	$(CARGO) run --offline --manifest-path kernel/Cargo.toml --example first_use

build-formal:
	cd formal && $(LAKE) build

example-lean: build-formal
	cd formal && $(LAKE) env lean examples/ReadExample.lean

check-formal: build-formal
	cd formal && $(PYTHON) check_correspondence.py

check-formal-partial: build-formal
	cd formal && $(PYTHON) check_correspondence.py --allow-open

check-protos:
	$(PYTHON) tools/check_protos.py --protoc "$(PROTOC)" --siblings "$(SIBLING_ROOT)"

check-paper-build:
	$(PYTHON) -m unittest discover -s tests -p 'test_paper_*.py' -v
