PAPER=paper
TALK=talk
# turn dot to pdf
# Pattern rules
DOT?=dot
%.pdf : %.dot
	$(DOT) -Tpdf -o $@ $<

# Process all *.gv files in this directory, producing .png and .svg output.
SRC_FILES=$(wildcard latex/*.dot)
OUT_FILES=$(SRC_FILES:.dot=.pdf)

out: $(OUT_FILES)

#help me
listtargets:
	@echo $(OUT_FILES)
.PHONY: all


all: latex/$(PAPER).pdf latex/$(TALK).pdf $(OUT_FILES)

src = src

lib-agdas:=$(shell find $(src) -name '*.agda' | grep -v 'Old/')
lib-lagdas:=$(shell find $(src) -name '*.lagda.tex' | grep -v 'Old/')
lib-texs:=$(patsubst $(src)/%.lagda.tex,latex/%.tex,$(lib-lagdas))
lib-texs: $(lib-texs)

# Sanity check
test-lib-texs:
	@echo $(lib-texs)

AGDA=agda

PRECIOUS: $(lib-texs)

# LaTeX generated from literate sources
latex/%.tex: $(src)/%.lagda.tex
	@mkdir -p $(dir $@)
	${AGDA} --latex --latex-dir=latex $<

latex-deps=macros.tex unicode.tex agda-commands.tex bib.bib



latex/%.pdf: $(latex-deps) %.tex $(lib-texs) $(test-texs) $(example-texs) $(example-toks)
	latexmk -xelatex -bibtex -output-directory=latex -shell-escape $*.tex
	@touch $@

# The touch is in case latexmk decides not to update the pdf.

# For MacOS
SHOWPDF=zathura

%.see: latex/%.pdf
	${SHOWPDF} $<

see: $(PAPER).see

clean:
	rm -rf _build latex
	- $(RM) $(OUT_FILES)
