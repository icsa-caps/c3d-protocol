#
# Simple Makefile for LaTeX
#
# Author: Marco Elver
# Version: 20130924-1

DOC_PREFIX=c3d-protocol
BIB_FILES=micro2016.bib
SUPPORT_FILES=

# Additional source files
TEX_FILES=$(shell find ./tex/ -type f -name "*.tex" 2> /dev/null)

# Alternative template path; set in case default is not found below
TEMPLATE_PATH_ALT=

##
# Setup binaries
LATEX=pdflatex -file-line-error -halt-on-error

# Options for this are: bibtex, bibtex8, biber (recommended for BibLaTeX)
BIBGEN=bibtex

##
# RULES

.PHONY: all
all: pdf view

##
# Generate PDF

.PHONY: pdf
pdf: $(DOC_PREFIX).pdf

$(DOC_PREFIX).pdf: $(DOC_PREFIX).tex $(TEX_FILES) $(SUPPORT_FILES) $(DOC_PREFIX).bbl
	@echo "======================================================"
	$(LATEX) $(DOC_PREFIX).tex

%__eps.pdf: %.eps
	@echo "======================================================"
	epstopdf --outfile=$@ $<

%__svg.pdf: %.svg
	@echo "======================================================"
	inkscape --export-pdf=$@ $<

%__dot.pdf: %.dot
	@echo "======================================================"
	dot -Tpdf $< > $@
	pdfcrop $@ $@

%__dia.pdf: %.dia
	@echo "======================================================"
	dia -n -e $<.eps $<
	epstopdf --outfile=$@ $<.eps

$(DOC_PREFIX).bbl: $(BIB_FILES)
	@echo "======================================================"
	$(LATEX) $(DOC_PREFIX).tex
	@echo "------------------------------------------------------"
	$(BIBGEN) $(DOC_PREFIX)
	@echo "------------------------------------------------------"
	$(LATEX) $(DOC_PREFIX).tex

##
# Helper targets

.PHONY: view
view:
	- @xdg-open $(DOC_PREFIX).pdf

.PHONY: clean
clean:
	$(RM) $(DOC_PREFIX).out
	$(RM) $(DOC_PREFIX).log
	$(RM) $(DOC_PREFIX).ps
	$(RM) $(DOC_PREFIX).dvi
	$(RM) $(DOC_PREFIX).aux
	$(RM) $(DOC_PREFIX).bbl
	$(RM) $(DOC_PREFIX).blg
	$(RM) $(DOC_PREFIX).toc
	$(RM) $(DOC_PREFIX).lof
	$(RM) $(DOC_PREFIX).lol
	$(RM) $(DOC_PREFIX).lot
	$(RM) $(DOC_PREFIX).nav
	$(RM) $(DOC_PREFIX).snm
	$(RM) $(DOC_PREFIX).bcf
	$(RM) $(DOC_PREFIX).run.xml

.PHONY: cleanall
cleanall: clean
	$(RM) $(DOC_PREFIX).pdf
	$(RM) *__eps.pdf fig/*__eps.pdf
	$(RM) *__svg*.pdf fig/*__svg*.pdf
	$(RM) *__dot.pdf fig/*__dot.pdf
	$(RM) *__dia.pdf fig/*__dia.pdf *.dia.eps fig/*.dia.eps

