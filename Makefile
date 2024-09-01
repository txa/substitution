.PHONY: clean

default: paper.pdf

%.tex : %.lagda lib.fmt
	lhs2TeX --agda $< > $@

%.pdf : %.tex local.bib
	latexmk -pdf paper.tex
#	latexmk -pdf -pdflatex="xelatex" paper.tex

clean:
	rm *.tex || true
	rm *.aux || true
	rm *.fdb_latexmk || true
	rm *.fls || true
	rm *.log || true
	rm *.out || true
	rm *.ptb || true
	rm *.pdf || true
