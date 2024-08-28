%.tex : %.lagda lib.fmt
	lhs2TeX --agda $< > $@

%.pdf : %.tex local.bib
	latexmk -pdf paper.tex
#	latexmk -pdf -pdflatex="xelatex" paper.tex

