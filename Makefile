%.tex : %.lagda lib.fmt
	lhs2TeX --agda $< > $@

%.pdf : %.tex local.bib %.bbl
	pdflatex $<

%.bbl : %.aux
	bibtex $<

