%.tex : %.lagda lib.fmt
	lhs2TeX --agda $< > $@

%.pdf : %.tex local.bib
	pdflatex $<

%.bbl : %.aux
	bibtex $<

