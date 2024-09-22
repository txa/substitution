.PHONY: clean

default: paper.pdf

paper-full.tex : paper.lagda naive.lagda subst.lagda laws.lagda init.lagda lib.fmt
	echo "%let full = True" > is-full.lagda
	lhs2TeX  --agda $< > $@

paper.tex : paper.lagda naive.lagda subst.lagda laws.lagda init.lagda lib.fmt
	echo "%let full = False" > is-full.lagda
	lhs2TeX --agda $< > $@

%.pdf : %.tex local.bib
	latexmk -pdf $<
#	latexmk -pdf -pdflatex="xelatex" paper.tex

supplement.zip : README.txt naive.lagda subst.lagda laws.lagda init.lagda
	zip supplement.zip README.txt naive.lagda subst.lagda laws.lagda init.lagda

clean:
	rm *.tex || true
	rm *.aux || true
	rm *.fdb_latexmk || true
	rm *.fls || true
	rm *.log || true
	rm *.out || true
	rm *.ptb || true
	rm *.pdf || true
	rm *.zip || true
