.PHONY: clean

default: paper.pdf

# paper-full.tex : paper.lagda naive.lagda subst.lagda laws.lagda init.lagda lib.fmt
# 	echo "%let full = True" > is-full.lagda
# 	lhs2TeX  --agda $< > $@

paper.tex : paper.lagda is-jfp.lagda naive.lagda subst.lagda laws.lagda init.lagda lib.fmt
	lhs2TeX --agda $< > $@

%.pdf : %.tex local.bib
	latexmk -pdf $<
#	latexmk -pdf -pdflatex="xelatex" paper.tex

supplement.zip : README.txt naive.lagda subst.lagda laws.lagda init.lagda
	zip supplement.zip README.txt naive.lagda subst.lagda laws.lagda init.lagda

paper.bbl : paper.pdf

eptcs.zip : README.txt paper.lagda naive.lagda subst.lagda laws.lagda init.lagda paper.tex eptcs.bst eptcs.cls local.bib paper.bbl
	zip eptcs.zip README.txt naive.lagda subst.lagda laws.lagda init.lagda paper.tex eptcs.bst eptcs.cls local.bib paper.bbl

clean:
	rm paper.tex || true
	rm *.aux || true
	rm *.fdb_latexmk || true
	rm *.fls || true
	rm *.log || true
	rm *.out || true
	rm *.ptb || true
	rm paper.pdf || true
	rm *.zip || true
	rm *.bbl || true
	rm *.blg || true
	rm *.pag || true
	rm *.vtc || true
