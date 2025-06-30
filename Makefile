.PHONY: clean

default: paper.pdf

# paper-full.tex : paper.lagda naive.lagda subst.lagda laws.lagda init.lagda lib.fmt
# 	echo "%let full = True" > is-full.lagda
# 	lhs2TeX  --agda $< > $@

paper.tex : paper.lagda is-jfp.lagda naive.lagda subst.lagda laws.lagda init.lagda lib.fmt
	lhs2TeX --verb --agda $< > $@

%.pdf : %.tex local.bib
	latexmk -pdf -pdflatex="xelatex" $<
#	latexmk -pdf -pdflatex="xelatex" paper.tex

supplement.zip : README.txt naive.lagda subst.lagda laws.lagda init.lagda
	zip supplement.zip README.txt naive.lagda subst.lagda laws.lagda init.lagda

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
