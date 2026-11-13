.PHONY: all clean

all: NBE.pdf

# 1. Generate the TeX file from Literate Agda if NbE.lagda changes
NBE:
	agda --latex --latex-dir=. NBE.lagda.tex

# 2. Compile the main PDF using latexmk (handles pdflatex + bibtex cycles automatically)
NBE.pdf: NBE.bib NBE
	latexmk -f -pdf -use-make -shell-escape NBE.tex

clean:
	rm -rf ./*.aux ./*.log ./*.out ./*.toc ./*.bbl ./*.blg ./*.fdb_latexmk ./*.fls ./*.synctex.gz;
	rm -rf ./_minted-*;
	rm -rf ./*.out ./*.fdb_latexmk ./*.log ./*.ptb;
