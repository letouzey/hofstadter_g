

poster.pdf: poster.tex
#	pdflatex $^
	rubber -f --pdf $^ || rubber -f --pdf $^

# the || is a hack : currently the first build without poster.aux fails...

clean:
	rm -f poster.dvi poster.pdf poster.aux poster.log poster.nav poster.snm poster.toc poster.out poster.rubbercache
