#!/bin/bash

pdflatex algebra.tex
htlatex algebra.tex "xhtml, charset=utf-8" " -cunihtf -utf8"
mv algebra.html *.css *.png html/

pdflatex analisi.tex
htlatex analisi.tex "xhtml, charset=utf-8" " -cunihtf -utf8"
mv analisi.html *.css *.png html/

pdflatex ct.tex
htlatex ct.tex "xhtml, charset=utf-8" " -cunihtf -utf8"
mv ct.html *.css *.png html/

rm *.4ct *.4tc *.aux *.dvi *.idv *.lg *.log *.tmp *.xref *.synctex.gz
