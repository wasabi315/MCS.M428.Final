#!/usr/bin/env perl

$latex                         = 'platex %O -synctex=1 -interaction=nonstopmode %S';
$pdflatex                      = 'lualatex %O -synctex=1 -interaction=nonstopmode %S';
$biber                         = 'biber %O --bblencoding=utf8 -u -U --output_safechars %B';
$bibtex                        = 'pbibtex %O %B';
$makeindex                     = 'mendex %O -o %D %S';
$dvipdf                        = 'dvipdfmx %O -o %D %S';
$dvips                         = 'dvips %O -z -f %S | convbkmk -u > %D';
$ps2pdf                        = 'ps2pdf %O %S %D';
$pdf_mode                      = 1;
$pdf_previewer                 = 'xdg-open';
