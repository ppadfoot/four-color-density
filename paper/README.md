# Manuscript and LaTeX source

[Read the PDF](four_color_density.pdf).

**Title:** A proof of Cohn and Rajagopal's four-color density conjecture  
**Authors:** Timofei Iuzhakov and Dmitry Vetrov

The included PDF is the reviewed 19-page manuscript with the updated acknowledgment of Henry Cohn. Packaging it for this repository did not change the mathematical text, bibliography, figures, or acknowledgment.

The source is `latex/article.tex`. The two vector figures, `equality_triangles.pdf` and `paired_cotangents.pdf`, must remain beside it. The bibliography is contained in the LaTeX file.

To build with an installed XeLaTeX distribution, run from the repository root:

```bash
cd paper/latex
xelatex -interaction=nonstopmode -halt-on-error article.tex
xelatex -interaction=nonstopmode -halt-on-error article.tex
```

This writes `paper/latex/article.pdf`. The distributed PDF was built using Tectonic 0.17.0 (XeTeX); with that version installed, the alternative command in `paper/latex/` is:

```bash
tectonic article.tex
```

Different TeX distributions or PDF timestamps may produce different PDF bytes. The supplied PDF and source files have snapshot checksums in the repository's `SHA256SUMS.txt`.

The formalization is in [`../lean/`](../lean/); its scope is explained in the manuscript's final appendix and in [the verification guide](../docs/VERIFICATION.md).
