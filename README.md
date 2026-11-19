# Rome CPP 2027
Artifact for Certified Proofs Programs 2027 publication *Normalization by Evaluation of Higher-Order Rows* by Alex Hubers & Garrett Morris.



## Artifact & Code
See [./Agda/Rome/REDME.lagda.md](./Agda/Rome/README.lagda.md) for a summary of the artifact and its claims.

## Paper Requirements
[NBE.lagda](./paper/NBE.lagda) requires:
- [Minted](https://github.com/gpoore/minted) (turn on the `shell-escape` flag);
- [Rosi Pygments](https://github.com/iowaFP/rosi-pygments) for the formatting of Rosi source; and 
- [Agda](https://agda.readthedocs.io/en/latest/getting-started/installation.html), as this is a [literate Agda](https://agda.readthedocs.io/en/latest/tools/literate-programming.html) document.

To build in shell (or powershell), run:

```sh
agda --latex --latex-dir=. NBE.lagda;
latexmk -pdf NBE.tex
```

from the [./paper](./paper/) directory.

### VS Code 
To build on Windows, I've added a [task](./.vscode/tasks.json) "Compile Agda to PDF" for compilation
via VS Code (open [NBE.lagda](./paper/NBE.lagda), hit ctrl+shift+p and run "Tasks: Run Build Task").

### Emacs
If you are using [AucTeX](https://www.gnu.org/software/auctex/), add the following to your emacs configuration:
```lisp
(add-to-list 'TeX-command-list
               '("LagdaLaTeX" "agda --latex --latex-dir=. %s && latexmk -c && latexmk --shell-escape -f -pdf %z.tex" TeX-run-command nil t
                 :help "Generate LaTeX from Literate Agda file"))
```

which will add "LagdaLaTeX" as an option when building (C-c C-C). 


