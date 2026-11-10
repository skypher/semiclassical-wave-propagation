# On "Semiclassical wave propagation for large times": gaps, a counterexample, and a repaired statement

This repository contains the manuscript and the Lean 4 formalization of a repair of

> R. Schubert, *Semiclassical wave propagation for large times*, arXiv:0705.0134v1 (2007),
> withdrawn by its author in v2 (2011) for a gap in the proof of the dispersive estimates.

The strategy of the results is Schubert's. The manuscript locates the defects of the withdrawn preprint, shows
that its Theorem 1.3 is false as printed, and proves corrected versions of Theorems 1.3 and 1.4 and of
Corollaries 1.5 and 1.6. Schubert's files are not part of this repository.

## Contents

- `paper/`: LaTeX source of the manuscript (`paper.tex` with its input files). Build with `pdflatex paper.tex`
  (run it three times).
- `lean/`: the Lean 4 development, namespace `Qschubert` (Lean `v4.35.0`, Mathlib `v4.35.0`, `physicslib4`).
  Appendix "Formalization" of the manuscript says which statements are formalized, in which reading, and
  which are not; its table maps every labelled statement of the manuscript to a Lean theorem.
- `.github/workflows/lean.yml`: builds `lean/` from a fresh checkout and runs the two axiom audits. The build
  runs when `lean/` has changed; a commit that leaves `lean/` unchanged takes over the result of the last run
  on the same Lean sources.

## Checking the formalization

```
cd lean
lake exe cache get
lake build
lake env lean scripts/Axioms.lean    > axioms.log
lake env lean scripts/AxiomsAll.lean > axioms_all.log
python3 -u scripts/check_axioms.py named axioms.log scripts/Axioms.lean
python3 -u scripts/check_axioms.py all axioms_all.log
```

`scripts/Axioms.lean` prints the axioms of the named declarations; `scripts/AxiomsAll.lean` checks every
declaration of the project. Both must report only `propext`, `Classical.choice` and `Quot.sound`.

Comments in the Lean sources and in the LaTeX sources refer in places to working documents of the project
(`lean/BLUEPRINT.md`, files under `notes/`, review numbers such as `R60`) and to line numbers of the LaTeX
source of arXiv:0705.0134v1. These working documents are not part of this repository; nothing in the
manuscript or in the formal statements depends on them.

A kernel check certifies the proofs of the formal statements. Whether a formal statement says what the
corresponding statement of the manuscript says is a matter of reading; the manuscript's appendix lists the
reading choices.
