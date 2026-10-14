# The Subjectivity of Monoculture — Lean formalization

This repository formalizes the nine named theoretical results in the October 14, 2026 working draft of *The Subjectivity of Monoculture*.

Start with the [final validation report](FINAL_VALIDATION_REPORT.md), then the [precise formal statements](JGR26SubjectivityMonoculture/PaperInterface.lean).

The manuscript itself is not redistributed. Empirical claims and standalone estimation prose are outside this theorem formalization.

## Build

Install Lean through Elan, then run:

```sh
lake exe cache get
lake build JGR26SubjectivityMonoculture
lake env lean ProofChecks.lean
```

The toolchain, Mathlib, and AppliedModelingLib revisions are pinned. The AppliedModelingLib import supplies the required probability and finite optimization foundations.

The code is licensed under Apache 2.0.
