# Final Validation Report: The Subjectivity of Monoculture
Updated: 2026-10-14

## 1. Human Verdict

The nine named theoretical results are formalized under their stated
hypotheses and intended definedness conventions. Their conclusions match the
current manuscript. No additional assumption or substantive theorem repair
is required.

## 2. Closeout Status

- Completion status: Formalized
- One-sentence recap: The mixture, null-ladder, population-relativity,
  heterogeneity and residual results are checked against the current draft.

## 3. Source and Scope

The source is the working draft dated October 14, 2026. The scope covers its
named main-text and appendix theory, including the labelled empirical-residuals
remark, and every definition and condition governing those results.
Standalone empirical, computational, related-work and future-work prose is
outside this theorem audit.

## 4. Researcher Summary of Checked Results

The main results appear first, followed by appendix support.

| Result | Comparison with source |
| --- | --- |
| **Theorem 1.** Every finite binary response law has a conditionally independent Bernoulli mixture representation with at most 2^m positive-mass components. | Exact |
| **Proposition 2.** Minimal excess is nonincreasing along a nested null ladder. | Exact |
| **Theorem 3.** Residual cross dependence vanishes when the fitted null discrepancy tends to zero and controls bounded expectations. | Exact |
| **Proposition 4.** A population-specific best fit may change when the item or model population is restricted. | Exact |
| **Theorem 5.** Local distance to the exact prediction fiber is bounded by Cε/√h under the stated identification conditions. | Exact |
| **Lemma 6.** Multidimensional IRT null families are nested as the dimension increases. | Exact |
| **Proposition 7.** Residual means track average calibration error, and demeaning gives the stated centered decomposition and zero sample mean. | Exact |
| **Remark 1.** Uniform probability consistency and the stated moment laws yield vanishing empirical residual covariance and, with the variance floor, correlation. | Exact |
| **Lemma 8.** Increasing dot-product links satisfy the stated local identification bound, including the fixed-coordinate case. | Exact |

## 5. Remaining Boundaries and Gaps

None.

## 6. Additional Assumptions Beyond Paper

None.

## 7. Proof-Strategy Deviations

None.

## 8. Proof Tricks Worth Reusing

- Use deterministic binary response vectors as the components of a finite
  Bernoulli mixture.
- Establish the exact centering identities before applying a law of large
  numbers.
- Measure local parameter distance to the complete prediction fiber so that
  observational invariances are retained.

## 9. Generalizations, Conjectures, and Extensions

None selected for this closeout.

## 10. Source Clarifications and Exact Readings

No change to a named result is required.

## 11. Paper Issues or Caveats

None within the selected theorem scope.

## 12. Detailed Formalization Evidence

The [paper interface](JGR26SubjectivityMonoculture/PaperInterface.lean) contains nine transparent proposition
specifications. The [proof interface](JGR26SubjectivityMonoculture/ProofInterface.lean) proves each
specification through the paper root import. Kernel checks establish the exact
Spec/proof relation and safe axiom closure for every pair. The permitted axioms
are propositional extensionality, classical choice, and quotient soundness.

Each result has an independent current-source comparison. Governing definitions
and conditions receive separate comparisons against their complete elaborated
declarations, including the material supporting definitions. The source-facing
judgments are separate from the kernel's proof checks.

## 13. Paper Assumption Provenance

The local stability result uses Assumption 1: constant Jacobian rank near the
chosen fit and the stated lower bound on perturbations orthogonal to the
Jacobian kernel. It is exposed by `HasLocalIdentificationAt`. Lemma 8 proves
the stated Jacobian bound for increasing dot-product links. Other premises
are the source's probability model, discrepancy control, fitted-probability
consistency, moment laws, and positive variance floor where specified.
No premise is introduced as a substitute for a missing proof.

## 14. Displayed Formula Provenance

| Formula or clause | Checked basis |
| --- | --- |
| Finite mixture support at most 2^m | Binary response vectors supply the mixture atoms; their conditional laws have the required probabilities and independence. |
| Minimal excess at adjacent levels | The smaller null family is included in the larger one, so its infimum cannot be lower. |
| Pair-residual cross moment | The bounded residual functional transfers discrepancy control; the fitted item-row product law has zero centered pair moment. |
| Population-specific optimizer | A fixed two-item logistic example has attained full and restricted optima with different marginal predictions. |
| Heterogeneity and local distance | The source factor covariance matrices define h; constant rank and the Jacobian lower bound yield the local Cε/√h bound to the full prediction fiber. |
| Calibration and centering | Expanding raw residuals gives true centered fluctuations plus calibration error; subtracting the sample mean gives the exact centered decomposition. |
| Empirical covariance and correlation | Uniform fitted-probability error and the specified moment limits transfer the population cross-moment limit; the variance floor controls normalization. |
| Link derivative minimum | The positive minimum over the finite fitted logits gives the stated identification constant, also in the fixed-coordinate domain. |

## 15. Library Lift Pass

The development uses six modules from AppliedModelingLib, together with
Mathlib. Their role is ordinary finite sums, optimization, expectation,
probability, independence, and limit support. The current dependency graph
requires no material library source-definition judgment and exposes no
undischarged certificate premise. No new library extraction is needed for
this paper.

## 16. DAG Audit

The [diagram](docs/DependencyDAG.pdf) and its [source](docs/DependencyDAG.tex)
show the paper's models, definitions, Assumption 1, and all nine named results.
Main results precede appendix support. Arrows reflect mathematical
dependencies; auxiliary proof declarations are excluded. The rendered
labels and arrows have been visually inspected.

## 17. Validation Checks

The paper-root build and all nine exact Spec/proof checks pass. Independent
source reviewers matched the selected results and their governing definitions.
The terminal closeout checks the complete tracked-paper build and requires
a final independent source audit before issuing its native acceptance record.
Human statement sign-off has not been recorded: 0 of 9 result rows.

## 18. Paper Definitions Checked

The checked model surface includes the MIRT null, null ladder, minimal excess
(including attained fits and nonattained approximation sequences), selected
best fit, population restriction, fitted success probabilities,
raw and centered residuals, correlation normalization, factor prediction map,
heterogeneity and its stated normalization, local ε-equivalence set, full
exact-prediction fiber and distance, Jacobian identification, and the fitted
link derivative minimum. Their source presentations remain distinct even
where they share a mathematical primitive. The [model notes](docs/SOURCE_CLARIFICATIONS.md)
explain prediction invariances, conditional residual probabilities, and
calibration centering.

## 19. Named Theorem Statements Checked

### Theorem 1

**Paper statement.** Every binary response law on m coordinates is the marginal of a finite Bernoulli mixture with at most 2^m positive-mass components and conditionally independent coordinates.

**Lean interface statement.** `PaperInterface.theorem1Spec`, proved by `ProofInterface.theorem1`, covers this conclusion.

**Status.** Exact.

### Proposition 2

**Paper statement.** Minimal excess does not increase when a nested null ladder increases in level.

**Lean interface statement.** `PaperInterface.proposition2Spec`, proved by `ProofInterface.proposition2`, covers this conclusion.

**Status.** Exact.

### Theorem 3

**Paper statement.** Under the stated discrepancy control and convergence, each pair-residual cross moment tends to zero. Conditional item-row independence in the null is sufficient; cross-item independence is unnecessary.

**Lean interface statement.** `PaperInterface.theorem3Spec`, proved by `ProofInterface.theorem3`, covers this conclusion.

**Status.** Exact.

### Proposition 4

**Paper statement.** Population restriction may fail to commute with fitting, with a fixed link, discrepancy, and response law witnessing incompatible full and restricted optimizer marginals.

**Lean interface statement.** `PaperInterface.proposition4Spec`, proved by `ProofInterface.proposition4`, covers this conclusion.

**Status.** Exact.

### Theorem 5

**Paper statement.** For a given smooth fitted prediction map with positive heterogeneity and the stated local identification, the local distance to its exact prediction fiber is at most Cε/√h.

**Lean interface statement.** `PaperInterface.theorem5Spec`, proved by `ProofInterface.theorem5`, covers this conclusion.

**Status.** Exact.

### Lemma 6

**Paper statement.** The dimension-K probit MIRT null embeds in the dimension-(K+1) null by appending zero coordinates.

**Lean interface statement.** `PaperInterface.lemma6Spec`, proved by `ProofInterface.lemma6`, covers this conclusion.

**Status.** Exact.

### Proposition 7

**Paper statement.** Expected raw residuals equal expected calibration errors; the sample residual mean tracks average calibration error in probability; demeaning gives zero sample mean and the exact centered fluctuation/calibration decomposition, including sample-dependent estimates.

**Lean interface statement.** `PaperInterface.proposition7Spec`, proved by `ProofInterface.proposition7`, covers this conclusion.

**Status.** Exact.

### Remark 1

**Paper statement.** Uniform fitted-probability consistency and the stipulated oracle moment laws transfer the vanishing population residual cross moment to sample centered covariance. Correlation also vanishes under the eventual positive variance floor.

**Lean interface statement.** `PaperInterface.remark1Spec`, proved by `ProofInterface.remark1`, covers this conclusion.

**Status.** Exact.

### Lemma 8

**Paper statement.** For the stated increasing dot-product links at positive fitted heterogeneity, the finite positive derivative minimum yields local identification with the specified constant, on both the full factor domain and the fixed-coordinate domain.

**Lean interface statement.** `PaperInterface.lemma8Spec`, proved by `ProofInterface.lemma8`, covers this conclusion.

**Status.** Exact.

## 20. Paper-Facing Statement Validator Ledger

The nine result targets were independently compared with their pinned source
statements on October 14, 2026. The result reviewer was distinct from interface
and proof authors. Model review does not imply human sign-off.

| Result | Lean specification | Independent comparison |
| --- | --- | --- |
| Theorem 1 | `PaperInterface.theorem1Spec` | Matches |
| Proposition 2 | `PaperInterface.proposition2Spec` | Matches |
| Theorem 3 | `PaperInterface.theorem3Spec` | Matches |
| Proposition 4 | `PaperInterface.proposition4Spec` | Matches |
| Theorem 5 | `PaperInterface.theorem5Spec` | Matches |
| Lemma 6 | `PaperInterface.lemma6Spec` | Matches |
| Proposition 7 | `PaperInterface.proposition7Spec` | Matches |
| Remark 1 | `PaperInterface.remark1Spec` | Matches |
| Lemma 8 | `PaperInterface.lemma8Spec` | Matches |

## 21. Source-Coverage Audit Ledger

The complete source inventory identifies nine named results, four named
definitions, and one named assumption. Its definition-shaped prose inventory
contains 61 presentations: 23 governing theory definitions, 25 computational
definitions, nine local-proof vocabulary presentations, and four contextual
passages outside the selected theory. The latter three classes are retained
in the inventory with their scope dispositions. The source-only inventory and
its definition dispositions were independently reviewed. No selected named
result is missing.

| Source result | Interface row | Source comparison |
| --- | --- | --- |
| Theorem 1 | `PaperInterface.theorem1Spec` | Exact |
| Proposition 2 | `PaperInterface.proposition2Spec` | Exact |
| Theorem 3 | `PaperInterface.theorem3Spec` | Exact |
| Proposition 4 | `PaperInterface.proposition4Spec` | Exact |
| Theorem 5 | `PaperInterface.theorem5Spec` | Exact |
| Lemma 6 | `PaperInterface.lemma6Spec` | Exact |
| Proposition 7 | `PaperInterface.proposition7Spec` | Exact |
| Remark 1 | `PaperInterface.remark1Spec` | Exact |
| Lemma 8 | `PaperInterface.lemma8Spec` | Exact |
