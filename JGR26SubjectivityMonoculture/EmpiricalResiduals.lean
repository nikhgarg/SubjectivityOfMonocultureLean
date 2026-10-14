import JGR26SubjectivityMonoculture.MainTheorems
import AppliedModelingLib.Foundations.Probability.RenewalReward
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# IID evaluation sampling and residual correlation normalization

Fixed oracle residual scores are measurable functions of IID evaluation rows.
Their empirical means, cross-moments and centered covariances obey the strong
law. Fitted scores may depend on the entire sample: their transfer uses uniform
probability-error bounds, not a fabricated IID assumption on fitted residuals.

Covariance convergence alone does not imply convergence of Pearson correlation;
normalization requires a positive variance floor or denominator-relative error.
Model-dimension and sample-size limits are kept separate.

The imported shared strong-law wrapper uses Mathlib's Etemadi theorem, pinned at
`v4.30.0-rc2`, commit `5450b53e5ddc75d46418fabb605edbf36bd0beb6`, Apache 2.0:
<https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Probability/StrongLaw.lean>.
-/

namespace JGR26SubjectivityMonoculture

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology ProbabilityTheory

noncomputable section

/-- Empirical mean of one fixed row score, normalized by the evaluation sample size. -/
def empiricalRowMoment {Ω Row : Type*}
    (row : ℕ → Ω → Row) (score : Row → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (∑ i ∈ Finset.range n, score (row i ω)) / (n : ℝ)

/-- The centered empirical covariance of two fixed row scores. -/
def empiricalRowCovariance {Ω Row : Type*}
    (row : ℕ → Ω → Row) (x y : Row → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  empiricalRowMoment row (fun z => x z * y z) n ω -
    empiricalRowMoment row x n ω * empiricalRowMoment row y n ω

/-- Population covariance, retaining the two potentially nonzero residual means. -/
def populationRowCovariance {Ω Row : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (row : ℕ → Ω → Row) (x y : Row → ℝ) : ℝ :=
  (∫ ω, x (row 0 ω) * y (row 0 ω) ∂P) -
    (∫ ω, x (row 0 ω) ∂P) * (∫ ω, y (row 0 ω) ∂P)

/-- The raw-moment formula is exactly the average product of centered sample scores. -/
theorem empiricalRowCovariance_eq_centered_average {Ω Row : Type*}
    (row : ℕ → Ω → Row) (x y : Row → ℝ) (n : ℕ) (ω : Ω) :
    empiricalRowCovariance row x y n ω =
      (∑ i ∈ Finset.range n,
        (x (row i ω) - empiricalRowMoment row x n ω) *
          (y (row i ω) - empiricalRowMoment row y n ω)) / (n : ℝ) := by
  let mx := empiricalRowMoment row x n ω
  let my := empiricalRowMoment row y n ω
  have hsum :
      (∑ i ∈ Finset.range n, (x (row i ω) - mx) * (y (row i ω) - my)) =
      (∑ i ∈ Finset.range n, x (row i ω) * y (row i ω)) -
        mx * (∑ i ∈ Finset.range n, y (row i ω)) -
        my * (∑ i ∈ Finset.range n, x (row i ω)) + (n : ℝ) * (mx * my) := by
    calc
      _ = ∑ i ∈ Finset.range n,
          (x (row i ω) * y (row i ω) - mx * y (row i ω) - my * x (row i ω) + mx * my) := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  change empiricalRowCovariance row x y n ω =
    (∑ i ∈ Finset.range n, (x (row i ω) - mx) * (y (row i ω) - my)) / (n : ℝ)
  rw [hsum]
  dsimp only [mx, my, empiricalRowCovariance, empiricalRowMoment]
  by_cases hn : n = 0
  · simp only [hn, Finset.range_zero, Finset.sum_empty, Nat.cast_zero, div_zero, mul_zero,
      sub_zero, zero_add]
  · have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    field_simp [hnreal]
    ring

/-- The empirical variance used for Pearson normalization is genuinely nonnegative. -/
theorem empiricalRowCovariance_self_nonneg {Ω Row : Type*}
    (row : ℕ → Ω → Row) (x : Row → ℝ) (n : ℕ) (ω : Ω) :
    0 ≤ empiricalRowCovariance row x x n ω := by
  rw [empiricalRowCovariance_eq_centered_average]
  exact div_nonneg (Finset.sum_nonneg fun i _hi => mul_self_nonneg _) (Nat.cast_nonneg n)

section Sampling

variable {Ω Row : Type*} [MeasurableSpace Ω] [MeasurableSpace Row] {P : Measure Ω}

/--
A measurable score of IID rows has a genuine empirical strong law. Independence
and identical distribution of the score sequence are derived by composition.
-/
theorem ae_empiricalRowMoment_tendsto_of_iid
    (row : ℕ → Ω → Row) (score : Row → ℝ) (hscore : Measurable score)
    (hint : Integrable (score ∘ row 0) P)
    (hindep : Pairwise (fun i j => row i ⟂ᵢ[P] row j))
    (hident : ∀ i, IdentDistrib (row i) (row 0) P P) :
    ∀ᵐ ω ∂P, Tendsto (fun n => empiricalRowMoment row score n ω)
      atTop (𝓝 (∫ ω, score (row 0 ω) ∂P)) := by
  exact AppliedModelingLib.ae_tendsto_empirical_mean_real_of_iid
    (fun i => score ∘ row i) hint
    (fun i j hij => (hindep hij).comp hscore hscore)
    (fun i => (hident i).comp hscore)

/-- Bounded measurable scores have the integrability required by the strong law. -/
theorem integrable_rowScore_of_bounded [IsFiniteMeasure P]
    (row : Ω → Row) (hrow : Measurable row) (score : Row → ℝ) (hscore : Measurable score)
    (C : ℝ) (hbound : ∀ z : Row, |score z| ≤ C) : Integrable (score ∘ row) P := by
  exact Integrable.of_bound (hscore.comp hrow).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hbound (row ω))

/-- Empirical centered covariance estimates the actual population covariance. -/
theorem ae_empiricalRowCovariance_tendsto_of_iid
    (row : ℕ → Ω → Row) (x y : Row → ℝ)
    (hx : Measurable x) (hy : Measurable y)
    (hxint : Integrable (x ∘ row 0) P) (hyint : Integrable (y ∘ row 0) P)
    (hxyint : Integrable ((fun z => x z * y z) ∘ row 0) P)
    (hindep : Pairwise (fun i j => row i ⟂ᵢ[P] row j))
    (hident : ∀ i, IdentDistrib (row i) (row 0) P P) :
    ∀ᵐ ω ∂P, Tendsto (fun n => empiricalRowCovariance row x y n ω)
      atTop (𝓝 (populationRowCovariance P row x y)) := by
  have hxm := ae_empiricalRowMoment_tendsto_of_iid row x hx hxint hindep hident
  have hym := ae_empiricalRowMoment_tendsto_of_iid row y hy hyint hindep hident
  have hxym := ae_empiricalRowMoment_tendsto_of_iid row (fun z => x z * y z)
    (hx.mul hy) hxyint hindep hident
  filter_upwards [hxm, hym, hxym] with ω hxm hym hxym
  exact hxym.sub (hxm.mul hym)

/-- The residual-score boundedness supplies every moment assumption in the covariance LLN. -/
theorem ae_empiricalRowCovariance_tendsto_of_bounded_iid [IsFiniteMeasure P]
    (row : ℕ → Ω → Row) (hrow : Measurable (row 0)) (x y : Row → ℝ)
    (hx : Measurable x) (hy : Measurable y)
    (hxbound : ∀ z, |x z| ≤ 1) (hybound : ∀ z, |y z| ≤ 1)
    (hindep : Pairwise (fun i j => row i ⟂ᵢ[P] row j))
    (hident : ∀ i, IdentDistrib (row i) (row 0) P P) :
    ∀ᵐ ω ∂P, Tendsto (fun n => empiricalRowCovariance row x y n ω)
      atTop (𝓝 (populationRowCovariance P row x y)) := by
  apply ae_empiricalRowCovariance_tendsto_of_iid row x y hx hy
    (integrable_rowScore_of_bounded (row 0) hrow x hx 1 hxbound)
    (integrable_rowScore_of_bounded (row 0) hrow y hy 1 hybound)
    _ hindep hident
  apply integrable_rowScore_of_bounded (row 0) hrow (fun z => x z * y z) (hx.mul hy) 1
  intro z
  rw [abs_mul]
  exact (mul_le_mul (hxbound z) (hybound z) (abs_nonneg _) zero_le_one).trans_eq (mul_one 1)

end Sampling

/-! ## Source binary residuals and fitted-probability perturbations -/

/-- The observed binary residual score is measurable when its probability and response are. -/
theorem measurable_binaryResidual_score
    {Row : Type*} [MeasurableSpace Row] (p : Row → ℝ) (response : Row → Bool)
    (hp : Measurable p) (hy : Measurable response) :
    Measurable (fun z => binaryResidual (p z) (response z)) := by
  exact ((measurable_of_finite boolAsReal).comp hy).sub hp

/-- Prefix average of the source's unnormalized binary residual cross-products. -/
def empiricalBinaryResidualCrossMoment {Model : Type*}
    (p : ℕ → Model → ℝ) (response : ℕ → Model → Bool) (j ℓ : Model) (n : ℕ) : ℝ :=
  (∑ i ∈ Finset.range n, binaryResidual (p i j) (response i j) *
    binaryResidual (p i ℓ) (response i ℓ)) / (n : ℝ)

/-- Prefix mean of one binary residual coordinate. -/
def empiricalBinaryResidualMean {Model : Type*}
    (p : ℕ → Model → ℝ) (response : ℕ → Model → Bool) (j : Model) (n : ℕ) : ℝ :=
  (∑ i ∈ Finset.range n, binaryResidual (p i j) (response i j)) / (n : ℝ)

/-- Centered sample covariance of binary residuals, allowing nonzero sample means. -/
def empiricalBinaryResidualCovariance {Model : Type*}
    (p : ℕ → Model → ℝ) (response : ℕ → Model → Bool) (j ℓ : Model) (n : ℕ) : ℝ :=
  empiricalBinaryResidualCrossMoment p response j ℓ n -
    empiricalBinaryResidualMean p response j n * empiricalBinaryResidualMean p response ℓ n

/-- The residual covariance is the average product of the centered sample residuals. -/
theorem empiricalBinaryResidualCovariance_eq_centered_average
    {Model : Type*} (p : ℕ → Model → ℝ) (response : ℕ → Model → Bool)
    (j ℓ : Model) (n : ℕ) :
    empiricalBinaryResidualCovariance p response j ℓ n =
      (∑ i ∈ Finset.range n,
        (binaryResidual (p i j) (response i j) - empiricalBinaryResidualMean p response j n) *
        (binaryResidual (p i ℓ) (response i ℓ) - empiricalBinaryResidualMean p response ℓ n)) /
        (n : ℝ) := by
  exact empiricalRowCovariance_eq_centered_average (fun i (_ : Unit) => i)
    (fun i => binaryResidual (p i j) (response i j))
    (fun i => binaryResidual (p i ℓ) (response i ℓ)) n ()

/-- Each diagonal residual sample covariance is a nonnegative centered sample variance. -/
theorem empiricalBinaryResidualCovariance_self_nonneg
    {Model : Type*} (p : ℕ → Model → ℝ) (response : ℕ → Model → Bool)
    (j : Model) (n : ℕ) : 0 ≤ empiricalBinaryResidualCovariance p response j j n := by
  exact empiricalRowCovariance_self_nonneg (fun i (_ : Unit) => i)
    (fun i => binaryResidual (p i j) (response i j)) n ()

/-- An absolute pointwise bound is retained by a nonempty prefix average. -/
theorem abs_prefix_average_le (score : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (C : ℝ)
    (hscore : ∀ i < n, |score i| ≤ C) :
    |(∑ i ∈ Finset.range n, score i) / (n : ℝ)| ≤ C := by
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [abs_div, abs_of_nonneg hnreal.le]
  apply (div_le_iff₀ hnreal).mpr
  calc
    |∑ i ∈ Finset.range n, score i| ≤ ∑ i ∈ Finset.range n, |score i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range n, C :=
      Finset.sum_le_sum fun i hi => hscore i (Finset.mem_range.mp hi)
    _ = C * (n : ℝ) := by simp [mul_comm]

/-- Binary residual means have absolute value at most one. -/
theorem abs_empiricalBinaryResidualMean_le_one
    {Model : Type*} (p : ℕ → Model → ℝ) (response : ℕ → Model → Bool)
    (j : Model) {n : ℕ} (hn : 0 < n)
    (hp : ∀ i < n, ∀ m, 0 ≤ p i m ∧ p i m ≤ 1) :
    |empiricalBinaryResidualMean p response j n| ≤ 1 := by
  apply abs_prefix_average_le _ hn 1
  intro i hi
  exact abs_binaryResidual_le_one _ _ (hp i hi j).1 (hp i hi j).2

/-- Uniform probability error bounds the perturbation of each residual mean. -/
theorem abs_empiricalBinaryResidualMean_sub_le_delta
    {Model : Type*} (p phat : ℕ → Model → ℝ) (response : ℕ → Model → Bool)
    (j : Model) {n : ℕ} (hn : 0 < n) (δ : ℝ)
    (hδ : ∀ i < n, ∀ m, |phat i m - p i m| ≤ δ) :
    |empiricalBinaryResidualMean phat response j n -
      empiricalBinaryResidualMean p response j n| ≤ δ := by
  unfold empiricalBinaryResidualMean
  rw [← sub_div, ← Finset.sum_sub_distrib]
  apply abs_prefix_average_le _ hn δ
  intro i hi
  exact abs_binaryResidual_sub_le_of_abs_prob_sub_le _ _ _ (hδ i hi j)

/--
The source's uniform probability-perturbation inequality applies to each
evaluation prefix, even when the fitted probabilities depend on that prefix.
-/
theorem abs_empiricalBinaryResidualCrossMoment_sub_le_two_delta
    {Model : Type*} (p phat : ℕ → Model → ℝ) (response : ℕ → Model → Bool)
    (j ℓ : Model) {n : ℕ} (hn : 0 < n) (δ : ℝ)
    (hp : ∀ i < n, ∀ m, 0 ≤ p i m ∧ p i m ≤ 1)
    (hphat : ∀ i < n, ∀ m, 0 ≤ phat i m ∧ phat i m ≤ 1)
    (hδ : ∀ i < n, ∀ m, |phat i m - p i m| ≤ δ) :
    |empiricalBinaryResidualCrossMoment phat response j ℓ n -
      empiricalBinaryResidualCrossMoment p response j ℓ n| ≤ 2 * δ := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hfinite := abs_averagePairResidualFunctional_sub_le_two_delta
    (fun i : Fin n => p i.val) (fun i : Fin n => phat i.val) j ℓ
    (fun i m => hp i.val i.isLt m) (fun i m => hphat i.val i.isLt m) δ
    (fun i m => hδ i.val i.isLt m) (fun i : Fin n => response i.val)
  have heq : ∀ q : ℕ → Model → ℝ,
      averagePairResidualFunctional (fun i : Fin n => q i.val) j ℓ
        (fun i : Fin n => response i.val) = empiricalBinaryResidualCrossMoment q response j ℓ n := by
    intro q
    simp only [averagePairResidualFunctional, empiricalBinaryResidualCrossMoment, Fintype.card_fin]
    rw [Fin.sum_univ_eq_sum_range
      (fun i : ℕ => binaryResidual (q i j) (response i j) * binaryResidual (q i ℓ) (response i ℓ)) n]
    rw [div_eq_inv_mul]
  simpa only [heq] using hfinite

/--
Centering preserves uniform fitting stability: the raw cross-moment and the
product of sample means each change by at most `2 * δ`.
-/
theorem abs_empiricalBinaryResidualCovariance_sub_le_four_delta
    {Model : Type*} (p phat : ℕ → Model → ℝ) (response : ℕ → Model → Bool)
    (j ℓ : Model) {n : ℕ} (hn : 0 < n) (δ : ℝ)
    (hp : ∀ i < n, ∀ m, 0 ≤ p i m ∧ p i m ≤ 1)
    (hphat : ∀ i < n, ∀ m, 0 ≤ phat i m ∧ phat i m ≤ 1)
    (hδ : ∀ i < n, ∀ m, |phat i m - p i m| ≤ δ) :
    |empiricalBinaryResidualCovariance phat response j ℓ n -
      empiricalBinaryResidualCovariance p response j ℓ n| ≤ 4 * δ := by
  have hcross := abs_empiricalBinaryResidualCrossMoment_sub_le_two_delta
    p phat response j ℓ hn δ hp hphat hδ
  have hmeans := abs_mul_sub_mul_le_two_delta_of_abs_le_one
    (abs_empiricalBinaryResidualMean_le_one p response j hn hp)
    (abs_empiricalBinaryResidualMean_le_one phat response ℓ hn hphat)
    (abs_empiricalBinaryResidualMean_sub_le_delta p phat response j hn δ hδ)
    (abs_empiricalBinaryResidualMean_sub_le_delta p phat response ℓ hn δ hδ)
  unfold empiricalBinaryResidualCovariance
  calc
    _ = |(empiricalBinaryResidualCrossMoment phat response j ℓ n -
        empiricalBinaryResidualCrossMoment p response j ℓ n) -
        (empiricalBinaryResidualMean phat response j n * empiricalBinaryResidualMean phat response ℓ n -
          empiricalBinaryResidualMean p response j n * empiricalBinaryResidualMean p response ℓ n)| := by
      congr 1
      ring
    _ ≤ _ := abs_sub _ _
    _ ≤ 2 * δ + 2 * δ := add_le_add hcross hmeans
    _ = 4 * δ := by ring

/-- Genuine residual-moment sampling from IID rows, without assuming IID residual scores. -/
theorem ae_empiricalBinaryResidualMoment_tendsto_of_iid
    {Ω Row Model : Type*} [MeasurableSpace Ω] [MeasurableSpace Row]
    {P : Measure Ω} [IsFiniteMeasure P]
    (row : ℕ → Ω → Row) (hrow : Measurable (row 0))
    (p : Row → Model → ℝ) (response : Row → Model → Bool) (j ℓ : Model)
    (hpmeas : ∀ m, Measurable (fun z => p z m))
    (hymeas : ∀ m, Measurable (fun z => response z m))
    (hp : ∀ z m, 0 ≤ p z m ∧ p z m ≤ 1)
    (hindep : Pairwise (fun i k => row i ⟂ᵢ[P] row k))
    (hident : ∀ i, IdentDistrib (row i) (row 0) P P) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n => empiricalBinaryResidualCrossMoment
        (fun i m => p (row i ω) m) (fun i m => response (row i ω) m) j ℓ n)
      atTop (𝓝 (∫ ω, binaryResidual (p (row 0 ω) j) (response (row 0 ω) j) *
        binaryResidual (p (row 0 ω) ℓ) (response (row 0 ω) ℓ) ∂P)) := by
  let x : Row → ℝ := fun z => binaryResidual (p z j) (response z j)
  let y : Row → ℝ := fun z => binaryResidual (p z ℓ) (response z ℓ)
  have hx : Measurable x := measurable_binaryResidual_score _ _ (hpmeas j) (hymeas j)
  have hy : Measurable y := measurable_binaryResidual_score _ _ (hpmeas ℓ) (hymeas ℓ)
  apply ae_empiricalRowMoment_tendsto_of_iid row (fun z => x z * y z) (hx.mul hy)
    _ hindep hident
  apply integrable_rowScore_of_bounded (row 0) hrow (fun z => x z * y z) (hx.mul hy) 1
  intro z
  rw [abs_mul]
  have hxbound := abs_binaryResidual_le_one (p z j) (response z j) (hp z j).1 (hp z j).2
  have hybound := abs_binaryResidual_le_one (p z ℓ) (response z ℓ) (hp z ℓ).1 (hp z ℓ).2
  exact (mul_le_mul hxbound hybound (abs_nonneg _) zero_le_one).trans_eq (mul_one 1)

/-- Vanishing uniform errors transfer a proved oracle limit to an arbitrary fitted sequence. -/
theorem tendsto_of_oracle_limit_and_uniform_perturbation
    {ι : Type*} {l : Filter ι} {oracle fitted error : ι → ℝ} {L : ℝ}
    (horacle : Tendsto oracle l (𝓝 L)) (herror : Tendsto error l (𝓝 0))
    (hbound : ∀ᶠ i in l, |fitted i - oracle i| ≤ 2 * error i) :
    Tendsto fitted l (𝓝 L) := by
  have hdifference : Tendsto (fun i => fitted i - oracle i) l (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    apply squeeze_zero' (Filter.Eventually.of_forall fun _ => abs_nonneg _) hbound
    simpa only [mul_zero] using herror.const_mul 2
  have hsum := hdifference.add horacle
  simpa only [sub_add_cancel, zero_add] using hsum

/--
Uniform consistency for probabilities evaluated on IID rows transfers the
oracle residual-moment strong law to fitted moments. Fitted probabilities are
allowed to depend on the entire evaluation/training sample; their residual
scores are not assumed independent or identically distributed.
-/
theorem ae_fittedBinaryResidualMoment_tendsto_of_uniform_consistency
    {Ω Row Model : Type*} [MeasurableSpace Ω] [MeasurableSpace Row]
    {P : Measure Ω} [IsFiniteMeasure P]
    (row : ℕ → Ω → Row) (hrow : Measurable (row 0))
    (p : Row → Model → ℝ) (response : Row → Model → Bool) (j ℓ : Model)
    (hpmeas : ∀ m, Measurable (fun z => p z m))
    (hymeas : ∀ m, Measurable (fun z => response z m))
    (hp : ∀ z m, 0 ≤ p z m ∧ p z m ≤ 1)
    (hindep : Pairwise (fun i k => row i ⟂ᵢ[P] row k))
    (hident : ∀ i, IdentDistrib (row i) (row 0) P P)
    (phat : ℕ → ℕ → Ω → Model → ℝ) (error : ℕ → Ω → ℝ)
    (hphat : ∀ n ω i, i < n → ∀ m, 0 ≤ phat n i ω m ∧ phat n i ω m ≤ 1)
    (herror : ∀ n ω i, i < n → ∀ m,
      |phat n i ω m - p (row i ω) m| ≤ error n ω)
    (hconsistent : ∀ᵐ ω ∂P, Tendsto (fun n => error n ω) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n => empiricalBinaryResidualCrossMoment (fun i m => phat n i ω m)
        (fun i m => response (row i ω) m) j ℓ n)
      atTop (𝓝 (∫ ω, binaryResidual (p (row 0 ω) j) (response (row 0 ω) j) *
        binaryResidual (p (row 0 ω) ℓ) (response (row 0 ω) ℓ) ∂P)) := by
  have horacle := ae_empiricalBinaryResidualMoment_tendsto_of_iid
    row hrow p response j ℓ hpmeas hymeas hp hindep hident
  filter_upwards [horacle, hconsistent] with ω horacle hconsistent
  apply tendsto_of_oracle_limit_and_uniform_perturbation horacle hconsistent
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact abs_empiricalBinaryResidualCrossMoment_sub_le_two_delta
    (fun i m => p (row i ω) m) (fun i m => phat n i ω m)
    (fun i m => response (row i ω) m) j ℓ hn (error n ω)
    (fun i _hi m => hp (row i ω) m) (fun i hi m => hphat n ω i hi m)
    (fun i hi m => herror n ω i hi m)

/--
Uniformly consistent probabilities on the same IID evaluation sample estimate
centered population residual covariance. The fitted table may depend on every
row of the sample; no independence hypothesis is imposed on fitted scores.
-/
theorem ae_fittedBinaryResidualCovariance_tendsto_of_uniform_consistency
    {Ω Row Model : Type*} [MeasurableSpace Ω] [MeasurableSpace Row]
    {P : Measure Ω} [IsFiniteMeasure P]
    (row : ℕ → Ω → Row) (hrow : Measurable (row 0))
    (p : Row → Model → ℝ) (response : Row → Model → Bool) (j ℓ : Model)
    (hpmeas : ∀ m, Measurable (fun z => p z m))
    (hymeas : ∀ m, Measurable (fun z => response z m))
    (hp : ∀ z m, 0 ≤ p z m ∧ p z m ≤ 1)
    (hindep : Pairwise (fun i k => row i ⟂ᵢ[P] row k))
    (hident : ∀ i, IdentDistrib (row i) (row 0) P P)
    (phat : ℕ → ℕ → Ω → Model → ℝ) (error : ℕ → Ω → ℝ)
    (hphat : ∀ n ω i, i < n → ∀ m, 0 ≤ phat n i ω m ∧ phat n i ω m ≤ 1)
    (herror : ∀ n ω i, i < n → ∀ m,
      |phat n i ω m - p (row i ω) m| ≤ error n ω)
    (hconsistent : ∀ᵐ ω ∂P, Tendsto (fun n => error n ω) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n => empiricalBinaryResidualCovariance (fun i m => phat n i ω m)
        (fun i m => response (row i ω) m) j ℓ n) atTop
      (𝓝 (populationRowCovariance P row
        (fun z => binaryResidual (p z j) (response z j))
        (fun z => binaryResidual (p z ℓ) (response z ℓ)))) := by
  have horacle := ae_empiricalRowCovariance_tendsto_of_bounded_iid row hrow
    (fun z => binaryResidual (p z j) (response z j))
    (fun z => binaryResidual (p z ℓ) (response z ℓ))
    (measurable_binaryResidual_score _ _ (hpmeas j) (hymeas j))
    (measurable_binaryResidual_score _ _ (hpmeas ℓ) (hymeas ℓ))
    (fun z => abs_binaryResidual_le_one _ _ (hp z j).1 (hp z j).2)
    (fun z => abs_binaryResidual_le_one _ _ (hp z ℓ).1 (hp z ℓ).2) hindep hident
  filter_upwards [horacle, hconsistent] with ω horacle hconsistent
  have herror2 : Tendsto (fun n => 2 * error n ω) atTop (𝓝 0) := by
    simpa only [mul_zero] using hconsistent.const_mul 2
  apply tendsto_of_oracle_limit_and_uniform_perturbation horacle herror2
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hbound := abs_empiricalBinaryResidualCovariance_sub_le_four_delta
    (fun i m => p (row i ω) m) (fun i m => phat n i ω m)
    (fun i m => response (row i ω) m) j ℓ hn (error n ω)
    (fun i _hi m => hp (row i ω) m) (fun i hi m => hphat n ω i hi m)
    (fun i hi m => herror n ω i hi m)
  convert hbound using 1
  ring

/-! ## Pearson normalization -/

/-- Pearson normalization of one covariance and two variances. -/
def pearsonFromMoments (covariance varianceX varianceY : ℝ) : ℝ :=
  covariance / Real.sqrt (varianceX * varianceY)

/-- The usual centered empirical Pearson statistic for a pair of row scores. -/
def empiricalRowPearson {Ω Row : Type*}
    (row : ℕ → Ω → Row) (x y : Row → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  pearsonFromMoments (empiricalRowCovariance row x y n ω)
    (empiricalRowCovariance row x x n ω) (empiricalRowCovariance row y y n ω)

/-- The centered Pearson statistic computed from a possibly sample-dependent fitted table. -/
def empiricalBinaryResidualPearson {Model : Type*}
    (p : ℕ → Model → ℝ) (response : ℕ → Model → Bool) (j ℓ : Model) (n : ℕ) : ℝ :=
  pearsonFromMoments (empiricalBinaryResidualCovariance p response j ℓ n)
    (empiricalBinaryResidualCovariance p response j j n)
    (empiricalBinaryResidualCovariance p response ℓ ℓ n)

/-- A common positive variance floor bounds the normalized covariance. -/
theorem abs_pearsonFromMoments_le_of_variance_floor
    {covariance varianceX varianceY v : ℝ} (hv : 0 < v)
    (hX : v ≤ varianceX) (hY : v ≤ varianceY) :
    |pearsonFromMoments covariance varianceX varianceY| ≤ |covariance| / v := by
  have hXpos : 0 < varianceX := hv.trans_le hX
  have hYpos : 0 < varianceY := hv.trans_le hY
  have hprod : v ^ 2 ≤ varianceX * varianceY := by
    simpa only [pow_two] using mul_le_mul hX hY hv.le hXpos.le
  have hsqrt : v ≤ Real.sqrt (varianceX * varianceY) :=
    (Real.le_sqrt hv.le (mul_nonneg hXpos.le hYpos.le)).mpr hprod
  rw [pearsonFromMoments, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact div_le_div_of_nonneg_left (abs_nonneg covariance) hv hsqrt

/-- Vanishing covariance implies vanishing correlation under an eventual positive variance floor. -/
theorem pearsonFromMoments_tendsto_zero_of_variance_floor
    {ι : Type*} {l : Filter ι} {covariance varianceX varianceY : ι → ℝ} {v : ℝ}
    (hcov : Tendsto covariance l (𝓝 0)) (hv : 0 < v)
    (hfloor : ∀ᶠ i in l, v ≤ varianceX i ∧ v ≤ varianceY i) :
    Tendsto (fun i => pearsonFromMoments (covariance i) (varianceX i) (varianceY i)) l (𝓝 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => abs_nonneg _)
    (hfloor.mono fun i hi => abs_pearsonFromMoments_le_of_variance_floor hv hi.1 hi.2)
  simpa only [abs_zero, zero_div] using hcov.abs.div_const v

/-- IID sampling consistently estimates Pearson correlation when population variances are positive. -/
theorem ae_empiricalRowPearson_tendsto_of_bounded_iid
    {Ω Row : Type*} [MeasurableSpace Ω] [MeasurableSpace Row]
    {P : Measure Ω} [IsFiniteMeasure P]
    (row : ℕ → Ω → Row) (hrow : Measurable (row 0)) (x y : Row → ℝ)
    (hx : Measurable x) (hy : Measurable y)
    (hxbound : ∀ z, |x z| ≤ 1) (hybound : ∀ z, |y z| ≤ 1)
    (hindep : Pairwise (fun i j => row i ⟂ᵢ[P] row j))
    (hident : ∀ i, IdentDistrib (row i) (row 0) P P)
    (hvarX : 0 < populationRowCovariance P row x x)
    (hvarY : 0 < populationRowCovariance P row y y) :
    ∀ᵐ ω ∂P, Tendsto (fun n => empiricalRowPearson row x y n ω) atTop
      (𝓝 (pearsonFromMoments (populationRowCovariance P row x y)
        (populationRowCovariance P row x x) (populationRowCovariance P row y y))) := by
  have hc := ae_empiricalRowCovariance_tendsto_of_bounded_iid row hrow x y
    hx hy hxbound hybound hindep hident
  have hX := ae_empiricalRowCovariance_tendsto_of_bounded_iid row hrow x x
    hx hx hxbound hxbound hindep hident
  have hY := ae_empiricalRowCovariance_tendsto_of_bounded_iid row hrow y y
    hy hy hybound hybound hindep hident
  filter_upwards [hc, hX, hY] with ω hc hX hY
  exact hc.div (hX.mul hY).sqrt (ne_of_gt (Real.sqrt_pos.mpr (mul_pos hvarX hvarY)))

/--
Same-sample uniform probability consistency also transfers centered Pearson
correlation when the two fixed population residual variances are positive.
-/
theorem ae_fittedBinaryResidualPearson_tendsto_of_uniform_consistency
    {Ω Row Model : Type*} [MeasurableSpace Ω] [MeasurableSpace Row]
    {P : Measure Ω} [IsFiniteMeasure P]
    (row : ℕ → Ω → Row) (hrow : Measurable (row 0))
    (p : Row → Model → ℝ) (response : Row → Model → Bool) (j ℓ : Model)
    (hpmeas : ∀ m, Measurable (fun z => p z m))
    (hymeas : ∀ m, Measurable (fun z => response z m))
    (hp : ∀ z m, 0 ≤ p z m ∧ p z m ≤ 1)
    (hindep : Pairwise (fun i k => row i ⟂ᵢ[P] row k))
    (hident : ∀ i, IdentDistrib (row i) (row 0) P P)
    (phat : ℕ → ℕ → Ω → Model → ℝ) (error : ℕ → Ω → ℝ)
    (hphat : ∀ n ω i, i < n → ∀ m, 0 ≤ phat n i ω m ∧ phat n i ω m ≤ 1)
    (herror : ∀ n ω i, i < n → ∀ m,
      |phat n i ω m - p (row i ω) m| ≤ error n ω)
    (hconsistent : ∀ᵐ ω ∂P, Tendsto (fun n => error n ω) atTop (𝓝 0))
    (hvarX : 0 < populationRowCovariance P row
      (fun z => binaryResidual (p z j) (response z j))
      (fun z => binaryResidual (p z j) (response z j)))
    (hvarY : 0 < populationRowCovariance P row
      (fun z => binaryResidual (p z ℓ) (response z ℓ))
      (fun z => binaryResidual (p z ℓ) (response z ℓ))) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n => empiricalBinaryResidualPearson (fun i m => phat n i ω m)
        (fun i m => response (row i ω) m) j ℓ n) atTop
      (𝓝 (pearsonFromMoments
        (populationRowCovariance P row
          (fun z => binaryResidual (p z j) (response z j))
          (fun z => binaryResidual (p z ℓ) (response z ℓ)))
        (populationRowCovariance P row
          (fun z => binaryResidual (p z j) (response z j))
          (fun z => binaryResidual (p z j) (response z j)))
        (populationRowCovariance P row
          (fun z => binaryResidual (p z ℓ) (response z ℓ))
          (fun z => binaryResidual (p z ℓ) (response z ℓ))))) := by
  have hc := ae_fittedBinaryResidualCovariance_tendsto_of_uniform_consistency
    row hrow p response j ℓ hpmeas hymeas hp hindep hident phat error hphat herror hconsistent
  have hX := ae_fittedBinaryResidualCovariance_tendsto_of_uniform_consistency
    row hrow p response j j hpmeas hymeas hp hindep hident phat error hphat herror hconsistent
  have hY := ae_fittedBinaryResidualCovariance_tendsto_of_uniform_consistency
    row hrow p response ℓ ℓ hpmeas hymeas hp hindep hident phat error hphat herror hconsistent
  filter_upwards [hc, hX, hY] with ω hc hX hY
  exact hc.div (hX.mul hY).sqrt (ne_of_gt (Real.sqrt_pos.mpr (mul_pos hvarX hvarY)))

/-! ## Sequential sample-size then model-dimension limits -/

/-- Inner sample limits and an outer population limit give a sequential, not a joint, zero limit. -/
theorem sequential_vanishing_of_inner_and_outer_limits
    (f : ℕ → ℕ → ℝ) (population : ℕ → ℝ)
    (hinner : ∀ K, Tendsto (f K) atTop (𝓝 (population K)))
    (houter : Tendsto population atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ K in atTop, ∀ᶠ n in atTop, |f K n| < ε := by
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have hK := (Metric.tendsto_nhds.mp houter) (ε / 2) hhalf
  filter_upwards [hK] with K hK
  have hn := (Metric.tendsto_nhds.mp (hinner K)) (ε / 2) hhalf
  filter_upwards [hn] with n hn
  have htri := abs_add_le (f K n - population K) (population K)
  rw [sub_add_cancel] at htri
  simp only [Real.dist_eq, sub_zero] at hK hn
  linarith

/--
Under one fixed IID evaluation-row model, population covariance tending to zero
is inherited almost surely in the sequential `n → ∞`, then `K → ∞` sense.
No diagonal or triangular-array conclusion is asserted.
-/
theorem ae_sequential_empiricalCovariance_vanishes_of_bounded_iid
    {Ω Row : Type*} [MeasurableSpace Ω] [MeasurableSpace Row]
    {P : Measure Ω} [IsFiniteMeasure P]
    (row : ℕ → Ω → Row) (hrow : Measurable (row 0)) (x y : ℕ → Row → ℝ)
    (hx : ∀ K, Measurable (x K)) (hy : ∀ K, Measurable (y K))
    (hxbound : ∀ K z, |x K z| ≤ 1) (hybound : ∀ K z, |y K z| ≤ 1)
    (hindep : Pairwise (fun i j => row i ⟂ᵢ[P] row j))
    (hident : ∀ i, IdentDistrib (row i) (row 0) P P)
    (hpopulation : Tendsto (fun K => populationRowCovariance P row (x K) (y K)) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ K in atTop, ∀ᶠ n in atTop, |empiricalRowCovariance row (x K) (y K) n ω| < ε := by
  have hall : ∀ᵐ ω ∂P, ∀ K, Tendsto
      (fun n => empiricalRowCovariance row (x K) (y K) n ω) atTop
      (𝓝 (populationRowCovariance P row (x K) (y K))) := by
    rw [ae_all_iff]
    intro K
    exact ae_empiricalRowCovariance_tendsto_of_bounded_iid row hrow (x K) (y K)
      (hx K) (hy K) (hxbound K) (hybound K) hindep hident
  filter_upwards [hall] with ω hall
  exact sequential_vanishing_of_inner_and_outer_limits _ _ hall hpopulation

/--
The oracle population moment's `K → ∞` zero limit is inherited by fitted sample
moments sequentially: first `n → ∞` at each fixed `K`, then `K → ∞`. The only
fitted-estimation assumption is a uniformly vanishing probability error at
each fixed `K`, while the sampling strong law is proved from the IID rows.
-/
theorem ae_sequential_fittedResidualMoment_vanishes_of_iid_and_consistency
    {Ω Row Model : Type*} [MeasurableSpace Ω] [MeasurableSpace Row]
    {P : Measure Ω} [IsFiniteMeasure P]
    (row : ℕ → Ω → Row) (hrow : Measurable (row 0))
    (p : ℕ → Row → Model → ℝ) (response : Row → Model → Bool) (j ℓ : Model)
    (hpmeas : ∀ K m, Measurable (fun z => p K z m))
    (hymeas : ∀ m, Measurable (fun z => response z m))
    (hp : ∀ K z m, 0 ≤ p K z m ∧ p K z m ≤ 1)
    (hindep : Pairwise (fun i k => row i ⟂ᵢ[P] row k))
    (hident : ∀ i, IdentDistrib (row i) (row 0) P P)
    (phat : ℕ → ℕ → ℕ → Ω → Model → ℝ) (error : ℕ → ℕ → Ω → ℝ)
    (hphat : ∀ K n ω i, i < n → ∀ m, 0 ≤ phat K n i ω m ∧ phat K n i ω m ≤ 1)
    (herror : ∀ K n ω i, i < n → ∀ m,
      |phat K n i ω m - p K (row i ω) m| ≤ error K n ω)
    (hconsistent : ∀ K, ∀ᵐ ω ∂P, Tendsto (fun n => error K n ω) atTop (𝓝 0))
    (hpopulation : Tendsto
      (fun K => ∫ ω, binaryResidual (p K (row 0 ω) j) (response (row 0 ω) j) *
        binaryResidual (p K (row 0 ω) ℓ) (response (row 0 ω) ℓ) ∂P) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ᶠ K in atTop, ∀ᶠ n in atTop,
      |empiricalBinaryResidualCrossMoment (fun i m => phat K n i ω m)
        (fun i m => response (row i ω) m) j ℓ n| < ε := by
  have hall : ∀ᵐ ω ∂P, ∀ K, Tendsto
      (fun n => empiricalBinaryResidualCrossMoment (fun i m => phat K n i ω m)
        (fun i m => response (row i ω) m) j ℓ n) atTop
      (𝓝 (∫ ω, binaryResidual (p K (row 0 ω) j) (response (row 0 ω) j) *
        binaryResidual (p K (row 0 ω) ℓ) (response (row 0 ω) ℓ) ∂P)) := by
    rw [ae_all_iff]
    intro K
    exact ae_fittedBinaryResidualMoment_tendsto_of_uniform_consistency
      row hrow (p K) response j ℓ (hpmeas K) hymeas (hp K) hindep hident
      (phat K) (error K) (hphat K) (herror K) (hconsistent K)
  filter_upwards [hall] with ω hall
  exact sequential_vanishing_of_inner_and_outer_limits _ _ hall hpopulation

/--
Centered fitted sample covariance vanishes almost surely in the sequential
`n → ∞`, then `K → ∞` sense whenever the oracle population covariance does.
Uniform probability consistency is required at each fixed model dimension.
-/
theorem ae_sequential_fittedResidualCovariance_vanishes_of_iid_and_consistency
    {Ω Row Model : Type*} [MeasurableSpace Ω] [MeasurableSpace Row]
    {P : Measure Ω} [IsFiniteMeasure P]
    (row : ℕ → Ω → Row) (hrow : Measurable (row 0))
    (p : ℕ → Row → Model → ℝ) (response : Row → Model → Bool) (j ℓ : Model)
    (hpmeas : ∀ K m, Measurable (fun z => p K z m))
    (hymeas : ∀ m, Measurable (fun z => response z m))
    (hp : ∀ K z m, 0 ≤ p K z m ∧ p K z m ≤ 1)
    (hindep : Pairwise (fun i k => row i ⟂ᵢ[P] row k))
    (hident : ∀ i, IdentDistrib (row i) (row 0) P P)
    (phat : ℕ → ℕ → ℕ → Ω → Model → ℝ) (error : ℕ → ℕ → Ω → ℝ)
    (hphat : ∀ K n ω i, i < n → ∀ m, 0 ≤ phat K n i ω m ∧ phat K n i ω m ≤ 1)
    (herror : ∀ K n ω i, i < n → ∀ m,
      |phat K n i ω m - p K (row i ω) m| ≤ error K n ω)
    (hconsistent : ∀ K, ∀ᵐ ω ∂P, Tendsto (fun n => error K n ω) atTop (𝓝 0))
    (hpopulation : Tendsto (fun K => populationRowCovariance P row
      (fun z => binaryResidual (p K z j) (response z j))
      (fun z => binaryResidual (p K z ℓ) (response z ℓ))) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ᶠ K in atTop, ∀ᶠ n in atTop,
      |empiricalBinaryResidualCovariance (fun i m => phat K n i ω m)
        (fun i m => response (row i ω) m) j ℓ n| < ε := by
  have hall : ∀ᵐ ω ∂P, ∀ K, Tendsto
      (fun n => empiricalBinaryResidualCovariance (fun i m => phat K n i ω m)
        (fun i m => response (row i ω) m) j ℓ n) atTop
      (𝓝 (populationRowCovariance P row
        (fun z => binaryResidual (p K z j) (response z j))
        (fun z => binaryResidual (p K z ℓ) (response z ℓ)))) := by
    rw [ae_all_iff]
    intro K
    exact ae_fittedBinaryResidualCovariance_tendsto_of_uniform_consistency
      row hrow (p K) response j ℓ (hpmeas K) hymeas (hp K) hindep hident
      (phat K) (error K) (hphat K) (herror K) (hconsistent K)
  filter_upwards [hall] with ω hall
  exact sequential_vanishing_of_inner_and_outer_limits _ _ hall hpopulation

/--
An eventual positive population variance floor transfers sequential covariance
vanishing to fitted centered Pearson correlation. Both sampling and fitting
limits are taken at fixed `K`; no joint or diagonal limit is asserted.
-/
theorem ae_sequential_fittedResidualPearson_vanishes_of_iid_consistency_and_variance_floor
    {Ω Row Model : Type*} [MeasurableSpace Ω] [MeasurableSpace Row]
    {P : Measure Ω} [IsFiniteMeasure P]
    (row : ℕ → Ω → Row) (hrow : Measurable (row 0))
    (p : ℕ → Row → Model → ℝ) (response : Row → Model → Bool) (j ℓ : Model)
    (hpmeas : ∀ K m, Measurable (fun z => p K z m))
    (hymeas : ∀ m, Measurable (fun z => response z m))
    (hp : ∀ K z m, 0 ≤ p K z m ∧ p K z m ≤ 1)
    (hindep : Pairwise (fun i k => row i ⟂ᵢ[P] row k))
    (hident : ∀ i, IdentDistrib (row i) (row 0) P P)
    (phat : ℕ → ℕ → ℕ → Ω → Model → ℝ) (error : ℕ → ℕ → Ω → ℝ)
    (hphat : ∀ K n ω i, i < n → ∀ m, 0 ≤ phat K n i ω m ∧ phat K n i ω m ≤ 1)
    (herror : ∀ K n ω i, i < n → ∀ m,
      |phat K n i ω m - p K (row i ω) m| ≤ error K n ω)
    (hconsistent : ∀ K, ∀ᵐ ω ∂P, Tendsto (fun n => error K n ω) atTop (𝓝 0))
    (hpopulation : Tendsto (fun K => populationRowCovariance P row
      (fun z => binaryResidual (p K z j) (response z j))
      (fun z => binaryResidual (p K z ℓ) (response z ℓ))) atTop (𝓝 0))
    (v : ℝ) (hv : 0 < v)
    (hfloor : ∀ᶠ K in atTop,
      v ≤ populationRowCovariance P row
        (fun z => binaryResidual (p K z j) (response z j))
        (fun z => binaryResidual (p K z j) (response z j)) ∧
      v ≤ populationRowCovariance P row
        (fun z => binaryResidual (p K z ℓ) (response z ℓ))
        (fun z => binaryResidual (p K z ℓ) (response z ℓ))) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ᶠ K in atTop, ∀ᶠ n in atTop,
      |empiricalBinaryResidualPearson (fun i m => phat K n i ω m)
        (fun i m => response (row i ω) m) j ℓ n| < ε := by
  have hcov := ae_sequential_fittedResidualCovariance_vanishes_of_iid_and_consistency
    row hrow p response j ℓ hpmeas hymeas hp hindep hident
    phat error hphat herror hconsistent hpopulation
  have hvars : ∀ᵐ ω ∂P, ∀ K,
      Tendsto (fun n => empiricalBinaryResidualCovariance (fun i m => phat K n i ω m)
        (fun i m => response (row i ω) m) j j n) atTop
        (𝓝 (populationRowCovariance P row
          (fun z => binaryResidual (p K z j) (response z j))
          (fun z => binaryResidual (p K z j) (response z j)))) ∧
      Tendsto (fun n => empiricalBinaryResidualCovariance (fun i m => phat K n i ω m)
        (fun i m => response (row i ω) m) ℓ ℓ n) atTop
        (𝓝 (populationRowCovariance P row
          (fun z => binaryResidual (p K z ℓ) (response z ℓ))
          (fun z => binaryResidual (p K z ℓ) (response z ℓ)))) := by
    rw [ae_all_iff]
    intro K
    exact (ae_fittedBinaryResidualCovariance_tendsto_of_uniform_consistency
      row hrow (p K) response j j (hpmeas K) hymeas (hp K) hindep hident
      (phat K) (error K) (hphat K) (herror K) (hconsistent K)).and
      (ae_fittedBinaryResidualCovariance_tendsto_of_uniform_consistency
        row hrow (p K) response ℓ ℓ (hpmeas K) hymeas (hp K) hindep hident
        (phat K) (error K) (hphat K) (herror K) (hconsistent K))
  filter_upwards [hcov, hvars] with ω hcov hvars
  intro ε hε
  have hsmall := hcov (ε * (v / 2)) (mul_pos hε (half_pos hv))
  filter_upwards [hsmall, hfloor] with K hsmall hfloor
  have hX := (hvars K).1.eventually (eventually_ge_nhds
    (by linarith [hfloor.1] : v / 2 < populationRowCovariance P row
      (fun z => binaryResidual (p K z j) (response z j))
      (fun z => binaryResidual (p K z j) (response z j))))
  have hY := (hvars K).2.eventually (eventually_ge_nhds
    (by linarith [hfloor.2] : v / 2 < populationRowCovariance P row
      (fun z => binaryResidual (p K z ℓ) (response z ℓ))
      (fun z => binaryResidual (p K z ℓ) (response z ℓ))))
  filter_upwards [hsmall, hX, hY] with n hsmall hX hY
  exact (abs_pearsonFromMoments_le_of_variance_floor
    (covariance := empiricalBinaryResidualCovariance (fun i m => phat K n i ω m)
      (fun i m => response (row i ω) m) j ℓ n)
    (half_pos hv) hX hY).trans_lt ((div_lt_iff₀ (half_pos hv)).mpr hsmall)

/-! ## A fixed binary row law with degenerating residual variance -/

/-- One fixed fair response bit, shared by the two model coordinates in the example. -/
def degeneratingResidualLaw : PMF Bool := realBernoulliPMF (1 / 2) (by norm_num) (by norm_num)

/-- A positive residual scale tending to zero. -/
def degeneratingResidualScale (K : ℕ) : ℝ := ((K : ℝ) + 2)⁻¹

theorem degeneratingResidualScale_pos (K : ℕ) : 0 < degeneratingResidualScale K := by
  unfold degeneratingResidualScale
  positivity

theorem degeneratingResidualScale_lt_one (K : ℕ) : degeneratingResidualScale K < 1 := by
  unfold degeneratingResidualScale
  apply (inv_lt_one₀ (by positivity : 0 < (K : ℝ) + 2)).mpr
  linarith [Nat.cast_nonneg (α := ℝ) K]

/-- Increasingly sharp strictly interior oracle probabilities on the binary item feature. -/
def degeneratingOracleProbability (K : ℕ) (b : Bool) : ℝ :=
  if b then 1 - degeneratingResidualScale K else degeneratingResidualScale K

theorem degeneratingOracleProbability_strictlyInterior (K : ℕ) (b : Bool) :
    0 < degeneratingOracleProbability K b ∧ degeneratingOracleProbability K b < 1 := by
  have hp := degeneratingResidualScale_pos K
  have hlt := degeneratingResidualScale_lt_one K
  cases b <;> simp only [degeneratingOracleProbability, Bool.false_eq_true,
    if_false, if_true] <;> constructor <;> linarith

/-- Both model residuals are this same centered score on the common binary row. -/
def degeneratingResidualScore (K : ℕ) (b : Bool) : ℝ :=
  binaryResidual (degeneratingOracleProbability K b) b

/-- The actual centered covariance/variance under the fixed finite response law. -/
def degeneratingResidualCovariance (K : ℕ) : ℝ :=
  AppliedModelingLib.pmfExp degeneratingResidualLaw (fun b => degeneratingResidualScore K b ^ 2) -
    (AppliedModelingLib.pmfExp degeneratingResidualLaw (degeneratingResidualScore K)) ^ 2

/-- The concrete finite-law computation: zero mean and squared residual scale. -/
theorem degeneratingResidualCovariance_eq_scale_sq (K : ℕ) :
    degeneratingResidualCovariance K = degeneratingResidualScale K ^ 2 := by
  simp [degeneratingResidualCovariance, AppliedModelingLib.pmfExp,
    degeneratingResidualLaw, degeneratingResidualScore, binaryResidual, boolAsReal,
    degeneratingOracleProbability]
  ring

theorem degeneratingResidualCovariance_pos (K : ℕ) : 0 < degeneratingResidualCovariance K := by
  rw [degeneratingResidualCovariance_eq_scale_sq]
  exact sq_pos_of_pos (degeneratingResidualScale_pos K)

theorem degeneratingResidualScale_tendsto_zero :
    Tendsto degeneratingResidualScale atTop (𝓝 0) := by
  change Tendsto (fun K : ℕ => ((K : ℝ) + 2)⁻¹) atTop (𝓝 0)
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat,
    one_div] using
    (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp (tendsto_add_atTop_nat 2)

theorem degeneratingResidualCovariance_tendsto_zero :
    Tendsto degeneratingResidualCovariance atTop (𝓝 0) := by
  change Tendsto (fun K => degeneratingResidualCovariance K) atTop (𝓝 0)
  have hsq := degeneratingResidualScale_tendsto_zero.pow 2
  simpa only [degeneratingResidualCovariance_eq_scale_sq, zero_pow (by decide : 2 ≠ 0)] using hsq

/-- Despite exact oracle/fitted probabilities and positive variance at every `K`, correlation is one. -/
theorem degeneratingResidualPearson_eq_one (K : ℕ) :
    pearsonFromMoments (degeneratingResidualCovariance K)
      (degeneratingResidualCovariance K) (degeneratingResidualCovariance K) = 1 := by
  have hv := degeneratingResidualCovariance_pos K
  rw [pearsonFromMoments, ← pow_two, Real.sqrt_sq hv.le, div_self (ne_of_gt hv)]

/-- Covariance tending to zero and exact fitted-oracle agreement do not force correlation to zero. -/
theorem vanishing_covariance_does_not_force_vanishing_Pearson :
    Tendsto degeneratingResidualCovariance atTop (𝓝 0) ∧
      (∀ K, 0 < degeneratingResidualCovariance K) ∧
      (∀ K b, 0 < degeneratingOracleProbability K b ∧ degeneratingOracleProbability K b < 1) ∧
      ¬Tendsto (fun K => pearsonFromMoments (degeneratingResidualCovariance K)
        (degeneratingResidualCovariance K) (degeneratingResidualCovariance K)) atTop (𝓝 0) := by
  refine ⟨degeneratingResidualCovariance_tendsto_zero, degeneratingResidualCovariance_pos,
    degeneratingOracleProbability_strictlyInterior, ?_⟩
  intro hzero
  have hone : Tendsto (fun K => pearsonFromMoments (degeneratingResidualCovariance K)
      (degeneratingResidualCovariance K) (degeneratingResidualCovariance K)) atTop (𝓝 1) := by
    simpa only [degeneratingResidualPearson_eq_one] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  have heq := tendsto_nhds_unique hone hzero
  norm_num at heq

/-- An explicit uniformly consistent fitted family still exhibits the normalization obstruction. -/
theorem consistent_probabilities_and_vanishing_covariance_do_not_force_vanishing_Pearson :
    ∃ fitted : ℕ → Bool → ℝ,
      (∀ K b, fitted K b = degeneratingOracleProbability K b) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ K in atTop, ∀ b : Bool,
        |fitted K b - degeneratingOracleProbability K b| < ε) ∧
      Tendsto degeneratingResidualCovariance atTop (𝓝 0) ∧
      ¬Tendsto (fun K => pearsonFromMoments (degeneratingResidualCovariance K)
        (degeneratingResidualCovariance K) (degeneratingResidualCovariance K)) atTop (𝓝 0) := by
  refine ⟨degeneratingOracleProbability, fun _ _ => rfl, ?_,
    degeneratingResidualCovariance_tendsto_zero, ?_⟩
  · intro ε hε
    exact Filter.Eventually.of_forall fun _K _b => by simpa only [sub_self, abs_zero] using hε
  · exact vanishing_covariance_does_not_force_vanishing_Pearson.2.2.2

end

end JGR26SubjectivityMonoculture
