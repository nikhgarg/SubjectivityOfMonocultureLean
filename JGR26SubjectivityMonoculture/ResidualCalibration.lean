import JGR26SubjectivityMonoculture.MainTheorems
import AppliedModelingLib.Foundations.Probability.RenewalReward

/-!
# What residual demeaning does and does not remove

The expectation identity in Proposition 7 is linearity of expectation. Its
finite-sample centering step removes only the mean of the calibration error.
The exact decomposition below preserves the item-dependent remainder.

The sampling limit uses the shared library's existing real IID strong-law
wrapper, which is backed by Mathlib's Etemadi theorem. It is not inferred from
IID response rows when the fitted probabilities can depend on the whole sample.
-/

namespace JGR26SubjectivityMonoculture

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology ProbabilityTheory

noncomputable section

variable {Item Model : Type*} [Fintype Item]

/-- Demeaning a sum is the sum of the two demeaned components. -/
theorem debiasedResidual_add (a b : Item → Model → ℝ) (i : Item) (j : Model) :
    debiasedResidual (fun i j => a i j + b i j) i j =
      debiasedResidual a i j + debiasedResidual b i j := by
  simp only [debiasedResidual, meanResidual, Finset.sum_add_distrib]
  ring

/-- Exactly the true centered fluctuation plus the centered calibration error remains. -/
theorem debiasedResidual_calibration_decomposition
    (response truth fitted : Item → Model → ℝ) (i : Item) (j : Model) :
    debiasedResidual (fun i j => response i j - fitted i j) i j =
      debiasedResidual (fun i j => response i j - truth i j) i j +
        debiasedResidual (fun i j => truth i j - fitted i j) i j := by
  have heq : (fun i j => response i j - fitted i j) =
      (fun i j => (response i j - truth i j) + (truth i j - fitted i j)) := by
    funext i j
    ring
  rw [heq, debiasedResidual_add]

/-- A common model-specific calibration shift is removed exactly by demeaning. -/
theorem debiasedResidual_eq_true_centered_of_common_calibration
    [Nonempty Item] (response truth fitted : Item → Model → ℝ) (bias : Model → ℝ)
    (hcommon : ∀ i j, truth i j - fitted i j = bias j) (i : Item) (j : Model) :
    debiasedResidual (fun i j => response i j - fitted i j) i j =
      debiasedResidual (fun i j => response i j - truth i j) i j := by
  rw [debiasedResidual_calibration_decomposition response truth fitted]
  have hcard : (Fintype.card Item : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [debiasedResidual, meanResidual, hcommon, Finset.sum_const,
    nsmul_eq_mul, hcard]

/-- For a finite law, the mean residual equals the mean calibration error. -/
theorem finiteLawExpectation_residual_eq_calibration
    {Ω : Type*} [Fintype Ω] (law : FiniteLaw Ω)
    (response truth fitted : Ω → ℝ)
    (htruth : finiteLawExpectation law response = finiteLawExpectation law truth) :
    finiteLawExpectation law (fun ω => response ω - fitted ω) =
      finiteLawExpectation law (fun ω => truth ω - fitted ω) := by
  simp only [finiteLawExpectation, mul_sub, Finset.sum_sub_distrib] at htruth ⊢
  rw [htruth]

/-- Under a genuine IID residual-row model, the sample mean estimates its expectation. -/
theorem ae_residualMean_tendsto_of_iid
    {Ω : Type*} [MeasurableSpace Ω] {law : Measure Ω}
    (residual : ℕ → Ω → ℝ) (hint : Integrable (residual 0) law)
    (hindep : Pairwise (fun i j => residual i ⟂ᵢ[law] residual j))
    (hident : ∀ i, IdentDistrib (residual i) (residual 0) law law) :
    ∀ᵐ ω ∂law, Tendsto
      (fun n : ℕ => (∑ i ∈ Finset.range n, residual i ω) / n)
      atTop (𝓝 (∫ ω, residual 0 ω ∂law)) :=
  AppliedModelingLib.ae_tendsto_empirical_mean_real_of_iid residual hint hindep hident

/-- Arbitrary fitted probabilities cancel from the difference of empirical mean errors. -/
theorem rawResidualMean_sub_averageCalibration
    (response fitted : ℕ → ℝ) (truth : ℝ) {n : ℕ} (hn : 0 < n) :
    ((∑ i ∈ Finset.range n, (response i - fitted i)) / n) -
        ((∑ i ∈ Finset.range n, (truth - fitted i)) / n) =
      ((∑ i ∈ Finset.range n, response i) / n) - truth := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp
  ring

/-- With arbitrary sample-dependent estimates, the residual mean tracks empirical average bias.

Only the response sequence is IID. No independence, consistency, or IID
condition is imposed on `fitted n i`, which may use the entire observed sample.
-/
theorem ae_rawResidualMean_sub_averageCalibration_tendsto_zero
    {Ω : Type*} [MeasurableSpace Ω] {law : Measure Ω}
    (response : ℕ → Ω → ℝ) (fitted : ℕ → ℕ → Ω → ℝ) (truth : ℝ)
    (hint : Integrable (response 0) law)
    (hindep : Pairwise (fun i j => response i ⟂ᵢ[law] response j))
    (hident : ∀ i, IdentDistrib (response i) (response 0) law law)
    (hmean : (∫ ω, response 0 ω ∂law) = truth) :
    ∀ᵐ ω ∂law, Tendsto
      (fun n : ℕ =>
        ((∑ i ∈ Finset.range n, (response i ω - fitted n i ω)) / n) -
          ((∑ i ∈ Finset.range n, (truth - fitted n i ω)) / n))
      atTop (𝓝 0) := by
  filter_upwards [AppliedModelingLib.ae_tendsto_empirical_mean_real_of_iid
    response hint hindep hident] with ω hω
  rw [hmean] at hω
  have hlimit := hω.sub_const truth
  simp only [sub_self] at hlimit
  apply hlimit.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact (rawResidualMean_sub_averageCalibration
    (fun i => response i ω) (fun i => fitted n i ω) truth hn).symm

/-! ## A bounded, genuine row-law counterexample to complete bias removal -/

/-- Two independent response bits and an independent item feature. -/
abbrev CalibrationExampleOutcome := (Bool × Bool) × Bool

/-- All eight possible row/feature realizations are equally likely. -/
def calibrationExampleLaw : FiniteLaw CalibrationExampleOutcome :=
  finiteLawOfPMF (AppliedModelingLib.uniformPMF CalibrationExampleOutcome)

/-- A predictor uses an irrelevant item feature, identically for both models. -/
def calibrationExampleFitted (ω : CalibrationExampleOutcome) : ℝ :=
  if ω.2 then 3 / 4 else 1 / 4

/-- The two independent models have true success probabilities one half. -/
def calibrationExampleResponse (ω : CalibrationExampleOutcome) (j : Fin 2) : ℝ :=
  if (if j = 0 then ω.1.1 else ω.1.2) then 1 else 0

theorem calibrationExampleFitted_strict_probability (ω : CalibrationExampleOutcome) :
    0 < calibrationExampleFitted ω ∧ calibrationExampleFitted ω < 1 := by
  cases h : ω.2 <;> norm_num [calibrationExampleFitted, h]

theorem calibrationExample_responseMean_half (j : Fin 2) :
    finiteLawExpectation calibrationExampleLaw (fun ω => calibrationExampleResponse ω j) = 1 / 2 := by
  fin_cases j <;>
    norm_num [calibrationExampleLaw, finiteLawOfPMF, finiteLawExpectation,
      AppliedModelingLib.uniformPMF_apply_toReal, calibrationExampleResponse,
      Fintype.sum_prod_type, Fintype.sum_bool]

/-- Mean calibration error is zero despite a nonzero item-dependent error. -/
theorem calibrationExample_calibrationMean_zero :
    finiteLawExpectation calibrationExampleLaw (fun ω => (1 / 2 : ℝ) - calibrationExampleFitted ω) = 0 := by
  norm_num [calibrationExampleLaw, finiteLawOfPMF, finiteLawExpectation,
    AppliedModelingLib.uniformPMF_apply_toReal, calibrationExampleFitted,
    Fintype.sum_prod_type, Fintype.sum_bool]

/-- True centered fluctuations of the independent models have zero covariance. -/
theorem calibrationExample_trueResidual_cross_zero :
    finiteLawExpectation calibrationExampleLaw
      (fun ω => (calibrationExampleResponse ω 0 - 1 / 2) *
        (calibrationExampleResponse ω 1 - 1 / 2)) = 0 := by
  norm_num [calibrationExampleLaw, finiteLawOfPMF, finiteLawExpectation,
    AppliedModelingLib.uniformPMF_apply_toReal, calibrationExampleResponse,
    Fintype.sum_prod_type, Fintype.sum_bool]

/-- Demeaning cannot remove this positive covariance: both raw residual means are zero. -/
theorem calibrationExample_fittedResidual_cross_sixteenth :
    finiteLawExpectation calibrationExampleLaw
      (fun ω => (calibrationExampleResponse ω 0 - calibrationExampleFitted ω) *
        (calibrationExampleResponse ω 1 - calibrationExampleFitted ω)) = 1 / 16 := by
  norm_num [calibrationExampleLaw, finiteLawOfPMF, finiteLawExpectation,
    AppliedModelingLib.uniformPMF_apply_toReal, calibrationExampleResponse,
    calibrationExampleFitted, Fintype.sum_prod_type, Fintype.sum_bool]

theorem calibrationExample_residualMean_zero (j : Fin 2) :
    finiteLawExpectation calibrationExampleLaw
      (fun ω => calibrationExampleResponse ω j - calibrationExampleFitted ω) = 0 := by
  rw [finiteLawExpectation_residual_eq_calibration calibrationExampleLaw
    (fun ω => calibrationExampleResponse ω j) (fun _ => (1 / 2 : ℝ))
    calibrationExampleFitted]
  · exact calibrationExample_calibrationMean_zero
  · rw [calibrationExample_responseMean_half]
    norm_num [calibrationExampleLaw, finiteLawOfPMF, finiteLawExpectation,
      AppliedModelingLib.uniformPMF_apply_toReal, Fintype.sum_prod_type, Fintype.sum_bool]

/-- The response bits really are independent fair bits under this row law. -/
theorem calibrationExample_responseJoint_quarter (b c : Bool) :
    finiteLawExpectation calibrationExampleLaw
      (fun ω => if ω.1.1 = b ∧ ω.1.2 = c then (1 : ℝ) else 0) = 1 / 4 := by
  cases b <;> cases c <;>
    norm_num [calibrationExampleLaw, finiteLawOfPMF, finiteLawExpectation,
      AppliedModelingLib.uniformPMF_apply_toReal, Fintype.sum_prod_type, Fintype.sum_bool]

theorem calibrationExample_fittedResidual_variance (j : Fin 2) :
    finiteLawExpectation calibrationExampleLaw
      (fun ω => (calibrationExampleResponse ω j - calibrationExampleFitted ω) ^ 2) = 5 / 16 := by
  fin_cases j <;>
    norm_num [calibrationExampleLaw, finiteLawOfPMF, finiteLawExpectation,
      AppliedModelingLib.uniformPMF_apply_toReal, calibrationExampleResponse,
      calibrationExampleFitted, Fintype.sum_prod_type, Fintype.sum_bool]

/-- The fitted residual population correlation is one fifth, not zero. -/
theorem calibrationExample_fittedResidual_correlation :
    finiteLawExpectation calibrationExampleLaw
      (fun ω => (calibrationExampleResponse ω 0 - calibrationExampleFitted ω) *
        (calibrationExampleResponse ω 1 - calibrationExampleFitted ω)) /
      Real.sqrt (finiteLawExpectation calibrationExampleLaw
          (fun ω => (calibrationExampleResponse ω 0 - calibrationExampleFitted ω) ^ 2) *
        finiteLawExpectation calibrationExampleLaw
          (fun ω => (calibrationExampleResponse ω 1 - calibrationExampleFitted ω) ^ 2)) = 1 / 5 := by
  rw [calibrationExample_fittedResidual_cross_sixteenth,
    calibrationExample_fittedResidual_variance, calibrationExample_fittedResidual_variance]
  norm_num [Real.sqrt_mul_self]

end

end JGR26SubjectivityMonoculture
