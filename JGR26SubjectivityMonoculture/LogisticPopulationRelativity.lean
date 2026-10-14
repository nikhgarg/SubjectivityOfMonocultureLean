import JGR26SubjectivityMonoculture.PopulationRelativity
import Mathlib.Analysis.SpecialFunctions.Sigmoid

/-!
# Population relativity for a strictly interior logistic rank-one null

The fixed link is `f(u,v) = sigmoid(u*v)`, which is smooth on all real factors
and always takes values strictly between zero and one. The fixed discrepancy
is the sum of squared differences of inverse-link success probabilities.
Applying the logistic link to the two-by-two identity truth preserves the
exact rank-one squared-loss obstruction in inverse-link coordinates.

This is an existential witness for a nondegenerate fixed link/discrepancy,
not a universal claim for every discrepancy (which would include `D = 0`).

The foundational sigmoid API is the existing Apache-2.0 Mathlib dependency,
`v4.30.0-rc2`, commit `5450b53e5ddc75d46418fabb605edbf36bd0beb6`:
<https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/SpecialFunctions/Sigmoid.lean>.
-/

namespace JGR26SubjectivityMonoculture

open scoped BigOperators ContDiff

noncomputable section

/-- The inverse logistic link, written in the source-compatible inverse-odds form. -/
def logisticLogit (p : ℝ) : ℝ := -Real.log (p⁻¹ - 1)

@[simp]
theorem logisticLogit_sigmoid (x : ℝ) : logisticLogit (Real.sigmoid x) = x := by
  simp [logisticLogit, Real.sigmoid_def, Real.log_exp]

theorem sigmoid_logisticLogit {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    Real.sigmoid (logisticLogit p) = p := by
  have hpos : 0 < p⁻¹ - 1 := by
    rw [sub_pos, one_lt_inv_iff₀]
    exact ⟨hp0, hp1⟩
  simp [logisticLogit, Real.sigmoid_def, Real.exp_log hpos]

/-- One fixed rank-one logistic link, defined for every pair of real factors. -/
def logisticBilinearLink (z : ℝ × ℝ) : ℝ := Real.sigmoid (z.1 * z.2)

theorem logisticBilinearLink_strictlyInterior (z : ℝ × ℝ) :
    0 < logisticBilinearLink z ∧ logisticBilinearLink z < 1 :=
  ⟨Real.sigmoid_pos _, Real.sigmoid_lt_one _⟩

theorem logisticBilinearLink_smooth : ContDiff ℝ ω logisticBilinearLink := by
  exact contDiff_sigmoid.comp (contDiff_fst.mul contDiff_snd)

/-- Inverse-link squared discrepancy between two probability tables. -/
def inverseLinkSquaredDiscrepancy
    {Item Model : Type*} [Fintype Item] [Fintype Model]
    (p q : Item → Model → ℝ) : ℝ :=
  ∑ i : Item, ∑ j : Model, (logisticLogit (q i j) - logisticLogit (p i j)) ^ 2

theorem inverseLinkSquaredDiscrepancy_nonneg
    {Item Model : Type*} [Fintype Item] [Fintype Model]
    (p q : Item → Model → ℝ) : 0 ≤ inverseLinkSquaredDiscrepancy p q := by
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

@[simp]
theorem inverseLinkSquaredDiscrepancy_self
    {Item Model : Type*} [Fintype Item] [Fintype Model]
    (p : Item → Model → ℝ) : inverseLinkSquaredDiscrepancy p p = 0 := by
  simp [inverseLinkSquaredDiscrepancy]

/-- Strictly interior truth probabilities, with identity logits. -/
def logisticTwoItemTruth (i j : Fin 2) : ℝ := Real.sigmoid (twoItemTruth i j)

/-- Logistic rank-one null probabilities for arbitrary real factors. -/
def logisticRankOnePrediction (U V : Fin 2 → ℝ) (i j : Fin 2) : ℝ :=
  Real.sigmoid (rankOnePrediction U V i j)

theorem logisticTwoItemTruth_strictlyInterior (i j : Fin 2) :
    0 < logisticTwoItemTruth i j ∧ logisticTwoItemTruth i j < 1 :=
  ⟨Real.sigmoid_pos _, Real.sigmoid_lt_one _⟩

theorem logisticRankOnePrediction_strictlyInterior (U V : Fin 2 → ℝ) (i j : Fin 2) :
    0 < logisticRankOnePrediction U V i j ∧ logisticRankOnePrediction U V i j < 1 :=
  ⟨Real.sigmoid_pos _, Real.sigmoid_lt_one _⟩

/-- The full-population logistic discrepancy is exactly the existing inverse-coordinate loss. -/
theorem logisticTwoItemDiscrepancy_eq_squaredFitLoss (U V : Fin 2 → ℝ) :
    inverseLinkSquaredDiscrepancy logisticTwoItemTruth (logisticRankOnePrediction U V) =
      twoItemSquaredFitLoss U V := by
  simp only [inverseLinkSquaredDiscrepancy, logisticTwoItemTruth, logisticRankOnePrediction,
    logisticLogit_sigmoid, twoItemSquaredFitLoss]

theorem logisticFirstCoordinate_discrepancy_eq_one :
    inverseLinkSquaredDiscrepancy logisticTwoItemTruth
      (logisticRankOnePrediction firstCoordinateFactor firstCoordinateFactor) = 1 := by
  rw [logisticTwoItemDiscrepancy_eq_squaredFitLoss]
  norm_num [twoItemSquaredFitLoss, rankOnePrediction, firstCoordinateFactor,
    twoItemTruth, Fin.sum_univ_two]

/-- The displayed full fit minimizes over all real factors, with no probability feasibility guard. -/
theorem logisticFirstCoordinate_is_global_minimizer :
    ∀ U V : Fin 2 → ℝ,
      inverseLinkSquaredDiscrepancy logisticTwoItemTruth
        (logisticRankOnePrediction firstCoordinateFactor firstCoordinateFactor) ≤
      inverseLinkSquaredDiscrepancy logisticTwoItemTruth (logisticRankOnePrediction U V) := by
  intro U V
  rw [logisticFirstCoordinate_discrepancy_eq_one, logisticTwoItemDiscrepancy_eq_squaredFitLoss]
  exact one_le_twoItemSquaredFitLoss U V

/-- Restricting the truth to the second item retains the same logistic probabilities. -/
def restrictedLogisticTruth (_i : Unit) (j : Fin 2) : ℝ := logisticTwoItemTruth 1 j

/-- All scalar item-factor candidates for the restricted one-item population. -/
def restrictedLogisticPrediction (u : ℝ) (V : Fin 2 → ℝ) (_i : Unit) (j : Fin 2) : ℝ :=
  Real.sigmoid (u * V j)

theorem restrictedLogisticDiscrepancy_eq_squaredFitLoss (u : ℝ) (V : Fin 2 → ℝ) :
    inverseLinkSquaredDiscrepancy restrictedLogisticTruth (restrictedLogisticPrediction u V) =
      oneItemSquaredFitLoss 1 u V := by
  simp [inverseLinkSquaredDiscrepancy, restrictedLogisticTruth, restrictedLogisticPrediction,
    logisticTwoItemTruth, logisticLogit_sigmoid, oneItemSquaredFitLoss]

theorem logisticSecondCoordinate_discrepancy_eq_zero :
    inverseLinkSquaredDiscrepancy restrictedLogisticTruth
      (restrictedLogisticPrediction 1 secondCoordinateFactor) = 0 := by
  rw [restrictedLogisticDiscrepancy_eq_squaredFitLoss]
  norm_num [oneItemSquaredFitLoss, secondCoordinateFactor, twoItemTruth, Fin.sum_univ_two]

/-- The restricted fit reproduces every truth success probability, not merely one coordinate. -/
theorem restrictedLogisticPrediction_secondCoordinate_eq_truth :
    restrictedLogisticPrediction 1 secondCoordinateFactor = restrictedLogisticTruth := by
  funext i j
  fin_cases j <;>
    simp [restrictedLogisticPrediction, restrictedLogisticTruth, logisticTwoItemTruth,
      secondCoordinateFactor, twoItemTruth]

/-- The restricted optimizer is an exact fit and minimizes over all real factors. -/
theorem logisticSecondCoordinate_is_restricted_minimizer :
    ∀ u : ℝ, ∀ V : Fin 2 → ℝ,
      inverseLinkSquaredDiscrepancy restrictedLogisticTruth
        (restrictedLogisticPrediction 1 secondCoordinateFactor) ≤
      inverseLinkSquaredDiscrepancy restrictedLogisticTruth (restrictedLogisticPrediction u V) := by
  intro u V
  rw [logisticSecondCoordinate_discrepancy_eq_zero]
  exact inverseLinkSquaredDiscrepancy_nonneg _ _

theorem logisticPopulationRelativity_prediction_mismatch :
    logisticRankOnePrediction firstCoordinateFactor firstCoordinateFactor 1 1 ≠
      restrictedLogisticPrediction 1 secondCoordinateFactor () 1 := by
  intro heq
  have hraw := Real.sigmoid_injective heq
  norm_num [logisticRankOnePrediction, restrictedLogisticPrediction,
    rankOnePrediction, firstCoordinateFactor, secondCoordinateFactor] at hraw

/-- A true smooth logistic witness for population-dependent null predictions. -/
theorem populationRelativity_logistic_rankOne_witness :
    ContDiff ℝ ω logisticBilinearLink ∧
    (∀ z : ℝ × ℝ, 0 < logisticBilinearLink z ∧ logisticBilinearLink z < 1) ∧
    (∀ U V : Fin 2 → ℝ,
      inverseLinkSquaredDiscrepancy logisticTwoItemTruth
        (logisticRankOnePrediction firstCoordinateFactor firstCoordinateFactor) ≤
      inverseLinkSquaredDiscrepancy logisticTwoItemTruth (logisticRankOnePrediction U V)) ∧
    (∀ u : ℝ, ∀ V : Fin 2 → ℝ,
      inverseLinkSquaredDiscrepancy restrictedLogisticTruth
        (restrictedLogisticPrediction 1 secondCoordinateFactor) ≤
      inverseLinkSquaredDiscrepancy restrictedLogisticTruth (restrictedLogisticPrediction u V)) ∧
    logisticRankOnePrediction firstCoordinateFactor firstCoordinateFactor 1 1 ≠
      restrictedLogisticPrediction 1 secondCoordinateFactor () 1 := by
  exact ⟨logisticBilinearLink_smooth, logisticBilinearLink_strictlyInterior,
    logisticFirstCoordinate_is_global_minimizer,
    logisticSecondCoordinate_is_restricted_minimizer,
    logisticPopulationRelativity_prediction_mismatch⟩

/-! ## Actual finite response laws and their success marginals -/

/-- The success probability of one response cell in an actual finite response law. -/
def responseSuccessMarginal
    {Item Model : Type*} [Fintype Item] [Fintype Model]
    [DecidableEq Item] [DecidableEq Model]
    (μ : PMF (Item → Model → Bool)) (i : Item) (j : Model) : ℝ :=
  AppliedModelingLib.pmfExp μ (fun response => boolAsReal (response i j))

/-- The same fixed inverse-link discrepancy, now evaluated on law success marginals. -/
def inverseLinkMarginalSquaredDiscrepancy
    {Item Model : Type*} [Fintype Item] [Fintype Model]
    [DecidableEq Item] [DecidableEq Model]
    (μ ν : PMF (Item → Model → Bool)) : ℝ :=
  inverseLinkSquaredDiscrepancy (responseSuccessMarginal μ) (responseSuccessMarginal ν)

theorem inverseLinkMarginalSquaredDiscrepancy_nonneg
    {Item Model : Type*} [Fintype Item] [Fintype Model]
    [DecidableEq Item] [DecidableEq Model]
    (μ ν : PMF (Item → Model → Bool)) :
    0 ≤ inverseLinkMarginalSquaredDiscrepancy μ ν :=
  inverseLinkSquaredDiscrepancy_nonneg _ _

@[simp]
theorem inverseLinkMarginalSquaredDiscrepancy_self
    {Item Model : Type*} [Fintype Item] [Fintype Model]
    [DecidableEq Item] [DecidableEq Model]
    (μ : PMF (Item → Model → Bool)) : inverseLinkMarginalSquaredDiscrepancy μ μ = 0 :=
  inverseLinkSquaredDiscrepancy_self _

/-- The existing product-response constructor has its prescribed Bernoulli success marginals. -/
theorem fixedDesignResponsePMF_responseSuccessMarginal
    {Item Model : Type*} [Fintype Item] [Fintype Model]
    [DecidableEq Item] [DecidableEq Model]
    (p : Item → Model → ℝ)
    (hp : ∀ i j, 0 ≤ p i j ∧ p i j ≤ 1) (i : Item) (j : Model) :
    responseSuccessMarginal (fixedDesignResponsePMF p hp) i j = p i j := by
  classical
  unfold responseSuccessMarginal
  rw [fixedDesignResponsePMF, AppliedModelingLib.pmfExp_map]
  change AppliedModelingLib.pmfExp
      (AppliedModelingLib.pmfPi (fun coord : Item × Model =>
        realBernoulliPMF (p coord.1 coord.2) (hp coord.1 coord.2).1 (hp coord.1 coord.2).2))
      (fun response : Item × Model → Bool => boolAsReal (response (i, j))) = p i j
  rw [AppliedModelingLib.pmfExp_pmfPi_eval_eq]
  simp [AppliedModelingLib.pmfExp, boolAsReal]

/-- An independent product response truth law with identity logits. -/
def logisticTwoItemTruthLaw : PMF (Fin 2 → Fin 2 → Bool) :=
  fixedDesignResponsePMF logisticTwoItemTruth (fun i j =>
    ⟨(logisticTwoItemTruth_strictlyInterior i j).1.le,
      (logisticTwoItemTruth_strictlyInterior i j).2.le⟩)

/-- The actual independent Bernoulli response law for arbitrary logistic rank-one factors. -/
def logisticRankOneNullLaw (U V : Fin 2 → ℝ) : PMF (Fin 2 → Fin 2 → Bool) :=
  fixedDesignResponsePMF (logisticRankOnePrediction U V) (fun i j =>
    ⟨(logisticRankOnePrediction_strictlyInterior U V i j).1.le,
      (logisticRankOnePrediction_strictlyInterior U V i j).2.le⟩)

@[simp]
theorem logisticTwoItemTruthLaw_successMarginal (i j : Fin 2) :
    responseSuccessMarginal logisticTwoItemTruthLaw i j = logisticTwoItemTruth i j :=
  fixedDesignResponsePMF_responseSuccessMarginal _ _ i j

@[simp]
theorem logisticRankOneNullLaw_successMarginal (U V : Fin 2 → ℝ) (i j : Fin 2) :
    responseSuccessMarginal (logisticRankOneNullLaw U V) i j = logisticRankOnePrediction U V i j :=
  fixedDesignResponsePMF_responseSuccessMarginal _ _ i j

theorem logisticTwoItemTruthLaw_successMarginal_strictlyInterior (i j : Fin 2) :
    0 < responseSuccessMarginal logisticTwoItemTruthLaw i j ∧
      responseSuccessMarginal logisticTwoItemTruthLaw i j < 1 := by
  rw [logisticTwoItemTruthLaw_successMarginal]
  exact logisticTwoItemTruth_strictlyInterior i j

theorem logisticRankOneNullLaw_successMarginal_strictlyInterior
    (U V : Fin 2 → ℝ) (i j : Fin 2) :
    0 < responseSuccessMarginal (logisticRankOneNullLaw U V) i j ∧
      responseSuccessMarginal (logisticRankOneNullLaw U V) i j < 1 := by
  rw [logisticRankOneNullLaw_successMarginal]
  exact logisticRankOnePrediction_strictlyInterior U V i j

/--
The loss identity depends only on source success probabilities. It therefore
also applies to response laws with arbitrary cross-item dependence, provided
their success marginals have the fixed logistic rank-one parametrization.
-/
theorem logisticLawDiscrepancy_eq_squaredFitLoss_of_successMarginals
    (Q : PMF (Fin 2 → Fin 2 → Bool)) (U V : Fin 2 → ℝ)
    (hQ : ∀ i j, responseSuccessMarginal Q i j = logisticRankOnePrediction U V i j) :
    inverseLinkMarginalSquaredDiscrepancy logisticTwoItemTruthLaw Q =
      twoItemSquaredFitLoss U V := by
  unfold inverseLinkMarginalSquaredDiscrepancy
  have hp : responseSuccessMarginal logisticTwoItemTruthLaw = logisticTwoItemTruth := by
    funext i j
    exact logisticTwoItemTruthLaw_successMarginal i j
  have hq : responseSuccessMarginal Q = logisticRankOnePrediction U V := by
    funext i j
    exact hQ i j
  rw [hp, hq, logisticTwoItemDiscrepancy_eq_squaredFitLoss]

theorem logisticLawDiscrepancy_eq_squaredFitLoss (U V : Fin 2 → ℝ) :
    inverseLinkMarginalSquaredDiscrepancy logisticTwoItemTruthLaw (logisticRankOneNullLaw U V) =
      twoItemSquaredFitLoss U V := by
  exact logisticLawDiscrepancy_eq_squaredFitLoss_of_successMarginals _ U V
    (logisticRankOneNullLaw_successMarginal U V)

/-- The fixed law discrepancy is nondegenerate: the displayed full-fit error is one. -/
theorem logisticLawDiscrepancy_firstCoordinate_eq_one :
    inverseLinkMarginalSquaredDiscrepancy logisticTwoItemTruthLaw
      (logisticRankOneNullLaw firstCoordinateFactor firstCoordinateFactor) = 1 := by
  rw [logisticLawDiscrepancy_eq_squaredFitLoss]
  simpa only [logisticTwoItemDiscrepancy_eq_squaredFitLoss] using
    logisticFirstCoordinate_discrepancy_eq_one

/--
Global law-level optimality over every response law with logistic rank-one
success marginals, a class larger than the source's conditionally independent
nulls. No cross-item independence assumption is needed for this discrepancy.
-/
theorem logisticFirstCoordinate_is_global_responseLaw_minimizer
    (Q : PMF (Fin 2 → Fin 2 → Bool))
    (hQ : ∃ U V : Fin 2 → ℝ,
      ∀ i j, responseSuccessMarginal Q i j = logisticRankOnePrediction U V i j) :
    inverseLinkMarginalSquaredDiscrepancy logisticTwoItemTruthLaw
      (logisticRankOneNullLaw firstCoordinateFactor firstCoordinateFactor) ≤
      inverseLinkMarginalSquaredDiscrepancy logisticTwoItemTruthLaw Q := by
  obtain ⟨U, V, hQ⟩ := hQ
  rw [logisticLawDiscrepancy_firstCoordinate_eq_one,
    logisticLawDiscrepancy_eq_squaredFitLoss_of_successMarginals Q U V hQ]
  exact one_le_twoItemSquaredFitLoss U V

/-- Restrict an actual two-item response law to the second item, retaining both models. -/
def restrictSecondItemResponseLaw (μ : PMF (Fin 2 → Fin 2 → Bool)) :
    PMF (Unit → Fin 2 → Bool) :=
  μ.map (fun response (_i : Unit) j => response 1 j)

@[simp]
theorem restrictSecondItemResponseLaw_successMarginal
    (μ : PMF (Fin 2 → Fin 2 → Bool)) (i : Unit) (j : Fin 2) :
    responseSuccessMarginal (restrictSecondItemResponseLaw μ) i j = responseSuccessMarginal μ 1 j := by
  unfold responseSuccessMarginal restrictSecondItemResponseLaw
  rw [AppliedModelingLib.pmfExp_map]

/-- An actual product response law for every restricted-population scalar factor candidate. -/
def restrictedLogisticNullLaw (u : ℝ) (V : Fin 2 → ℝ) : PMF (Unit → Fin 2 → Bool) :=
  fixedDesignResponsePMF (restrictedLogisticPrediction u V) (fun _i j =>
    ⟨(Real.sigmoid_pos (u * V j)).le, (Real.sigmoid_lt_one (u * V j)).le⟩)

@[simp]
theorem restrictedLogisticNullLaw_successMarginal (u : ℝ) (V : Fin 2 → ℝ) (i : Unit) (j : Fin 2) :
    responseSuccessMarginal (restrictedLogisticNullLaw u V) i j = restrictedLogisticPrediction u V i j :=
  fixedDesignResponsePMF_responseSuccessMarginal _ _ i j

theorem restrictedLogisticNullLaw_successMarginal_strictlyInterior
    (u : ℝ) (V : Fin 2 → ℝ) (i : Unit) (j : Fin 2) :
    0 < responseSuccessMarginal (restrictedLogisticNullLaw u V) i j ∧
      responseSuccessMarginal (restrictedLogisticNullLaw u V) i j < 1 := by
  rw [restrictedLogisticNullLaw_successMarginal]
  exact ⟨Real.sigmoid_pos _, Real.sigmoid_lt_one _⟩

theorem restrictedLogisticLawDiscrepancy_eq_squaredFitLoss (u : ℝ) (V : Fin 2 → ℝ) :
    inverseLinkMarginalSquaredDiscrepancy (restrictSecondItemResponseLaw logisticTwoItemTruthLaw)
      (restrictedLogisticNullLaw u V) = oneItemSquaredFitLoss 1 u V := by
  unfold inverseLinkMarginalSquaredDiscrepancy
  have hp : responseSuccessMarginal (restrictSecondItemResponseLaw logisticTwoItemTruthLaw) =
      restrictedLogisticTruth := by
    funext i j
    rw [restrictSecondItemResponseLaw_successMarginal, logisticTwoItemTruthLaw_successMarginal]
    rfl
  have hq : responseSuccessMarginal (restrictedLogisticNullLaw u V) =
      restrictedLogisticPrediction u V := by
    funext i j
    exact restrictedLogisticNullLaw_successMarginal u V i j
  rw [hp, hq, restrictedLogisticDiscrepancy_eq_squaredFitLoss]

/-- The restricted exact fit is optimal even among every response law, not just null laws. -/
theorem logisticSecondCoordinate_is_global_restricted_responseLaw_minimizer
    (Q : PMF (Unit → Fin 2 → Bool)) :
    inverseLinkMarginalSquaredDiscrepancy (restrictSecondItemResponseLaw logisticTwoItemTruthLaw)
      (restrictedLogisticNullLaw 1 secondCoordinateFactor) ≤
    inverseLinkMarginalSquaredDiscrepancy (restrictSecondItemResponseLaw logisticTwoItemTruthLaw) Q := by
  have hzero : inverseLinkMarginalSquaredDiscrepancy
      (restrictSecondItemResponseLaw logisticTwoItemTruthLaw)
      (restrictedLogisticNullLaw 1 secondCoordinateFactor) = 0 := by
    rw [restrictedLogisticLawDiscrepancy_eq_squaredFitLoss]
    simpa only [restrictedLogisticDiscrepancy_eq_squaredFitLoss] using
      logisticSecondCoordinate_discrepancy_eq_zero
  rw [hzero]
  exact inverseLinkMarginalSquaredDiscrepancy_nonneg _ _

/-- The full optimizer's actual restricted response law differs from the restricted optimizer. -/
theorem logisticPopulationRelativity_responseLaw_mismatch :
    restrictSecondItemResponseLaw (logisticRankOneNullLaw firstCoordinateFactor firstCoordinateFactor) ≠
      restrictedLogisticNullLaw 1 secondCoordinateFactor := by
  intro heq
  have hm := congrArg (fun μ : PMF (Unit → Fin 2 → Bool) => responseSuccessMarginal μ () 1) heq
  dsimp only at hm
  rw [restrictSecondItemResponseLaw_successMarginal, logisticRankOneNullLaw_successMarginal,
    restrictedLogisticNullLaw_successMarginal] at hm
  exact logisticPopulationRelativity_prediction_mismatch hm

/--
Population relativity with actual product-response laws: a full-population
global null minimizer and a restricted-population exact global null minimizer
have different induced restricted laws. Both optimizer quantifiers cover all
real factors; the discrepancy is fixed, nonnegative, zero on the diagonal,
and demonstrably not identically zero.
-/
theorem populationRelativity_logistic_responseLaw_witness :
    inverseLinkMarginalSquaredDiscrepancy logisticTwoItemTruthLaw
      (logisticRankOneNullLaw firstCoordinateFactor firstCoordinateFactor) = 1 ∧
    (∀ U V : Fin 2 → ℝ,
      inverseLinkMarginalSquaredDiscrepancy logisticTwoItemTruthLaw
        (logisticRankOneNullLaw firstCoordinateFactor firstCoordinateFactor) ≤
      inverseLinkMarginalSquaredDiscrepancy logisticTwoItemTruthLaw (logisticRankOneNullLaw U V)) ∧
    inverseLinkMarginalSquaredDiscrepancy (restrictSecondItemResponseLaw logisticTwoItemTruthLaw)
      (restrictedLogisticNullLaw 1 secondCoordinateFactor) = 0 ∧
    (∀ u : ℝ, ∀ V : Fin 2 → ℝ,
      inverseLinkMarginalSquaredDiscrepancy (restrictSecondItemResponseLaw logisticTwoItemTruthLaw)
        (restrictedLogisticNullLaw 1 secondCoordinateFactor) ≤
      inverseLinkMarginalSquaredDiscrepancy (restrictSecondItemResponseLaw logisticTwoItemTruthLaw)
        (restrictedLogisticNullLaw u V)) ∧
    restrictSecondItemResponseLaw (logisticRankOneNullLaw firstCoordinateFactor firstCoordinateFactor) ≠
      restrictedLogisticNullLaw 1 secondCoordinateFactor := by
  refine ⟨logisticLawDiscrepancy_firstCoordinate_eq_one, ?_, ?_, ?_,
    logisticPopulationRelativity_responseLaw_mismatch⟩
  · intro U V
    rw [logisticLawDiscrepancy_firstCoordinate_eq_one, logisticLawDiscrepancy_eq_squaredFitLoss]
    exact one_le_twoItemSquaredFitLoss U V
  · rw [restrictedLogisticLawDiscrepancy_eq_squaredFitLoss]
    simpa only [restrictedLogisticDiscrepancy_eq_squaredFitLoss] using
      logisticSecondCoordinate_discrepancy_eq_zero
  · intro u V
    simp only [restrictedLogisticLawDiscrepancy_eq_squaredFitLoss]
    exact secondCoordinateFactor_is_restricted_minimizer u V

end

end JGR26SubjectivityMonoculture
