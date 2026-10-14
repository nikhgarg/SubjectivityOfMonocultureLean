import JGR26SubjectivityMonoculture.MainTheorems

/-!
# A probability-valued population-relativity witness

Fitting all probability-valued rank-one prediction matrices to the identity
matrix need not commute with restricting to a single item. The full fit has
squared loss one, whereas the restricted item admits a perfect fit.
-/

namespace JGR26SubjectivityMonoculture

open scoped BigOperators

/-- The two-item, two-model success-probability matrix. -/
def twoItemTruth (i j : Fin 2) : ℝ := if i = j then 1 else 0

/-- One-dimensional bilinear predictions. -/
def rankOnePrediction (U V : Fin 2 → ℝ) (i j : Fin 2) : ℝ := U i * V j

/-- Source-feasible probability-valued rank-one predictions. -/
def IsProbabilityValuedRankOne (U V : Fin 2 → ℝ) : Prop :=
  ∀ i j, 0 ≤ rankOnePrediction U V i j ∧ rankOnePrediction U V i j ≤ 1

/-- Squared discrepancy on the whole population. -/
def twoItemSquaredFitLoss (U V : Fin 2 → ℝ) : ℝ :=
  ∑ i, ∑ j, (rankOnePrediction U V i j - twoItemTruth i j) ^ 2

/-- Squared discrepancy after restricting to one item. -/
def oneItemSquaredFitLoss (i : Fin 2) (u : ℝ) (V : Fin 2 → ℝ) : ℝ :=
  ∑ j, (u * V j - twoItemTruth i j) ^ 2

/-- An exact two-dimensional identity separates the irreducible rank-one loss. -/
theorem twoItemSquaredFitLoss_eq_squares (U V : Fin 2 → ℝ) :
    twoItemSquaredFitLoss U V =
      (U 0 * V 0 + U 1 * V 1 - 1) ^ 2 +
        (U 0 * V 1 - U 1 * V 0) ^ 2 + 1 := by
  simp [twoItemSquaredFitLoss, rankOnePrediction, twoItemTruth, Fin.sum_univ_two]
  ring

/-- No rank-one candidate, including every probability-valued candidate, has loss below one. -/
theorem one_le_twoItemSquaredFitLoss (U V : Fin 2 → ℝ) :
    1 ≤ twoItemSquaredFitLoss U V := by
  rw [twoItemSquaredFitLoss_eq_squares]
  nlinarith [sq_nonneg (U 0 * V 0 + U 1 * V 1 - 1),
    sq_nonneg (U 0 * V 1 - U 1 * V 0)]

/-- A full-population rank-one minimizer. -/
def firstCoordinateFactor : Fin 2 → ℝ := ![1, 0]

/-- A restricted second-item perfect fit. -/
def secondCoordinateFactor : Fin 2 → ℝ := ![0, 1]

theorem firstCoordinateFactor_probabilityValued :
    IsProbabilityValuedRankOne firstCoordinateFactor firstCoordinateFactor := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rankOnePrediction, firstCoordinateFactor]

theorem firstCoordinateFactor_is_full_minimizer :
    ∀ U V : Fin 2 → ℝ, IsProbabilityValuedRankOne U V →
      twoItemSquaredFitLoss firstCoordinateFactor firstCoordinateFactor ≤
        twoItemSquaredFitLoss U V := by
  intro U V _
  have h := one_le_twoItemSquaredFitLoss U V
  simpa [twoItemSquaredFitLoss, firstCoordinateFactor, rankOnePrediction,
    twoItemTruth, Fin.sum_univ_two] using h

theorem secondCoordinateFactor_is_restricted_minimizer :
    ∀ u : ℝ, ∀ V : Fin 2 → ℝ,
      oneItemSquaredFitLoss 1 1 secondCoordinateFactor ≤
        oneItemSquaredFitLoss 1 u V := by
  intro u V
  have hnonneg : 0 ≤ oneItemSquaredFitLoss 1 u V :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  simpa [oneItemSquaredFitLoss, secondCoordinateFactor, twoItemTruth,
    Fin.sum_univ_two] using hnonneg

/-- The globally fitted predictions differ from a direct restricted-population fit. -/
theorem populationRelativity_probabilityValued_rankOne_witness :
    IsProbabilityValuedRankOne firstCoordinateFactor firstCoordinateFactor ∧
      (∀ U V : Fin 2 → ℝ, IsProbabilityValuedRankOne U V →
        twoItemSquaredFitLoss firstCoordinateFactor firstCoordinateFactor ≤
          twoItemSquaredFitLoss U V) ∧
      (∀ u : ℝ, ∀ V : Fin 2 → ℝ,
        oneItemSquaredFitLoss 1 1 secondCoordinateFactor ≤
          oneItemSquaredFitLoss 1 u V) ∧
      rankOnePrediction firstCoordinateFactor firstCoordinateFactor 1 1 ≠
        1 * secondCoordinateFactor 1 := by
  refine ⟨firstCoordinateFactor_probabilityValued,
    firstCoordinateFactor_is_full_minimizer,
    secondCoordinateFactor_is_restricted_minimizer, ?_⟩
  norm_num [rankOnePrediction, firstCoordinateFactor, secondCoordinateFactor]

end JGR26SubjectivityMonoculture
