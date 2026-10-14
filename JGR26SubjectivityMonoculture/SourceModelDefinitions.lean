import JGR26SubjectivityMonoculture.MainTheorems
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Null ladders, excess and population-specific targets

Excess uses the infimum over a null family; a population-specific target is
a selected attained minimizer. The two notions have different existence
requirements.
-/

namespace JGR26SubjectivityMonoculture

open Set
open Filter
open scoped Topology

noncomputable section

/-- Definition 2: nested families of probability laws. -/
def draftNullLadder {Law : Type*} (N : ℕ → Set Law) : Prop := NullLadder N

/-- An infimum of discrepancies admits a sequence of laws approaching its value. -/
theorem infimumDiscrepancy_approximating_sequence {Law : Type*}
    (D : Law → Law → ℝ) (P : Law) (N : Set Law) (excess : ℝ)
    (h : IsInfimumValue (discrepancyValues D P N) excess) :
    ∃ Q : ℕ → Law, (∀ t, Q t ∈ N) ∧
      Tendsto (fun t => D P (Q t)) atTop (𝓝 excess) := by
  classical
  have hchoose : ∀ t : ℕ, ∃ Q : Law, Q ∈ N ∧
      D P Q ≤ excess + 1 / ((t : ℝ) + 1) := by
    intro t
    obtain ⟨x, ⟨Q, hQ, rfl⟩, hx⟩ := h.2 (1 / ((t : ℝ) + 1)) (by positivity)
    exact ⟨Q, hQ, hx⟩
  choose Q hQ hupper using hchoose
  refine ⟨Q, hQ, ?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using (tendsto_const_nhds.add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))))
  · intro t
    exact h.1 _ ⟨Q t, hQ t, rfl⟩
  · intro t
    simpa only [one_div] using hupper t

/-- Definition 3: a selected minimizing law when attained, or a sequence at the
same fixed null level approaching its infimum when no minimizing law exists. -/
def sourceNullFitAtLevel {Law : Type*} (D : Law → Law → ℝ)
    (P : Law) (N : Set Law) (excess : ℝ) (fit : Law ⊕ (ℕ → Law)) : Prop :=
  IsInfimumValue (discrepancyValues D P N) excess ∧
    match fit with
    | .inl Q => Q ∈ N ∧ D P Q = excess
    | .inr Q => (¬ ∃ q ∈ N, D P q = excess) ∧ (∀ t, Q t ∈ N) ∧
        Tendsto (fun t => D P (Q t)) atTop (𝓝 excess)

/-- Definition 3: minimal excess together with its source-prescribed null fit. -/
def draftMinimalExcess {Law : Type*} (D : Law → Law → ℝ)
    (P : Law) (N : Set Law) (excess : ℝ) : Prop :=
  ∃ fit, sourceNullFitAtLevel D P N excess fit

/-- The two fit cases exist at every infimum, so the excess domain is unchanged. -/
theorem draftMinimalExcess_iff_infimum {Law : Type*}
    (D : Law → Law → ℝ) (P : Law) (N : Set Law) (excess : ℝ) :
    draftMinimalExcess D P N excess ↔ IsInfimumValue (discrepancyValues D P N) excess := by
  classical
  constructor
  · rintro ⟨fit, hfit⟩
    exact hfit.1
  · intro h
    by_cases hattained : ∃ Q ∈ N, D P Q = excess
    · obtain ⟨Q, hQ, hvalue⟩ := hattained
      exact ⟨.inl Q, h, hQ, hvalue⟩
    · obtain ⟨Q, hQ, hlimit⟩ := infimumDiscrepancy_approximating_sequence D P N excess h
      exact ⟨.inr Q, h, hattained, hQ, hlimit⟩

/-- Definition 4: an attained population-specific minimizer over the chosen null family. -/
def draftPopulationSpecificTarget {Law : Type*} (D : Law → Law → ℝ)
    (P : Law) (N : Set Law) (fit : Law) : Prop :=
  fit ∈ N ∧ ∀ Q ∈ N, D P fit ≤ D P Q

/-- At a fixed family, its infimum admits a sequence of laws approaching that value. -/
theorem draftMinimalExcess_approximating_sequence {Law : Type*}
    (D : Law → Law → ℝ) (P : Law) (N : Set Law) (excess : ℝ)
    (h : draftMinimalExcess D P N excess) :
    ∃ Q : ℕ → Law, (∀ t, Q t ∈ N) ∧
      Tendsto (fun t => D P (Q t)) atTop (𝓝 excess) :=
  infimumDiscrepancy_approximating_sequence D P N excess
    ((draftMinimalExcess_iff_infimum D P N excess).mp h)

end

end JGR26SubjectivityMonoculture
