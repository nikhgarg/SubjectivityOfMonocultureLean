import JGR26SubjectivityMonoculture.MainTheorems
import Mathlib.Analysis.SpecialFunctions.Sigmoid

/-!
# Heterogeneity normalization for a generic link

For the smooth probability link `sigmoid (u - v)`, translating both factors
leaves the fitted probability fixed while their uncentered Gram energy is
unbounded. Thus an attained finite heterogeneity maximizer needs a restriction
on the link or a specified normalization.
-/

namespace JGR26SubjectivityMonoculture

open scoped BigOperators

/-- One item and one model with the same scalar latent factor. -/
def translatedSingletonFactor (t : ℝ) : Unit → Fin 1 → ℝ := fun _ _ => t

/-- Every translated pair represents the same probability one half. -/
theorem translatedSingleton_prediction_eq_half (t : ℝ) :
    Real.sigmoid (translatedSingletonFactor t () 0 -
      translatedSingletonFactor t () 0) = (1 / 2 : ℝ) := by
  simp [translatedSingletonFactor, Real.sigmoid_zero]

/-- The probability link used in the example is twice continuously differentiable. -/
theorem translatedSingleton_link_contDiff :
    ContDiff ℝ 2 (fun z : ℝ × ℝ => Real.sigmoid (z.1 - z.2)) := by
  change ContDiff ℝ 2 (fun z : ℝ × ℝ => (1 + Real.exp (-(z.1 - z.2)))⁻¹)
  apply ContDiff.inv
  · exact contDiff_const.add
      (Real.contDiff_exp.comp ((contDiff_fst.sub contDiff_snd).neg))
  · intro z
    positivity

/-- The source's scalar Gram heterogeneity equals the square of the translation. -/
theorem translatedSingleton_heterogeneity_eq (t : ℝ) :
    oneDimHeterogeneityIndex (translatedSingletonFactor t)
      (translatedSingletonFactor t) = t ^ 2 := by
  simp [oneDimHeterogeneityIndex, oneDimFactorHeterogeneity, translatedSingletonFactor]

/-- No finite upper bound on heterogeneity follows from a fixed fitted probability. -/
theorem translatedSingleton_heterogeneity_unbounded (bound : ℝ) :
    ∃ t : ℝ, bound < oneDimHeterogeneityIndex (translatedSingletonFactor t)
      (translatedSingletonFactor t) := by
  refine ⟨|bound| + 1, ?_⟩
  rw [translatedSingleton_heterogeneity_eq]
  nlinarith [abs_nonneg bound, le_abs_self bound]

/-- The generic-link prescription to choose a heterogeneity maximizer can fail. -/
theorem translatedSingleton_no_heterogeneity_maximizer :
    ¬ ∃ t : ℝ, ∀ s : ℝ,
      oneDimHeterogeneityIndex (translatedSingletonFactor s)
        (translatedSingletonFactor s) ≤
      oneDimHeterogeneityIndex (translatedSingletonFactor t)
        (translatedSingletonFactor t) := by
  rintro ⟨t, hmax⟩
  obtain ⟨s, hs⟩ := translatedSingleton_heterogeneity_unbounded
    (oneDimHeterogeneityIndex (translatedSingletonFactor t) (translatedSingletonFactor t))
  exact hs.not_ge (hmax s)

end JGR26SubjectivityMonoculture
