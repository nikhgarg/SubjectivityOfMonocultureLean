import JGR26SubjectivityMonoculture.ConstantRankGeometry
import Mathlib.Data.Real.Sqrt

/-!
# Local prediction stability from the actual constant-rank assumption

Theorem 5 measures distance to the full exact-prediction
fiber, not to a chosen factor representation. The local identifiability
assumption is expanded into constant rank of the actual derivative and its
squared lower bound on kernel-normal vectors.

The proof derives the fiber curves, uniform normal strength, and uniform
first-order remainder from those assumptions. It proves the displayed
existential constant with `C = 4 / sqrt c`; this constant is not an additional
premise, and the proof does not require the appendix's sharper intermediate
coefficient.
-/

namespace JGR26SubjectivityMonoculture

open Filter Metric Set
open scoped Topology RealInnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Constant rank and the `c h` fit inequality give a local distance estimate. -/
theorem exists_radius_fiber_distance_bound_of_constantRank
    (prediction : E → F) (derivative : E → E →L[ℝ] F) (fit : E) {c h : ℝ}
    (hc : 0 < c) (hh : 0 < h) (hcontinuous : Continuous prediction)
    (hsmooth : ContDiffAt ℝ 1 prediction fit)
    (hderiv : ∀ᶠ z in 𝓝 fit, HasFDerivAt prediction (derivative z) z)
    (hrank : ∀ᶠ z in 𝓝 fit,
      Module.finrank ℝ (derivative z).range = Module.finrank ℝ (derivative fit).range)
    (hlower : ∀ v, (∀ k, derivative fit k = 0 → ⟪v, k⟫ = 0) →
      (c * h) * ‖v‖ ^ 2 ≤ ‖derivative fit v‖ ^ 2) :
    ∃ radius > 0, ∀ x, dist x fit < radius →
      infDist x (exactPredictionFiber prediction fit) ≤
        ((4 / Real.sqrt c) / Real.sqrt h) * ‖prediction x - prediction fit‖ := by
  have hroot : 0 < Real.sqrt (c * h) := Real.sqrt_pos.mpr (mul_pos hc hh)
  obtain ⟨r₁, hr₁, hcurves, htransverse⟩ :=
    exists_radius_fiberCurves_and_transverse_of_constantRank prediction derivative fit
      hc hh hsmooth hderiv hrank hlower
  have hcont : ContinuousAt derivative fit :=
    (hsmooth.continuousAt_fderiv one_ne_zero).congr_of_eventuallyEq
      (hderiv.mono fun z hz => hz.fderiv.symm)
  obtain ⟨r₂, hr₂, htaylor⟩ := exists_radius_uniform_linear_remainder
    prediction derivative fit (by positivity : 0 < Real.sqrt (c * h) / 4) hcont hderiv
  let radius := min r₁ (r₂ / 2)
  have hrad : 0 < radius := lt_min hr₁ (half_pos hr₂)
  have hrad₁ : radius ≤ r₁ := min_le_left _ _
  have hrad₂ : radius ≤ r₂ / 2 := min_le_right _ _
  have hcurves' : KernelVectorsHaveFiberCurves prediction fit derivative radius := by
    intro y hy hnear v hv
    exact hcurves y hy (hnear.trans_le (by linarith)) v hv
  refine ⟨radius, hrad, ?_⟩
  intro x hx
  have hbound := exactFiber_distance_le_of_transverse_derivative_and_linear_remainder
    prediction fit x derivative hcontinuous (half_pos hroot) hx (by linarith)
    hcurves'
    (fun y _ hnear => htransverse y (hnear.trans_le (by linarith)))
    (fun y _ hnear => htaylor x (by change dist x fit < r₂; linarith)
      y (by change dist y fit < r₂; linarith))
  have hcoeff : 2 / (Real.sqrt (c * h) / 2) =
      (4 / Real.sqrt c) / Real.sqrt h := by
    rw [Real.sqrt_mul hc.le]
    field_simp
    norm_num
  simpa only [hcoeff] using hbound

/-- Assumption 1, with the Jacobian interpreted as the actual Fréchet derivative. -/
def HasLocalIdentificationAt (prediction : E → F) (fit : E) (c h : ℝ) : Prop :=
  (∀ᶠ z in 𝓝 fit,
    Module.finrank ℝ (fderiv ℝ prediction z).range =
      Module.finrank ℝ (fderiv ℝ prediction fit).range) ∧
  ∀ v, (∀ k, fderiv ℝ prediction fit k = 0 → ⟪v, k⟫ = 0) →
    (c * h) * ‖v‖ ^ 2 ≤ ‖fderiv ℝ prediction fit v‖ ^ 2

/-- The pointwise distance statement follows from source smoothness and Assumption 1. -/
theorem localHeterogeneityStability
    (prediction : E → F) (fit : E) {c h : ℝ}
    (hc : 0 < c) (hh : 0 < h) (hsmooth : ContDiff ℝ 2 prediction)
    (hid : HasLocalIdentificationAt prediction fit c h) :
    ∃ radius > 0, ∀ x, dist x fit < radius →
      infDist x (exactPredictionFiber prediction fit) ≤
        ((4 / Real.sqrt c) / Real.sqrt h) * ‖prediction x - prediction fit‖ := by
  apply exists_radius_fiber_distance_bound_of_constantRank prediction
    (fderiv ℝ prediction) fit hc hh hsmooth.continuous
    (hsmooth.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).contDiffAt
    (Filter.Eventually.of_forall fun z =>
      (hsmooth.differentiable (by norm_num) z).hasFDerivAt) hid.1 hid.2

/-- The local equivalence set in Theorem 5, in the Euclidean prediction norm. -/
def localPredictionEquivalenceSet (prediction : E → F) (fit : E)
    (radius epsilon : ℝ) : Set E :=
  {x | dist x fit < radius ∧ ‖prediction x - prediction fit‖ ^ 2 ≤ epsilon ^ 2}

/-- The exact displayed supremum bound in Theorem 5.

In a Euclidean array codomain, its squared norm is the manuscript's sum of
squared prediction errors. The theorem holds for every positive `epsilon` after
the neighborhood is chosen, and therefore for all sufficiently small ones.
-/
theorem localHeterogeneityStability_sup
    (prediction : E → F) (fit : E) {c h : ℝ}
    (hc : 0 < c) (hh : 0 < h) (hsmooth : ContDiff ℝ 2 prediction)
    (hid : HasLocalIdentificationAt prediction fit c h) :
    ∃ radius > 0, ∃ C > 0, ∀ epsilon > 0,
      sSup ((fun x => infDist x (exactPredictionFiber prediction fit)) ''
        localPredictionEquivalenceSet prediction fit radius epsilon) ≤
        (C / Real.sqrt h) * epsilon := by
  obtain ⟨radius, hrad, hbound⟩ :=
    localHeterogeneityStability prediction fit hc hh hsmooth hid
  refine ⟨radius, hrad, 4 / Real.sqrt c, by positivity, ?_⟩
  intro epsilon hepsilon
  have hnonempty : ((fun x => infDist x (exactPredictionFiber prediction fit)) ''
      localPredictionEquivalenceSet prediction fit radius epsilon).Nonempty := by
    refine ⟨_, ⟨fit, ?_, rfl⟩⟩
    exact ⟨by simpa using hrad, by simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)]; positivity⟩
  apply csSup_le hnonempty
  rintro _ ⟨x, hx, rfl⟩
  have hnorm : ‖prediction x - prediction fit‖ ≤ epsilon := by
    have hsq := hx.2
    nlinarith [norm_nonneg (prediction x - prediction fit)]
  exact (hbound x hx.1).trans
    (mul_le_mul_of_nonneg_left hnorm (by positivity))

end JGR26SubjectivityMonoculture
