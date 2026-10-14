import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Local distance to an exact prediction fiber

A nearest exact fit exists in finite-dimensional Euclidean space. Its displacement
is orthogonal to every differentiable curve through that fit inside the exact
fiber. Uniform transverse derivative bounds and a quadratic remainder then give
the local linear distance bound. A continuous derivative also supplies a uniform
linear remainder on a sufficiently small ball, so the final distance theorem
does not need an independent Taylor-remainder hypothesis.

The differential-geometric step connecting constant rank to realization of every
kernel vector by such a curve is a separate obligation.
-/

namespace JGR26SubjectivityMonoculture

open Filter Metric Set
open scoped Topology RealInnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The set of representations producing the fitted prediction exactly. -/
def exactPredictionFiber (prediction : E → F) (fit : E) : Set E :=
  {z | prediction z = prediction fit}

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ F] in
/-- A continuous prediction map has a nonempty closed exact fiber. -/
theorem exactPredictionFiber_closed_nonempty (prediction : E → F) (fit : E)
    (hcontinuous : Continuous prediction) :
    IsClosed (exactPredictionFiber prediction fit) ∧
      (exactPredictionFiber prediction fit).Nonempty := by
  refine ⟨isClosed_eq hcontinuous continuous_const, ⟨fit, rfl⟩⟩

omit [NormedSpace ℝ F] in
/-- Nearest exact fits exist and stay within twice the candidate's distance to the fit. -/
theorem exists_nearest_exactPredictionFiber (prediction : E → F) (fit x : E)
    (hcontinuous : Continuous prediction) :
    ∃ y ∈ exactPredictionFiber prediction fit,
      infDist x (exactPredictionFiber prediction fit) = dist x y ∧
        dist y fit ≤ 2 * dist x fit := by
  obtain ⟨hclosed, hnonempty⟩ :=
    exactPredictionFiber_closed_nonempty prediction fit hcontinuous
  obtain ⟨y, hy, hnearest⟩ := hclosed.exists_infDist_eq_dist hnonempty x
  refine ⟨y, hy, hnearest, ?_⟩
  have hnear : dist x y ≤ dist x fit := by
    rw [← hnearest]
    exact infDist_le_dist_of_mem rfl
  have htri := dist_triangle y x fit
  rw [dist_comm y x] at htri
  linarith

omit [FiniteDimensional ℝ E] in
/-- A nearest-point displacement is orthogonal to every tangent curve in the set. -/
theorem nearestPoint_inner_eq_zero_of_curve
    (s : Set E) (x y v : E) (curve : ℝ → E)
    (hmin : ∀ z ∈ s, dist x y ≤ dist x z)
    (hcurve : ∀ᶠ t in 𝓝 (0 : ℝ), curve t ∈ s)
    (hzero : curve 0 = y) (hderiv : HasDerivAt curve v 0) :
    ⟪x - y, v⟫ = 0 := by
  have hlocal : IsLocalMin (fun t : ℝ => ‖x - curve t‖ ^ 2) 0 := by
    filter_upwards [hcurve] with t ht
    have hle := hmin (curve t) ht
    rw [dist_eq_norm, dist_eq_norm] at hle
    rw [hzero]
    nlinarith [norm_nonneg (x - y), norm_nonneg (x - curve t)]
  have hsq := (hderiv.const_sub x).norm_sq
  have hstationary := hlocal.hasDerivAt_eq_zero hsq
  simp only [hzero, inner_neg_right] at hstationary
  linarith

/-- Every derivative-kernel vector is realized by a curve in the exact fiber. -/
def KernelVectorsHaveFiberCurves (prediction : E → F) (fit : E)
    (derivative : E → E →L[ℝ] F) (radius : ℝ) : Prop :=
  ∀ y ∈ exactPredictionFiber prediction fit, dist y fit < 2 * radius →
    ∀ v, derivative y v = 0 →
      ∃ curve : ℝ → E, curve 0 = y ∧ HasDerivAt curve v 0 ∧
        ∀ᶠ t in 𝓝 (0 : ℝ), curve t ∈ exactPredictionFiber prediction fit

omit [FiniteDimensional ℝ E] in
/-- The kernel-curve realization yields normality of the nearest-fit displacement. -/
theorem nearest_exactFit_is_kernelOrthogonal
    (prediction : E → F) (fit x y : E)
    (derivative : E → E →L[ℝ] F) {radius : ℝ}
    (hcurves : KernelVectorsHaveFiberCurves prediction fit derivative radius)
    (hy : y ∈ exactPredictionFiber prediction fit) (hnear : dist y fit < 2 * radius)
    (hnearest : infDist x (exactPredictionFiber prediction fit) = dist x y) :
    ∀ v, derivative y v = 0 → ⟪x - y, v⟫ = 0 := by
  intro v hv
  obtain ⟨curve, hzero, hderiv, hcurve⟩ := hcurves y hy hnear v hv
  apply nearestPoint_inner_eq_zero_of_curve
    (exactPredictionFiber prediction fit) x y v curve
      (fun z hz => ?_) hcurve hzero hderiv
  rw [← hnearest]
  exact infDist_le_dist_of_mem hz

/-- The nearest-fit Taylor argument gives a genuine bound on distance to the entire fiber. -/
theorem exactFiber_distance_le_of_transverse_derivative_and_remainder
    (prediction : E → F) (fit x : E) (derivative : E → E →L[ℝ] F)
    {radius strength remainder : ℝ}
    (hcontinuous : Continuous prediction) (hstrength : 0 < strength)
    (hremainder : 0 ≤ remainder) (hx : dist x fit < radius)
    (hsmall : remainder * radius ≤ strength / 2)
    (hcurves : KernelVectorsHaveFiberCurves prediction fit derivative radius)
    (htransverse : ∀ y ∈ exactPredictionFiber prediction fit,
      dist y fit < 2 * radius → ∀ v,
        (∀ w, derivative y w = 0 → ⟪v, w⟫ = 0) →
          strength * ‖v‖ ≤ ‖derivative y v‖)
    (htaylor : ∀ y ∈ exactPredictionFiber prediction fit,
      dist y fit < 2 * radius →
        ‖prediction x - prediction y - derivative y (x - y)‖ ≤
          remainder * ‖x - y‖ ^ 2) :
    infDist x (exactPredictionFiber prediction fit) ≤
      (2 / strength) * ‖prediction x - prediction fit‖ := by
  obtain ⟨y, hy, hnearest, hynear⟩ :=
    exists_nearest_exactPredictionFiber prediction fit x hcontinuous
  have hynear' : dist y fit < 2 * radius := by linarith
  have hnormal := nearest_exactFit_is_kernelOrthogonal prediction fit x y derivative
    hcurves hy hynear' hnearest
  have hlower := htransverse y hy hynear' (x - y) hnormal
  have hrem := htaylor y hy hynear'
  have heq : prediction y = prediction fit := hy
  have hdelta : ‖x - y‖ ≤ dist x fit := by
    rw [← dist_eq_norm, ← hnearest]
    exact infDist_le_dist_of_mem rfl
  have hsmall' : remainder * ‖x - y‖ ≤ strength / 2 :=
    (mul_le_mul_of_nonneg_left (hdelta.trans hx.le) hremainder).trans hsmall
  have hupper : ‖derivative y (x - y)‖ ≤
      ‖prediction x - prediction fit‖ + remainder * ‖x - y‖ ^ 2 := by
    have hdecomp : derivative y (x - y) =
        (prediction x - prediction y) -
          (prediction x - prediction y - derivative y (x - y)) := by abel
    rw [hdecomp]
    exact (norm_sub_le _ _).trans
      (by simpa only [heq] using
        add_le_add (le_refl ‖prediction x - prediction y‖) hrem)
  have hbound : ‖x - y‖ * strength ≤ 2 * ‖prediction x - prediction fit‖ := by
    nlinarith [norm_nonneg (x - y)]
  rw [hnearest, dist_eq_norm, div_mul_eq_mul_div]
  exact (le_div_iff₀ hstrength).mpr hbound

omit [FiniteDimensional ℝ E] in
/-- Derivative continuity supplies a uniformly small first-order remainder.

The two points vary independently in the ball. Applying the mean-value estimate
to `prediction - derivative y` is what makes the estimate uniform in the base
point `y`, rather than merely an expansion at the distinguished fit.
-/
theorem exists_radius_uniform_linear_remainder
    (prediction : E → F) (derivative : E → E →L[ℝ] F) (fit : E)
    {tolerance : ℝ} (htolerance : 0 < tolerance)
    (hcont : ContinuousAt derivative fit)
    (hderiv : ∀ᶠ z in 𝓝 fit, HasFDerivAt prediction (derivative z) z) :
    ∃ radius > 0, ∀ x ∈ ball fit radius, ∀ y ∈ ball fit radius,
      ‖prediction x - prediction y - derivative y (x - y)‖ ≤
        tolerance * ‖x - y‖ := by
  have hnear : ∀ᶠ z in 𝓝 fit,
      dist (derivative z) (derivative fit) < tolerance / 2 :=
    hcont.eventually (ball_mem_nhds _ (half_pos htolerance))
  obtain ⟨radius, hrad, hball⟩ :=
    Metric.eventually_nhds_iff_ball.mp (hnear.and hderiv)
  refine ⟨radius, hrad, ?_⟩
  intro x hx y hy
  have hdiff : ∀ z ∈ ball fit radius,
      HasFDerivWithinAt (fun w => prediction w - derivative y w)
        (derivative z - derivative y) (ball fit radius) z := by
    intro z hz
    exact ((hball z hz).2.sub (derivative y).hasFDerivAt).hasFDerivWithinAt
  have hbound : ∀ z ∈ ball fit radius, ‖derivative z - derivative y‖ ≤ tolerance := by
    intro z hz
    rw [← dist_eq_norm]
    have htri := dist_triangle (derivative z) (derivative fit) (derivative y)
    have hz' := (hball z hz).1
    have hy' := (hball y hy).1
    rw [dist_comm (derivative fit) (derivative y)] at htri
    linarith
  have h := (convex_ball fit radius).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hdiff hbound hy hx
  have heq : (prediction x - derivative y x) - (prediction y - derivative y y) =
      prediction x - prediction y - derivative y (x - y) := by
    rw [map_sub]
    abel
  rwa [heq] at h

/-- A uniform linear remainder and transverse strength bound imply fiber stability. -/
theorem exactFiber_distance_le_of_transverse_derivative_and_linear_remainder
    (prediction : E → F) (fit x : E) (derivative : E → E →L[ℝ] F)
    {radius strength tolerance : ℝ}
    (hcontinuous : Continuous prediction) (hstrength : 0 < strength)
    (hx : dist x fit < radius) (hsmall : tolerance ≤ strength / 2)
    (hcurves : KernelVectorsHaveFiberCurves prediction fit derivative radius)
    (htransverse : ∀ y ∈ exactPredictionFiber prediction fit,
      dist y fit < 2 * radius → ∀ v,
        (∀ w, derivative y w = 0 → ⟪v, w⟫ = 0) →
          strength * ‖v‖ ≤ ‖derivative y v‖)
    (htaylor : ∀ y ∈ exactPredictionFiber prediction fit,
      dist y fit < 2 * radius →
        ‖prediction x - prediction y - derivative y (x - y)‖ ≤
          tolerance * ‖x - y‖) :
    infDist x (exactPredictionFiber prediction fit) ≤
      (2 / strength) * ‖prediction x - prediction fit‖ := by
  obtain ⟨y, hy, hnearest, hynear⟩ :=
    exists_nearest_exactPredictionFiber prediction fit x hcontinuous
  have hynear' : dist y fit < 2 * radius := by linarith
  have hnormal := nearest_exactFit_is_kernelOrthogonal prediction fit x y derivative
    hcurves hy hynear' hnearest
  have hlower := htransverse y hy hynear' (x - y) hnormal
  have hrem := htaylor y hy hynear'
  have heq : prediction y = prediction fit := hy
  have hupper : ‖derivative y (x - y)‖ ≤
      ‖prediction x - prediction fit‖ + tolerance * ‖x - y‖ := by
    have hdecomp : derivative y (x - y) =
        (prediction x - prediction y) -
          (prediction x - prediction y - derivative y (x - y)) := by abel
    rw [hdecomp]
    exact (norm_sub_le _ _).trans
      (by simpa only [heq] using
        add_le_add (le_refl ‖prediction x - prediction y‖) hrem)
  have hbound : ‖x - y‖ * strength ≤ 2 * ‖prediction x - prediction fit‖ := by
    nlinarith [mul_le_mul_of_nonneg_right hsmall (norm_nonneg (x - y))]
  rw [hnearest, dist_eq_norm, div_mul_eq_mul_div]
  exact (le_div_iff₀ hstrength).mpr hbound

end JGR26SubjectivityMonoculture
