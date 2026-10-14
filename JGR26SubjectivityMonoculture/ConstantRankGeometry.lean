import JGR26SubjectivityMonoculture.LocalFiberStability
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Geometry of constant-rank prediction fibers

The submersion theorem realizes derivative-kernel vectors by exact-fiber curves.
A fixed projection onto the derivative image reduces a constant-rank map to a
submersion: equality of ranks then identifies the two derivative kernels.
-/

namespace JGR26SubjectivityMonoculture

open Filter Metric Set
open scoped Topology RealInnerProductSpace

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A finite-dimensional submersion has exact-fiber curves in every kernel direction. -/
theorem exists_fiberCurve_of_surjective_derivative [FiniteDimensional ℝ F]
    (prediction : E → F) (y v : E) (A : E →L[ℝ] F)
    (hsmooth : ContDiffAt ℝ 1 prediction y) (hderiv : HasFDerivAt prediction A y)
    (hsurj : A.range = ⊤) (hv : A v = 0) :
    ∃ curve : ℝ → E, curve 0 = y ∧ HasDerivAt curve v 0 ∧
      ∀ᶠ t in 𝓝 (0 : ℝ), prediction (curve t) = prediction y := by
  let hstrict := hsmooth.hasStrictFDerivAt' hderiv one_ne_zero
  let w : A.ker := ⟨v, hv⟩
  let line : ℝ → A.ker := fun t => t • w
  let curve : ℝ → E := fun t => hstrict.implicitFunction prediction A hsurj
    (prediction y) (line t)
  have hline : HasDerivAt line w 0 := by
    simpa [line] using (hasDerivAt_id (0 : ℝ)).smul_const w
  refine ⟨curve, ?_, ?_, ?_⟩
  · simp [curve, line]
  · have houter : HasFDerivAt (hstrict.implicitFunction prediction A hsurj
        (prediction y)) A.ker.subtypeL (line 0) := by
      simpa [line] using (hstrict.to_implicitFunction hsurj).hasFDerivAt
    have h := houter.comp_hasDerivAt 0 hline
    simpa [curve, line, w] using h
  · have ht : Tendsto (fun t : ℝ => (prediction y, line t)) (𝓝 0)
        (𝓝 (prediction y, (0 : A.ker))) := by
      simpa [line] using tendsto_const_nhds.prodMk_nhds hline.continuousAt
    exact ht.eventually (hstrict.map_implicitFunction_eq hsurj)

/-- Equality of ranks prevents a surjective image projection from losing kernel information. -/
theorem ker_comp_eq_of_finrank_range_eq [FiniteDimensional ℝ G]
    (A : E →L[ℝ] F) (P : F →L[ℝ] G)
    (hsurj : (P.comp A).range = ⊤)
    (hrank : Module.finrank ℝ A.range = Module.finrank ℝ G) :
    (P.comp A).ker = A.ker := by
  apply (Submodule.eq_of_le_of_finrank_eq (show A.ker ≤ (P.comp A).ker from ?_) ?_).symm
  · intro v hv
    change P (A v) = 0
    rw [show A v = 0 from hv, map_zero]
  · have hA := A.toLinearMap.finrank_range_add_finrank_ker
    have hPA := (P.comp A).toLinearMap.finrank_range_add_finrank_ker
    rw [hsurj, finrank_top, ← hrank] at hPA
    exact Nat.add_left_cancel (hA.trans hPA.symm)

/-- Vanishing derivatives on a neighborhood force local constancy. -/
theorem eventually_eq_of_eventually_hasDerivAt_zero
    (f : ℝ → F) (a : ℝ)
    (hzero : ∀ᶠ t in 𝓝 a, HasDerivAt f 0 t) :
    ∀ᶠ t in 𝓝 a, f t = f a := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hzero
  filter_upwards [Metric.ball_mem_nhds a hr] with t ht
  exact isOpen_ball.is_const_of_deriv_eq_zero (convex_ball a r).isPreconnected
    (fun z hz => (hball z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hball z hz).deriv) ht (mem_ball_self hr)

/-- The implicit parametrization of a `C¹` submersion is itself `C¹` at the base point. -/
theorem contDiffAt_implicitFunction [FiniteDimensional ℝ F]
    (prediction : E → F) (y : E) (A : E →L[ℝ] F)
    (hsmooth : ContDiffAt ℝ 1 prediction y) (hstrict : HasStrictFDerivAt prediction A y)
    (hsurj : A.range = ⊤) :
    ContDiffAt ℝ 1 (hstrict.implicitFunction prediction A hsurj (prediction y)) 0 := by
  let hker := A.ker_closedComplemented_of_finiteDimensional_range
  let φ := hstrict.implicitFunctionDataOfComplemented prediction A hsurj hker
  have hright : ContDiffAt ℝ 1 φ.rightFun y := by
    exact (Classical.choose hker).contDiff.contDiffAt.comp y
      (contDiffAt_id.sub contDiffAt_const)
  have hprod : ContDiffAt ℝ 1 φ.prodFun y := hsmooth.prodMk hright
  have hbase : φ.toOpenPartialHomeomorph.symm (φ.prodFun y) = y :=
    φ.toOpenPartialHomeomorph.left_inv φ.pt_mem_toOpenPartialHomeomorph_source
  have hinv : ContDiffAt ℝ 1 φ.toOpenPartialHomeomorph.symm (φ.prodFun y) := by
    apply φ.toOpenPartialHomeomorph.contDiffAt_symm
      (f₀' := φ.leftDeriv.equivProdOfSurjectiveOfIsCompl φ.rightDeriv
        φ.range_leftDeriv φ.range_rightDeriv φ.isCompl_ker)
      φ.map_pt_mem_toOpenPartialHomeomorph_target
    · change HasFDerivAt φ.prodFun _ (φ.toOpenPartialHomeomorph.symm (φ.prodFun y))
      rw [hbase]
      exact φ.hasStrictFDerivAt.hasFDerivAt
    · change ContDiffAt ℝ 1 φ.prodFun (φ.toOpenPartialHomeomorph.symm (φ.prodFun y))
      rw [hbase]
      exact hprod
  have hprod_y : φ.prodFun y = (prediction y, 0) := by
    simp [φ, ImplicitFunctionData.prodFun]
  rw [hprod_y] at hinv
  have hslice : ContDiffAt ℝ 1 (fun z : A.ker => (prediction y, z)) 0 :=
    contDiffAt_const.prodMk contDiffAt_id
  have h := hinv.comp 0 (show ContDiffAt ℝ 1
      (fun z : A.ker => (prediction y, z)) 0 from hslice)
  simpa [φ, hker, ImplicitFunctionData.prodFun, ImplicitFunctionData.implicitFunction,
    HasStrictFDerivAt.implicitFunction, HasStrictFDerivAt.implicitToOpenPartialHomeomorph,
    HasStrictFDerivAt.implicitToOpenPartialHomeomorphOfComplemented] using h

/-- A submersion projection with the same local kernels realizes exact prediction-fiber curves. -/
theorem exists_fiberCurve_of_projected_submersion [FiniteDimensional ℝ G]
    (prediction : E → F) (derivative : E → E →L[ℝ] F)
    (y v : E) (P : F →L[ℝ] G)
    (hsmooth : ContDiffAt ℝ 1 prediction y)
    (hderiv : ∀ᶠ z in 𝓝 y, HasFDerivAt prediction (derivative z) z)
    (hsurj : (P.comp (derivative y)).range = ⊤)
    (hker : ∀ᶠ z in 𝓝 y, (P.comp (derivative z)).ker = (derivative z).ker)
    (hv : derivative y v = 0) :
    ∃ curve : ℝ → E, curve 0 = y ∧ HasDerivAt curve v 0 ∧
      ∀ᶠ t in 𝓝 (0 : ℝ), prediction (curve t) = prediction y := by
  let q : E → G := fun z => P (prediction z)
  let B := P.comp (derivative y)
  have hq : ContDiffAt ℝ 1 q y := P.contDiff.contDiffAt.comp y hsmooth
  have hqderiv : HasFDerivAt q B y :=
    P.hasFDerivAt.comp y hderiv.self_of_nhds
  let hstrict := hq.hasStrictFDerivAt' hqderiv one_ne_zero
  let w : B.ker := ⟨v, by change P (derivative y v) = 0; rw [hv, map_zero]⟩
  let line : ℝ → B.ker := fun t => t • w
  let curve : ℝ → E := fun t => hstrict.implicitFunction q B hsurj (q y) (line t)
  have hline : HasDerivAt line w 0 := by
    simpa [line] using (hasDerivAt_id (0 : ℝ)).smul_const w
  have hlineSmooth : ContDiffAt ℝ 1 line 0 :=
    contDiffAt_id.smul contDiffAt_const
  have hchart : ContDiffAt ℝ 1 (hstrict.implicitFunction q B hsurj (q y)) (line 0) := by
    simpa [line] using contDiffAt_implicitFunction q y B hq hstrict hsurj
  have hcurveSmooth : ContDiffAt ℝ 1 curve 0 := hchart.comp 0 hlineSmooth
  have hcurveZero : curve 0 = y := by simp [curve, line]
  have hcurveDeriv : HasDerivAt curve v 0 := by
    have houter : HasFDerivAt (hstrict.implicitFunction q B hsurj (q y))
        B.ker.subtypeL (line 0) := by
      simpa [line] using (hstrict.to_implicitFunction hsurj).hasFDerivAt
    simpa [curve, line, w] using houter.comp_hasDerivAt 0 hline
  have hcurveTendsto : Tendsto curve (𝓝 0) (𝓝 y) := by
    simpa only [hcurveZero] using hcurveDeriv.continuousAt.tendsto
  have hqcurve : ∀ᶠ t in 𝓝 (0 : ℝ), q (curve t) = q y := by
    have ht : Tendsto (fun t : ℝ => (q y, line t)) (𝓝 0) (𝓝 (q y, (0 : B.ker))) := by
      simpa [line] using tendsto_const_nhds.prodMk_nhds hline.continuousAt
    exact ht.eventually (hstrict.map_implicitFunction_eq hsurj)
  have hpzero : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt (fun s => prediction (curve s)) 0 t := by
    filter_upwards [hcurveSmooth.eventually (by norm_num),
      hcurveTendsto.eventually hderiv, hcurveTendsto.eventually hker,
      hqcurve.eventually_nhds] with t htSmooth htDeriv htKer htQ
    have htCurve : HasDerivAt curve (deriv curve t) t :=
      (htSmooth.differentiableAt one_ne_zero).hasDerivAt
    have htComp := (P.hasFDerivAt.comp (curve t) htDeriv).comp_hasDerivAt t htCurve
    have htConst : HasDerivAt (fun s => q (curve s)) 0 t :=
      (hasDerivAt_const t (q y)).congr_of_eventuallyEq htQ
    have hBzero : (P.comp (derivative (curve t))) (deriv curve t) = 0 :=
      htComp.unique htConst
    have hAzero : derivative (curve t) (deriv curve t) = 0 := by
      have hmem : deriv curve t ∈ (P.comp (derivative (curve t))).ker := hBzero
      rw [htKer] at hmem
      exact hmem
    simpa only [hAzero] using htDeriv.comp_hasDerivAt t htCurve
  refine ⟨curve, hcurveZero, hcurveDeriv, ?_⟩
  simpa only [hcurveZero] using
    eventually_eq_of_eventually_hasDerivAt_zero (fun t => prediction (curve t)) 0 hpzero

omit [FiniteDimensional ℝ E] in
/-- Surjectivity of a continuous finite-dimensional operator family persists locally. -/
theorem eventually_surjective_of_continuousAt [FiniteDimensional ℝ F]
    (B : E → E →L[ℝ] F) (y : E)
    (hcont : ContinuousAt B y) (hsurj : (B y).range = ⊤) :
    ∀ᶠ z in 𝓝 y, (B z).range = ⊤ := by
  obtain ⟨R, hR⟩ := (B y).exists_right_inverse_of_surjective hsurj
  have hcomp : ContinuousAt (fun z => (B z).comp R) y :=
    hcont.clm_comp continuousAt_const
  have hid : (ContinuousLinearEquiv.refl ℝ F : F →L[ℝ] F) = (B y).comp R := by
    exact hR.symm
  have hnear := hcomp.preimage_mem_nhds
    (hid ▸ (ContinuousLinearEquiv.refl ℝ F).nhds)
  filter_upwards [hnear] with z hz
  obtain ⟨e, he⟩ := hz
  apply LinearMap.range_eq_top.mpr
  intro g
  refine ⟨R (e.symm g), ?_⟩
  have h := congrArg (fun T : F →L[ℝ] F => T (e.symm g)) he
  exact h.symm.trans (e.apply_symm_apply g)

omit [FiniteDimensional ℝ E] in
/-- A continuous projection onto a derivative image does not change that derivative. -/
theorem exists_rangeProjection [FiniteDimensional ℝ F] (A : E →L[ℝ] F) :
    ∃ P : F →L[ℝ] A.range, P.comp A = A.rangeRestrict := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl A.range
  let P := (A.range.linearProjOfIsCompl C hC).toContinuousLinearMap
  refine ⟨P, ?_⟩
  apply ContinuousLinearMap.ext
  intro v
  change A.range.linearProjOfIsCompl C hC (A v) = A.rangeRestrict v
  exact Submodule.linearProjOfIsCompl_apply_left hC (A.rangeRestrict v)

/-- Constant finite rank and `C¹` regularity construct all kernel tangent curves. -/
theorem exists_fiberCurve_of_constantRank [FiniteDimensional ℝ F]
    (prediction : E → F) (derivative : E → E →L[ℝ] F) (y v : E)
    (hsmooth : ContDiffAt ℝ 1 prediction y)
    (hderiv : ∀ᶠ z in 𝓝 y, HasFDerivAt prediction (derivative z) z)
    (hrank : ∀ᶠ z in 𝓝 y,
      Module.finrank ℝ (derivative z).range = Module.finrank ℝ (derivative y).range)
    (hv : derivative y v = 0) :
    ∃ curve : ℝ → E, curve 0 = y ∧ HasDerivAt curve v 0 ∧
      ∀ᶠ t in 𝓝 (0 : ℝ), prediction (curve t) = prediction y := by
  obtain ⟨P, hP⟩ := exists_rangeProjection (derivative y)
  have hcont : ContinuousAt derivative y :=
    (hsmooth.continuousAt_fderiv one_ne_zero).congr_of_eventuallyEq
      (hderiv.mono fun z hz => hz.fderiv.symm)
  have hPcont : ContinuousAt (fun z => P.comp (derivative z)) y :=
    (ContinuousLinearMap.compL ℝ E F (derivative y).range P).continuous.continuousAt.comp hcont
  have hsurj : (P.comp (derivative y)).range = ⊤ := by
    rw [hP]
    exact (derivative y).toLinearMap.range_rangeRestrict
  have hsurjNear := eventually_surjective_of_continuousAt
    (fun z => P.comp (derivative z)) y hPcont hsurj
  apply exists_fiberCurve_of_projected_submersion prediction derivative y v P
    hsmooth hderiv hsurj ?_ hv
  filter_upwards [hsurjNear, hrank] with z hzSurj hzRank
  exact ker_comp_eq_of_finrank_range_eq (derivative z) P hzSurj hzRank

/-- Constant rank on a neighborhood supplies a positive-radius kernel-curve realization. -/
theorem exists_radius_kernelVectorsHaveFiberCurves_of_constantRank [FiniteDimensional ℝ F]
    (prediction : E → F) (derivative : E → E →L[ℝ] F) (fit : E)
    (hsmooth : ContDiffAt ℝ 1 prediction fit)
    (hderiv : ∀ᶠ z in 𝓝 fit, HasFDerivAt prediction (derivative z) z)
    (hrank : ∀ᶠ z in 𝓝 fit,
      Module.finrank ℝ (derivative z).range = Module.finrank ℝ (derivative fit).range) :
    ∃ radius > 0, KernelVectorsHaveFiberCurves prediction fit derivative radius := by
  have hlocal : ∀ᶠ y in 𝓝 fit, ∀ v, derivative y v = 0 →
      ∃ curve : ℝ → E, curve 0 = y ∧ HasDerivAt curve v 0 ∧
        ∀ᶠ t in 𝓝 (0 : ℝ), prediction (curve t) = prediction y := by
    filter_upwards [hsmooth.eventually (by norm_num), hderiv.eventually_nhds,
      hrank.eventually_nhds] with y hySmooth hyDeriv hyRank
    intro v hv
    apply exists_fiberCurve_of_constantRank prediction derivative y v hySmooth hyDeriv ?_ hv
    filter_upwards [hyRank] with z hzRank
    exact hzRank.trans hyRank.self_of_nhds.symm
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hlocal
  refine ⟨r / 2, half_pos hr, ?_⟩
  intro y hy hnear v hv
  have hyball : y ∈ ball fit r := by
    change dist y fit < r
    linarith
  obtain ⟨curve, hzero, hcurveDeriv, hcurve⟩ := hball y hyball v hv
  refine ⟨curve, hzero, hcurveDeriv, ?_⟩
  filter_upwards [hcurve] with t ht
  exact ht.trans hy

omit [FiniteDimensional ℝ E] in
/-- Orthogonality to the kernel makes an exact preimage no shorter than the normal vector. -/
theorem norm_le_of_kernelOrthogonal_of_image_eq
    (A : E →L[ℝ] F) (v w : E)
    (horth : ∀ k, A k = 0 → ⟪v, k⟫ = 0) (himage : A w = A v) :
    ‖v‖ ≤ ‖w‖ := by
  have hzero : A (v - w) = 0 := by rw [map_sub, himage, sub_self]
  have hinner : ⟪v, w⟫ = ‖v‖ ^ 2 :=
    inner_eq_norm_sq_left_iff.mpr (horth (v - w) hzero)
  have hcs := real_inner_le_norm v w
  rw [hinner] at hcs
  by_cases hv : ‖v‖ = 0
  · simpa only [hv] using norm_nonneg w
  · have hvpos := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv)
    nlinarith

/-- An operator within one half of the identity has inverse norm at most two. -/
theorem norm_symm_apply_le_two_of_norm_sub_id_lt_half [FiniteDimensional ℝ G]
    (e : G ≃L[ℝ] G)
    (hclose : ‖(e : G →L[ℝ] G) - ContinuousLinearMap.id ℝ G‖ < 1 / 2) (u : G) :
    ‖e.symm u‖ ≤ 2 * ‖u‖ := by
  let w := e.symm u
  have hdiff := ((e : G →L[ℝ] G) - ContinuousLinearMap.id ℝ G).le_opNorm w
  have hdecomp : w = e w -
      (((e : G →L[ℝ] G) - ContinuousLinearMap.id ℝ G) w) := by
    change w = e w - (e w - w)
    abel
  have htri : ‖w‖ ≤ ‖e w‖ +
      ‖((e : G →L[ℝ] G) - ContinuousLinearMap.id ℝ G) w‖ := by
    calc
      ‖w‖ = ‖e w - (((e : G →L[ℝ] G) - ContinuousLinearMap.id ℝ G) w)‖ :=
        congrArg norm hdecomp
      _ ≤ _ := norm_sub_le _ _
  have hew : e w = u := e.apply_symm_apply u
  rw [hew] at htri
  change ‖w‖ ≤ 2 * ‖u‖
  nlinarith [norm_nonneg w]

omit [FiniteDimensional ℝ E] in
/-- A locally bounded right inverse controls the derivative on its kernel-normal space. -/
theorem norm_le_mul_of_projected_rightInverse [FiniteDimensional ℝ G]
    (A : E →L[ℝ] F) (P : F →L[ℝ] G) (R : G →L[ℝ] E)
    (e : G ≃L[ℝ] G) (he : (e : G →L[ℝ] G) = (P.comp A).comp R)
    (hker : (P.comp A).ker = A.ker)
    (hclose : ‖(e : G →L[ℝ] G) - ContinuousLinearMap.id ℝ G‖ < 1 / 2)
    (v : E) (horth : ∀ k, A k = 0 → ⟪v, k⟫ = 0) :
    ‖v‖ ≤ (2 * ‖R‖ * ‖P‖) * ‖A v‖ := by
  let u := e.symm (P (A v))
  have hBu : (P.comp A) (R u) = P (A v) := by
    have h := e.apply_symm_apply (P (A v))
    change (e : G →L[ℝ] G) u = P (A v) at h
    rw [he] at h
    exact h
  have hkerMem : v - R u ∈ (P.comp A).ker := by
    change (P.comp A) (v - R u) = 0
    rw [map_sub, hBu]
    exact sub_self _
  rw [hker] at hkerMem
  have hAeq : A (R u) = A v := by
    have hzero : A (v - R u) = 0 := hkerMem
    rw [map_sub, sub_eq_zero] at hzero
    exact hzero.symm
  have hvw := norm_le_of_kernelOrthogonal_of_image_eq A v (R u) horth hAeq
  have hu := norm_symm_apply_le_two_of_norm_sub_id_lt_half e hclose (P (A v))
  calc
    ‖v‖ ≤ ‖R u‖ := hvw
    _ ≤ ‖R‖ * ‖u‖ := R.le_opNorm u
    _ ≤ ‖R‖ * (2 * ‖P (A v)‖) := mul_le_mul_of_nonneg_left hu (norm_nonneg R)
    _ ≤ ‖R‖ * (2 * (‖P‖ * ‖A v‖)) := by
      gcongr
      exact P.le_opNorm (A v)
    _ = (2 * ‖R‖ * ‖P‖) * ‖A v‖ := by ring

/-- Constant rank makes a fixed projected right inverse uniformly quantitative nearby. -/
theorem eventually_norm_le_mul_of_constantRank_projection [FiniteDimensional ℝ G]
    (derivative : E → E →L[ℝ] F) (fit : E) (P : F →L[ℝ] G) (R : G →L[ℝ] E)
    (hcont : ContinuousAt derivative fit)
    (hR : (P.comp (derivative fit)).comp R = ContinuousLinearMap.id ℝ G)
    (hrank : ∀ᶠ z in 𝓝 fit, Module.finrank ℝ (derivative z).range = Module.finrank ℝ G) :
    ∀ᶠ z in 𝓝 fit, ∀ v,
      (∀ k, derivative z k = 0 → ⟪v, k⟫ = 0) →
        ‖v‖ ≤ (2 * ‖R‖ * ‖P‖) * ‖derivative z v‖ := by
  have hPcont : ContinuousAt (fun z => P.comp (derivative z)) fit :=
    (ContinuousLinearMap.compL ℝ E F G P).continuous.continuousAt.comp hcont
  have hcomp : ContinuousAt (fun z => (P.comp (derivative z)).comp R) fit :=
    hPcont.clm_comp continuousAt_const
  have hid : (ContinuousLinearEquiv.refl ℝ G : G →L[ℝ] G) =
      (P.comp (derivative fit)).comp R := hR.symm
  have hequiv := hcomp.preimage_mem_nhds
    (hid ▸ (ContinuousLinearEquiv.refl ℝ G).nhds)
  have hclose : ∀ᶠ z in 𝓝 fit,
      ‖(P.comp (derivative z)).comp R - ContinuousLinearMap.id ℝ G‖ < 1 / 2 :=
    (hcomp.sub continuousAt_const).norm.eventually_lt continuousAt_const
      (by rw [hR, sub_self, norm_zero]; norm_num)
  filter_upwards [hequiv, hclose, hrank] with z hzEquiv hzClose hzRank
  obtain ⟨e, he⟩ := hzEquiv
  have hsurj : (P.comp (derivative z)).range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    intro g
    refine ⟨R (e.symm g), ?_⟩
    have h := congrArg (fun T : G →L[ℝ] G => T (e.symm g)) he
    exact h.symm.trans (e.apply_symm_apply g)
  have hker := ker_comp_eq_of_finrank_range_eq (derivative z) P hsurj hzRank
  intro v hv
  exact norm_le_mul_of_projected_rightInverse (derivative z) P R e he hker
    (by rwa [he]) v hv

/-- A continuous constant-rank operator family has a uniform positive transverse strength. -/
theorem exists_strength_eventually_transverse_of_constantRank [FiniteDimensional ℝ F]
    (derivative : E → E →L[ℝ] F) (fit : E)
    (hcont : ContinuousAt derivative fit)
    (hrank : ∀ᶠ z in 𝓝 fit,
      Module.finrank ℝ (derivative z).range = Module.finrank ℝ (derivative fit).range) :
    ∃ strength > 0, ∀ᶠ z in 𝓝 fit, ∀ v,
      (∀ k, derivative z k = 0 → ⟪v, k⟫ = 0) →
        strength * ‖v‖ ≤ ‖derivative z v‖ := by
  obtain ⟨P, hP⟩ := exists_rangeProjection (derivative fit)
  have hsurj : (P.comp (derivative fit)).range = ⊤ := by
    rw [hP]
    exact (derivative fit).toLinearMap.range_rangeRestrict
  obtain ⟨R, hR⟩ := (P.comp (derivative fit)).exists_right_inverse_of_surjective hsurj
  let C := max 1 (2 * ‖R‖ * ‖P‖)
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨1 / C, one_div_pos.mpr hC, ?_⟩
  filter_upwards [eventually_norm_le_mul_of_constantRank_projection derivative fit P R
    hcont hR hrank] with z hz
  intro v hv
  have hnorm := (hz v hv).trans
    (mul_le_mul_of_nonneg_right (le_max_right 1 _) (norm_nonneg (derivative z v)))
  change (1 / C) * ‖v‖ ≤ ‖derivative z v‖
  rw [one_div_mul_eq_div]
  exact (div_le_iff₀ hC).mpr (by rw [mul_comm]; exact hnorm)

/-- A transverse strength bounds the norm of a right inverse into the kernel-normal space. -/
theorem exists_normal_rangeRightInverse
    (A : E →L[ℝ] F) {strength : ℝ} (hstrength : 0 < strength)
    (hlower : ∀ v, (∀ k, A k = 0 → ⟪v, k⟫ = 0) → strength * ‖v‖ ≤ ‖A v‖) :
    ∃ R : A.range →L[ℝ] E,
      A.rangeRestrict.comp R = ContinuousLinearMap.id ℝ A.range ∧ ‖R‖ ≤ 1 / strength := by
  have hsurj : A.rangeRestrict.range = ⊤ := A.toLinearMap.range_rangeRestrict
  obtain ⟨R₀, hR₀⟩ := A.rangeRestrict.exists_right_inverse_of_surjective hsurj
  let N : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - A.ker.starProjection
  let R := N.comp R₀
  have himage : ∀ g : A.range, A (R g) = (g : F) := by
    intro g
    have hR₀point := congrArg (fun T : A.range →L[ℝ] A.range => T g) hR₀
    have hpoint : A (R₀ g) = (g : F) := congrArg Subtype.val hR₀point
    have hproj : A (A.ker.starProjection (R₀ g)) = 0 :=
      A.ker.starProjection_apply_mem (R₀ g)
    change A (R₀ g - A.ker.starProjection (R₀ g)) = (g : F)
    rw [map_sub, hproj, sub_zero, hpoint]
  refine ⟨R, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro g
    exact Subtype.ext (himage g)
  · apply R.opNorm_le_bound (one_div_nonneg.mpr hstrength.le)
    intro g
    have hnormal : R g ∈ A.kerᗮ := A.ker.sub_starProjection_mem_orthogonal (R₀ g)
    have horth : ∀ k, A k = 0 → ⟪R g, k⟫ = 0 := by
      intro k hk
      rw [real_inner_comm]
      exact (A.ker.mem_orthogonal (R g)).mp hnormal k hk
    have h := hlower (R g) horth
    rw [himage] at h
    have hdiv := (le_div_iff₀ hstrength).mpr (by simpa only [mul_comm] using h)
    rw [one_div_mul_eq_div]
    exact hdiv

/-- A fit's transverse strength persists with a factor of one half under constant rank. -/
theorem eventually_transverse_strength_ge_half_of_constantRank
    {F' : Type*} [NormedAddCommGroup F'] [InnerProductSpace ℝ F'] [FiniteDimensional ℝ F']
    (derivative : E → E →L[ℝ] F') (fit : E) {strength : ℝ}
    (hstrength : 0 < strength) (hcont : ContinuousAt derivative fit)
    (hrank : ∀ᶠ z in 𝓝 fit,
      Module.finrank ℝ (derivative z).range = Module.finrank ℝ (derivative fit).range)
    (hlower : ∀ v, (∀ k, derivative fit k = 0 → ⟪v, k⟫ = 0) →
      strength * ‖v‖ ≤ ‖derivative fit v‖) :
    ∀ᶠ z in 𝓝 fit, ∀ v,
      (∀ k, derivative z k = 0 → ⟪v, k⟫ = 0) →
        (strength / 2) * ‖v‖ ≤ ‖derivative z v‖ := by
  let P := (derivative fit).range.orthogonalProjection
  have hP : P.comp (derivative fit) = (derivative fit).rangeRestrict := by
    apply ContinuousLinearMap.ext
    intro v
    exact Submodule.orthogonalProjection_mem_subspace_eq_self
      ((derivative fit).rangeRestrict v)
  obtain ⟨R, hR, hRnorm⟩ := exists_normal_rangeRightInverse
    (derivative fit) hstrength hlower
  have hR' : (P.comp (derivative fit)).comp R =
      ContinuousLinearMap.id ℝ (derivative fit).range := by rwa [hP]
  have hPnorm : ‖P‖ ≤ 1 := (derivative fit).range.orthogonalProjection_norm_le
  have hcoeff : 2 * ‖R‖ * ‖P‖ ≤ 2 / strength := by
    calc
      2 * ‖R‖ * ‖P‖ ≤ 2 * (1 / strength) * 1 := by gcongr
      _ = 2 / strength := by ring
  filter_upwards [eventually_norm_le_mul_of_constantRank_projection derivative fit
    P R hcont hR' hrank] with z hz
  intro v hv
  have hnorm := (hz v hv).trans
    (mul_le_mul_of_nonneg_right hcoeff (norm_nonneg (derivative z v)))
  have hscaled := mul_le_mul_of_nonneg_left hnorm hstrength.le
  have hslope : strength * ((2 / strength) * ‖derivative z v‖) =
      2 * ‖derivative z v‖ := by field_simp [ne_of_gt hstrength]
  rw [hslope] at hscaled
  nlinarith

omit [FiniteDimensional ℝ E] in
/-- A squared transverse bound gives its square-root norm bound. -/
theorem transverse_norm_lowerBound_of_sq_lowerBound
    (A : E →L[ℝ] F) {a : ℝ} (ha : 0 ≤ a)
    (hlower : ∀ v, (∀ k, A k = 0 → ⟪v, k⟫ = 0) →
      a * ‖v‖ ^ 2 ≤ ‖A v‖ ^ 2) :
    ∀ v, (∀ k, A k = 0 → ⟪v, k⟫ = 0) → Real.sqrt a * ‖v‖ ≤ ‖A v‖ := by
  intro v hv
  have h := hlower v hv
  have hsq : (Real.sqrt a * ‖v‖) ^ 2 = a * ‖v‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt ha]
  have hnonneg := mul_nonneg (Real.sqrt_nonneg a) (norm_nonneg v)
  nlinarith [norm_nonneg (A v)]

/-- Source constant rank and the `c h` fit bound supply both local geometric inputs. -/
theorem exists_radius_fiberCurves_and_transverse_of_constantRank
    {F' : Type*} [NormedAddCommGroup F'] [InnerProductSpace ℝ F'] [FiniteDimensional ℝ F']
    (prediction : E → F') (derivative : E → E →L[ℝ] F') (fit : E) {c h : ℝ}
    (hc : 0 < c) (hh : 0 < h) (hsmooth : ContDiffAt ℝ 1 prediction fit)
    (hderiv : ∀ᶠ z in 𝓝 fit, HasFDerivAt prediction (derivative z) z)
    (hrank : ∀ᶠ z in 𝓝 fit,
      Module.finrank ℝ (derivative z).range = Module.finrank ℝ (derivative fit).range)
    (hlower : ∀ v, (∀ k, derivative fit k = 0 → ⟪v, k⟫ = 0) →
      (c * h) * ‖v‖ ^ 2 ≤ ‖derivative fit v‖ ^ 2) :
    ∃ radius > 0,
      KernelVectorsHaveFiberCurves prediction fit derivative radius ∧
      ∀ y, dist y fit < 2 * radius → ∀ v,
        (∀ k, derivative y k = 0 → ⟪v, k⟫ = 0) →
          (Real.sqrt (c * h) / 2) * ‖v‖ ≤ ‖derivative y v‖ := by
  have hch : 0 < c * h := mul_pos hc hh
  have hcont : ContinuousAt derivative fit :=
    (hsmooth.continuousAt_fderiv one_ne_zero).congr_of_eventuallyEq
      (hderiv.mono fun z hz => hz.fderiv.symm)
  have htrans := eventually_transverse_strength_ge_half_of_constantRank derivative fit
    (Real.sqrt_pos.mpr hch) hcont hrank
    (transverse_norm_lowerBound_of_sq_lowerBound (derivative fit) hch.le hlower)
  obtain ⟨r₁, hr₁, hcurves⟩ :=
    exists_radius_kernelVectorsHaveFiberCurves_of_constantRank prediction derivative fit
      hsmooth hderiv hrank
  obtain ⟨r₂, hr₂, hball⟩ := Metric.eventually_nhds_iff_ball.mp htrans
  let radius := min r₁ (r₂ / 2)
  have hrad : 0 < radius := lt_min hr₁ (half_pos hr₂)
  have hrad₁ : radius ≤ r₁ := min_le_left _ _
  have hrad₂ : radius ≤ r₂ / 2 := min_le_right _ _
  refine ⟨radius, hrad, ?_, ?_⟩
  · intro y hy hnear v hv
    exact hcurves y hy (hnear.trans_le (by linarith)) v hv
  · intro y hnear
    apply hball y
    change dist y fit < r₂
    linarith

/-- Rank zero means that the derivative itself is zero. -/
theorem derivative_eq_zero_of_finrank_range_eq_zero
    (A : E →L[ℝ] F) (hrank : Module.finrank ℝ A.range = 0) : A = 0 := by
  have hlinear : A.toLinearMap = 0 :=
    LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hrank)
  apply ContinuousLinearMap.ext
  intro v
  exact congrArg (fun L : E →ₗ[ℝ] F => L v) hlinear

/-- In the rank-zero case, straight lines are already locally exact-fiber curves. -/
theorem exists_fiberCurve_of_zeroRank
    (prediction : E → F) (derivative : E → E →L[ℝ] F) (y v : E)
    (hderiv : ∀ᶠ z in 𝓝 y, HasFDerivAt prediction (derivative z) z)
    (hrank : ∀ᶠ z in 𝓝 y, Module.finrank ℝ (derivative z).range = 0) :
    ∃ curve : ℝ → E, curve 0 = y ∧ HasDerivAt curve v 0 ∧
      ∀ᶠ t in 𝓝 (0 : ℝ), prediction (curve t) = prediction y := by
  let curve : ℝ → E := fun t => y + t • v
  have hcurve : ∀ t, HasDerivAt curve v t := by
    intro t
    simpa [curve] using ((hasDerivAt_id t).smul_const v).const_add y
  have hzero : curve 0 = y := by simp [curve]
  have htendsto : Tendsto curve (𝓝 0) (𝓝 y) := by
    simpa only [hzero] using (hcurve 0).continuousAt.tendsto
  have hpzero : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt (fun s => prediction (curve s)) 0 t := by
    filter_upwards [htendsto.eventually hderiv, htendsto.eventually hrank] with t htDeriv htRank
    have hz := derivative_eq_zero_of_finrank_range_eq_zero (derivative (curve t)) htRank
    simpa only [hz, ContinuousLinearMap.zero_apply] using htDeriv.comp_hasDerivAt t (hcurve t)
  refine ⟨curve, hzero, hcurve 0, ?_⟩
  simpa only [hzero] using
    eventually_eq_of_eventually_hasDerivAt_zero (fun t => prediction (curve t)) 0 hpzero

end JGR26SubjectivityMonoculture
