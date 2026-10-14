import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# Constant rank of full-rank bilinear factor predictions

For injective factors `U : W → I` and `V : W → J`, the kernel of the derivative
of `U V†` consists exactly of the gauge directions `(U B, -V B†)`. The gauge
map is injective, so its image has dimension `(dim W)²`. Injective factors form
an open set, on which rank-nullity makes the prediction derivative rank constant.
-/

namespace JGR26SubjectivityMonoculture

open Filter Function Set
open scoped Topology InnerProduct

noncomputable section

variable {W I J : Type*}
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup I] [InnerProductSpace ℝ I] [FiniteDimensional ℝ I]
  [NormedAddCommGroup J] [InnerProductSpace ℝ J] [FiniteDimensional ℝ J]

/-- Adjoint is a real continuous linear map between the operator spaces. -/
def realAdjointMap : (W →L[ℝ] J) →L[ℝ] (J →L[ℝ] W) :=
  ({ toFun := fun V => V.adjoint
     map_add' := by intro V₁ V₂; exact map_add ContinuousLinearMap.adjoint V₁ V₂
     map_smul' := by intro c V; simp
   } : (W →L[ℝ] J) →ₗ[ℝ] (J →L[ℝ] W)).toContinuousLinearMap

@[simp] theorem realAdjointMap_apply (V : W →L[ℝ] J) : realAdjointMap V = V.adjoint := rfl

/-- The complete matrix of bilinear predictions. -/
def bilinearOperatorPrediction (factors : (W →L[ℝ] I) × (W →L[ℝ] J)) : J →L[ℝ] I :=
  factors.1.comp factors.2.adjoint

/-- The actual bilinear linearization `dU V† + U dV†`. -/
def bilinearOperatorDerivative (U : W →L[ℝ] I) (V : W →L[ℝ] J) :
    ((W →L[ℝ] I) × (W →L[ℝ] J)) →L[ℝ] (J →L[ℝ] I) :=
  ({ toFun := fun d => d.1.comp V.adjoint + U.comp d.2.adjoint
     map_add' := by
       intro d e
       simp only [Prod.fst_add, Prod.snd_add, map_add, ContinuousLinearMap.add_comp,
         ContinuousLinearMap.comp_add]
       abel
     map_smul' := by
       intro c d
       simp [smul_add]
   } : ((W →L[ℝ] I) × (W →L[ℝ] J)) →ₗ[ℝ] (J →L[ℝ] I)).toContinuousLinearMap

@[simp] theorem bilinearOperatorDerivative_apply
    (U : W →L[ℝ] I) (V : W →L[ℝ] J) (d : (W →L[ℝ] I) × (W →L[ℝ] J)) :
    bilinearOperatorDerivative U V d = d.1.comp V.adjoint + U.comp d.2.adjoint := rfl

/-- Infinitesimal invertible reparametrizations of the two factors. -/
def bilinearOperatorGauge (U : W →L[ℝ] I) (V : W →L[ℝ] J) :
    (W →L[ℝ] W) →ₗ[ℝ] ((W →L[ℝ] I) × (W →L[ℝ] J)) where
  toFun B := (U.comp B, -(V.comp B.adjoint))
  map_add' := by intro B C; simp [map_add, add_comm]
  map_smul' := by intro c B; simp [smul_neg]

omit [FiniteDimensional ℝ I] [FiniteDimensional ℝ J] in
@[simp] theorem bilinearOperatorGauge_apply
    (U : W →L[ℝ] I) (V : W →L[ℝ] J) (B : W →L[ℝ] W) :
    bilinearOperatorGauge U V B = (U.comp B, -(V.comp B.adjoint)) := rfl

/-- Every gauge direction has zero prediction derivative. -/
theorem bilinearOperatorDerivative_gauge_eq_zero
    (U : W →L[ℝ] I) (V : W →L[ℝ] J) (B : W →L[ℝ] W) :
    bilinearOperatorDerivative U V (bilinearOperatorGauge U V B) = 0 := by
  simp [ContinuousLinearMap.comp_assoc]

/-- Injectivity of a factor makes its Gram operator injective and hence surjective. -/
theorem adjoint_range_eq_top_of_injective (V : W →L[ℝ] J) (hV : Injective V) :
    V.adjoint.range = ⊤ := by
  have hgram : Injective (V.adjoint.comp V) := V.adjoint_comp_self_injective_iff.mpr hV
  have hgramSurj : Surjective (V.adjoint.comp V) :=
    (V.adjoint.comp V).toLinearMap.surjective_of_injective hgram
  exact LinearMap.range_eq_top.mpr (Surjective.of_comp hgramSurj)

/-- All zero-derivative perturbations arise from one infinitesimal gauge operator. -/
theorem bilinearOperatorDerivative_eq_zero_iff_gauge
    (U : W →L[ℝ] I) (V : W →L[ℝ] J) (hU : Injective U) (hV : Injective V)
    (d : (W →L[ℝ] I) × (W →L[ℝ] J)) :
    bilinearOperatorDerivative U V d = 0 ↔
      ∃ B : W →L[ℝ] W, d = bilinearOperatorGauge U V B := by
  constructor
  · intro hd
    have hzero : d.1.comp V.adjoint + U.comp d.2.adjoint = 0 := hd
    obtain ⟨R, hR⟩ := V.adjoint.exists_right_inverse_of_surjective
      (adjoint_range_eq_top_of_injective V hV)
    let B : W →L[ℝ] W := -(d.2.adjoint.comp R)
    have hdU : d.1 = U.comp B := by
      have h := congrArg (fun T : J →L[ℝ] I => T.comp R) hzero
      simp only [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_assoc, hR,
        ContinuousLinearMap.comp_id, ContinuousLinearMap.zero_comp] at h
      simpa only [B, ContinuousLinearMap.comp_neg] using eq_neg_of_add_eq_zero_left h
    have hmiddle : B.comp V.adjoint + d.2.adjoint = 0 := by
      apply ContinuousLinearMap.ext
      intro j
      apply hU
      have h := congrArg (fun T : J →L[ℝ] I => T j) hzero
      rw [hdU] at h
      simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.zero_apply, map_add, map_zero] using h
    have hdV : d.2 = -(V.comp B.adjoint) := by
      have h := congrArg (fun T : J →L[ℝ] W => T.adjoint) hmiddle
      simp only [map_add, ContinuousLinearMap.adjoint_comp,
        ContinuousLinearMap.adjoint_adjoint, map_zero] at h
      exact eq_neg_of_add_eq_zero_right h
    refine ⟨B, ?_⟩
    exact Prod.ext hdU hdV
  · rintro ⟨B, rfl⟩
    exact bilinearOperatorDerivative_gauge_eq_zero U V B

/-- The bilinear derivative kernel is the image of the full gauge map. -/
theorem bilinearOperatorDerivative_ker_eq_gauge_range
    (U : W →L[ℝ] I) (V : W →L[ℝ] J) (hU : Injective U) (hV : Injective V) :
    (bilinearOperatorDerivative U V).ker = (bilinearOperatorGauge U V).range := by
  ext d
  simp only [LinearMap.mem_ker, LinearMap.mem_range]
  change bilinearOperatorDerivative U V d = 0 ↔ ∃ B, bilinearOperatorGauge U V B = d
  rw [bilinearOperatorDerivative_eq_zero_iff_gauge U V hU hV d]
  exact exists_congr fun B => eq_comm

omit [FiniteDimensional ℝ I] [FiniteDimensional ℝ J] in
/-- The gauge operator is uniquely determined by the item-factor perturbation. -/
theorem bilinearOperatorGauge_injective
    (U : W →L[ℝ] I) (V : W →L[ℝ] J) (hU : Injective U) :
    Injective (bilinearOperatorGauge U V) := by
  intro B C hBC
  apply ContinuousLinearMap.ext
  intro w
  apply hU
  have hfirst := congrArg Prod.fst hBC
  exact congrArg (fun T : W →L[ℝ] I => T w) hfirst

/-- The linearization is the Fréchet derivative of the actual prediction map. -/
theorem hasFDerivAt_bilinearOperatorPrediction
    (factors : (W →L[ℝ] I) × (W →L[ℝ] J)) :
    HasFDerivAt bilinearOperatorPrediction
      (bilinearOperatorDerivative factors.1 factors.2) factors := by
  have hleft : HasFDerivAt (fun p : (W →L[ℝ] I) × (W →L[ℝ] J) => p.1)
      (ContinuousLinearMap.fst ℝ _ _) factors := hasFDerivAt_fst
  have hright : HasFDerivAt (fun p : (W →L[ℝ] I) × (W →L[ℝ] J) => p.2.adjoint)
      (realAdjointMap.comp (ContinuousLinearMap.snd ℝ _ _)) factors :=
    (realAdjointMap (W := W) (J := J)).hasFDerivAt.comp factors hasFDerivAt_snd
  convert hleft.clm_comp hright using 1
  apply ContinuousLinearMap.ext
  intro d
  simp [bilinearOperatorDerivative, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply, add_comm]

omit [FiniteDimensional ℝ I] in
/-- Bilinear predictions are smooth at every factor pair. -/
theorem contDiff_bilinearOperatorPrediction {n : WithTop ℕ∞} :
    ContDiff ℝ n (bilinearOperatorPrediction :
      ((W →L[ℝ] I) × (W →L[ℝ] J)) → (J →L[ℝ] I)) :=
  contDiff_fst.clm_comp ((realAdjointMap (W := W) (J := J)).contDiff.comp contDiff_snd)

/-- Endomorphisms of the latent factor space have dimension `(dim W)²`. -/
theorem finrank_latentOperatorEnd : Module.finrank ℝ (W →L[ℝ] W) =
    (Module.finrank ℝ W) ^ 2 := by
  have h := (LinearMap.toContinuousLinearMap : (W →ₗ[ℝ] W) ≃ₗ[ℝ] (W →L[ℝ] W)).finrank_eq
  rw [Module.finrank_linearMap] at h
  exact h.symm.trans (pow_two (Module.finrank ℝ W)).symm

/-- The full-rank bilinear derivative kernel has exactly the gauge dimension. -/
theorem finrank_bilinearOperatorDerivative_ker
    (U : W →L[ℝ] I) (V : W →L[ℝ] J) (hU : Injective U) (hV : Injective V) :
    Module.finrank ℝ (bilinearOperatorDerivative U V).ker = (Module.finrank ℝ W) ^ 2 := by
  rw [bilinearOperatorDerivative_ker_eq_gauge_range U V hU hV,
    LinearMap.finrank_range_of_inj (bilinearOperatorGauge_injective U V hU)]
  exact finrank_latentOperatorEnd

/-- Rank-nullity expresses the full-rank prediction derivative rank by fixed dimensions. -/
theorem finrank_bilinearOperatorDerivative_range
    (U : W →L[ℝ] I) (V : W →L[ℝ] J) (hU : Injective U) (hV : Injective V) :
    Module.finrank ℝ (bilinearOperatorDerivative U V).range =
      Module.finrank ℝ ((W →L[ℝ] I) × (W →L[ℝ] J)) - (Module.finrank ℝ W) ^ 2 := by
  have h := (bilinearOperatorDerivative U V).toLinearMap.finrank_range_add_finrank_ker
  rw [finrank_bilinearOperatorDerivative_ker U V hU hV] at h
  exact Nat.eq_sub_of_add_eq h

/-- Both factors are full column rank. -/
def FullRankOperatorFactors (factors : (W →L[ℝ] I) × (W →L[ℝ] J)) : Prop :=
  Injective factors.1 ∧ Injective factors.2

omit [FiniteDimensional ℝ I] [FiniteDimensional ℝ J] in
/-- The full-rank factor locus is open. -/
theorem isOpen_fullRankOperatorFactors :
    IsOpen {factors : (W →L[ℝ] I) × (W →L[ℝ] J) | FullRankOperatorFactors factors} := by
  exact (ContinuousLinearMap.isOpen_injective.preimage continuous_fst).inter
    (ContinuousLinearMap.isOpen_injective.preimage continuous_snd)

/-- The actual derivative has locally constant rank near every full-rank factor pair. -/
theorem eventually_bilinearOperatorDerivative_rank_eq
    (factors : (W →L[ℝ] I) × (W →L[ℝ] J)) (hfull : FullRankOperatorFactors factors) :
    ∀ᶠ p in 𝓝 factors,
      Module.finrank ℝ (bilinearOperatorDerivative p.1 p.2).range =
        Module.finrank ℝ (bilinearOperatorDerivative factors.1 factors.2).range := by
  filter_upwards [isOpen_fullRankOperatorFactors.mem_nhds hfull] with p hp
  rw [finrank_bilinearOperatorDerivative_range p.1 p.2 hp.1 hp.2,
    finrank_bilinearOperatorDerivative_range factors.1 factors.2 hfull.1 hfull.2]

/-- Local constant rank is stated directly for the Fréchet derivative of predictions. -/
theorem eventually_fderiv_bilinearOperatorPrediction_rank_eq
    (factors : (W →L[ℝ] I) × (W →L[ℝ] J)) (hfull : FullRankOperatorFactors factors) :
    ∀ᶠ p in 𝓝 factors,
      Module.finrank ℝ (fderiv ℝ bilinearOperatorPrediction p).range =
        Module.finrank ℝ (fderiv ℝ bilinearOperatorPrediction factors).range := by
  filter_upwards [eventually_bilinearOperatorDerivative_rank_eq factors hfull] with p hp
  rw [(hasFDerivAt_bilinearOperatorPrediction p).fderiv,
    (hasFDerivAt_bilinearOperatorPrediction factors).fderiv]
  exact hp

/-- Model-factor perturbations vanish on the latent coordinate subspace held fixed. -/
def fixedOperatorPerturbations (C : Submodule ℝ W) :
    Submodule ℝ ((W →L[ℝ] I) × (W →L[ℝ] J)) where
  carrier := {d | ∀ w ∈ C, d.2 w = 0}
  zero_mem' := by intro w hw; rfl
  add_mem' := by intro d e hd he w hw; simp [hd w hw, he w hw]
  smul_mem' := by intro c d hd w hw; simp [hd w hw]

/-- Admissible infinitesimal gauges have adjoint annihilating the fixed coordinate subspace. -/
def fixedOperatorGaugeDirections (C : Submodule ℝ W) : Submodule ℝ (W →L[ℝ] W) where
  carrier := {B | ∀ w ∈ C, B.adjoint w = 0}
  zero_mem' := by intro w hw; simp
  add_mem' := by intro B D hB hD w hw; simp [map_add, hB w hw, hD w hw]
  smul_mem' := by intro c B hB w hw; simp [hB w hw]

/-- The gauge map restricted to admissible coordinate perturbations. -/
def bilinearOperatorGaugeWithin (C : Submodule ℝ W)
    (U : W →L[ℝ] I) (V : W →L[ℝ] J) :
    fixedOperatorGaugeDirections C →ₗ[ℝ] fixedOperatorPerturbations (I := I) (J := J) C where
  toFun B := ⟨bilinearOperatorGauge U V B, by
    intro w hw
    change -(V (B.val.adjoint w)) = 0
    rw [B.property w hw, map_zero, neg_zero]⟩
  map_add' := by intro B D; exact Subtype.ext ((bilinearOperatorGauge U V).map_add B D)
  map_smul' := by intro c B; exact Subtype.ext ((bilinearOperatorGauge U V).map_smul c B)

/-- The derivative on the actual fixed-coordinate tangent space. -/
def bilinearOperatorDerivativeWithin (C : Submodule ℝ W)
    (U : W →L[ℝ] I) (V : W →L[ℝ] J) :
    fixedOperatorPerturbations (I := I) (J := J) C →L[ℝ] (J →L[ℝ] I) :=
  (bilinearOperatorDerivative U V).comp (fixedOperatorPerturbations C).subtypeL

/-- On injective factors, the admissible derivative kernel is exactly the admissible gauge image. -/
theorem bilinearOperatorDerivativeWithin_ker_eq_gauge_range
    (C : Submodule ℝ W) (U : W →L[ℝ] I) (V : W →L[ℝ] J)
    (hU : Injective U) (hV : Injective V) :
    (bilinearOperatorDerivativeWithin C U V).ker = (bilinearOperatorGaugeWithin C U V).range := by
  ext d
  constructor
  · intro hd
    have hz : bilinearOperatorDerivative U V d.val = 0 := hd
    obtain ⟨B, hB⟩ := (bilinearOperatorDerivative_eq_zero_iff_gauge U V hU hV d.val).mp hz
    have hfixed : B ∈ fixedOperatorGaugeDirections C := by
      intro w hw
      apply hV
      have hv := d.property w hw
      rw [hB] at hv
      change -(V (B.adjoint w)) = 0 at hv
      simpa only [map_zero, neg_eq_zero] using hv
    refine ⟨⟨B, hfixed⟩, ?_⟩
    exact Subtype.ext hB.symm
  · rintro ⟨B, rfl⟩
    exact bilinearOperatorDerivative_gauge_eq_zero U V B.val

omit [FiniteDimensional ℝ I] [FiniteDimensional ℝ J] in
/-- Restricting gauges to fixed coordinates preserves injectivity of their parameterization. -/
theorem bilinearOperatorGaugeWithin_injective
    (C : Submodule ℝ W) (U : W →L[ℝ] I) (V : W →L[ℝ] J) (hU : Injective U) :
    Injective (bilinearOperatorGaugeWithin C U V) := by
  intro B D hBD
  apply Subtype.ext
  apply bilinearOperatorGauge_injective U V hU
  exact congrArg Subtype.val hBD

/-- The admissible kernel dimension is independent of either full-rank factor. -/
theorem finrank_bilinearOperatorDerivativeWithin_ker
    (C : Submodule ℝ W) (U : W →L[ℝ] I) (V : W →L[ℝ] J)
    (hU : Injective U) (hV : Injective V) :
    Module.finrank ℝ (bilinearOperatorDerivativeWithin C U V).ker =
      Module.finrank ℝ (fixedOperatorGaugeDirections C) := by
  rw [bilinearOperatorDerivativeWithin_ker_eq_gauge_range C U V hU hV,
    LinearMap.finrank_range_of_inj (bilinearOperatorGaugeWithin_injective C U V hU)]

/-- The derivative rank on fixed-coordinate perturbations has a factor-independent formula. -/
theorem finrank_bilinearOperatorDerivativeWithin_range
    (C : Submodule ℝ W) (U : W →L[ℝ] I) (V : W →L[ℝ] J)
    (hU : Injective U) (hV : Injective V) :
    Module.finrank ℝ (bilinearOperatorDerivativeWithin C U V).range =
      Module.finrank ℝ (fixedOperatorPerturbations (I := I) (J := J) C) -
        Module.finrank ℝ (fixedOperatorGaugeDirections C) := by
  have h := (bilinearOperatorDerivativeWithin C U V).toLinearMap.finrank_range_add_finrank_ker
  rw [finrank_bilinearOperatorDerivativeWithin_ker C U V hU hV] at h
  exact Nat.eq_sub_of_add_eq h

/-- Constant rank also holds on the fixed-coordinate admissible tangent space. -/
theorem eventually_bilinearOperatorDerivativeWithin_rank_eq
    (C : Submodule ℝ W) (factors : (W →L[ℝ] I) × (W →L[ℝ] J))
    (hfull : FullRankOperatorFactors factors) :
    ∀ᶠ p in 𝓝 factors,
      Module.finrank ℝ (bilinearOperatorDerivativeWithin C p.1 p.2).range =
        Module.finrank ℝ (bilinearOperatorDerivativeWithin C factors.1 factors.2).range := by
  filter_upwards [isOpen_fullRankOperatorFactors.mem_nhds hfull] with p hp
  rw [finrank_bilinearOperatorDerivativeWithin_range C p.1 p.2 hp.1 hp.2,
    finrank_bilinearOperatorDerivativeWithin_range C factors.1 factors.2 hfull.1 hfull.2]

/-- Predictions on the affine parameter space retaining all fixed model coordinates. -/
def bilinearOperatorPredictionWithin (C : Submodule ℝ W)
    (factors : (W →L[ℝ] I) × (W →L[ℝ] J))
    (d : fixedOperatorPerturbations (I := I) (J := J) C) : J →L[ℝ] I :=
  bilinearOperatorPrediction (factors + d.val)

/-- Restricting the prediction map to fixed coordinates has exactly the restricted derivative. -/
theorem hasFDerivAt_bilinearOperatorPredictionWithin
    (C : Submodule ℝ W) (factors : (W →L[ℝ] I) × (W →L[ℝ] J))
    (d : fixedOperatorPerturbations (I := I) (J := J) C) :
    HasFDerivAt (bilinearOperatorPredictionWithin C factors)
      (bilinearOperatorDerivativeWithin C (factors + d.val).1 (factors + d.val).2) d := by
  have hsub : HasFDerivAt
      (fun e : fixedOperatorPerturbations (I := I) (J := J) C => e.val)
      (fixedOperatorPerturbations (I := I) (J := J) C).subtypeL d :=
    (fixedOperatorPerturbations (I := I) (J := J) C).subtypeL.hasFDerivAt
  have harg : HasFDerivAt
      (fun e : fixedOperatorPerturbations (I := I) (J := J) C => factors + e.val)
      (fixedOperatorPerturbations (I := I) (J := J) C).subtypeL d := by
    exact HasFDerivAt.const_add (𝕜 := ℝ)
      (E := fixedOperatorPerturbations (I := I) (J := J) C)
      (F := (W →L[ℝ] I) × (W →L[ℝ] J)) factors hsub
  exact HasFDerivAt.comp (𝕜 := ℝ)
    (E := fixedOperatorPerturbations (I := I) (J := J) C)
    (F := (W →L[ℝ] I) × (W →L[ℝ] J)) (G := J →L[ℝ] I) d
    (hasFDerivAt_bilinearOperatorPrediction (factors + d.val)) harg

omit [FiniteDimensional ℝ I] in
/-- The affine fixed-coordinate prediction map is smooth. -/
theorem contDiff_bilinearOperatorPredictionWithin {n : WithTop ℕ∞}
    (C : Submodule ℝ W) (factors : (W →L[ℝ] I) × (W →L[ℝ] J)) :
    ContDiff ℝ n (bilinearOperatorPredictionWithin C factors) := by
  let inclusion : fixedOperatorPerturbations (I := I) (J := J) C →L[ℝ]
      ((W →L[ℝ] I) × (W →L[ℝ] J)) := (fixedOperatorPerturbations C).subtypeL
  have hsub : ContDiff ℝ n
      (fun e : fixedOperatorPerturbations (I := I) (J := J) C => e.val) := by
    exact ContinuousLinearMap.contDiff (𝕜 := ℝ)
      (E := fixedOperatorPerturbations (I := I) (J := J) C)
      (F := (W →L[ℝ] I) × (W →L[ℝ] J)) inclusion
  exact contDiff_bilinearOperatorPrediction.comp (contDiff_const.add hsub)

/-- Source fixed coordinates preserve local constant rank for the actual affine prediction map. -/
theorem eventually_fderiv_bilinearOperatorPredictionWithin_rank_eq
    (C : Submodule ℝ W) (factors : (W →L[ℝ] I) × (W →L[ℝ] J))
    (hfull : FullRankOperatorFactors factors) :
    ∀ᶠ d in 𝓝 (0 : fixedOperatorPerturbations (I := I) (J := J) C),
      Module.finrank ℝ (fderiv ℝ (bilinearOperatorPredictionWithin C factors) d).range =
        Module.finrank ℝ (fderiv ℝ (bilinearOperatorPredictionWithin C factors) 0).range := by
  have htendsto : Tendsto
      (fun d : fixedOperatorPerturbations (I := I) (J := J) C => factors + d.val)
      (𝓝 0) (𝓝 factors) := by
    have harg : Continuous
        (fun d : fixedOperatorPerturbations (I := I) (J := J) C => factors + d.val) :=
      continuous_const.add continuous_subtype_val
    convert harg.tendsto 0 using 1
    simp
  filter_upwards [htendsto.eventually
    (eventually_bilinearOperatorDerivativeWithin_rank_eq C factors hfull)] with d hd
  rw [(hasFDerivAt_bilinearOperatorPredictionWithin C factors d).fderiv,
    (hasFDerivAt_bilinearOperatorPredictionWithin C factors 0).fderiv]
  have hzero : factors +
      ((0 : fixedOperatorPerturbations (I := I) (J := J) C) :
        (W →L[ℝ] I) × (W →L[ℝ] J)) = factors := by simp
  rw [hzero]
  exact hd

end

end JGR26SubjectivityMonoculture
