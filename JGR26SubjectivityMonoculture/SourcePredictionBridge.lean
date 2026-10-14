import JGR26SubjectivityMonoculture.LocalIdentificationStability
import JGR26SubjectivityMonoculture.HeterogeneityGeometry
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Pi

/-!
# Finite-array bridge for the October 13 source

All item and model factors are placed in one Euclidean array. This matters:
the ordinary product's supremum norm would not be the paper's sum-of-squares
parameter norm. Predictions likewise use a Euclidean array indexed by the
actual item-model cells.
-/

namespace JGR26SubjectivityMonoculture

open scoped BigOperators RealInnerProductSpace

noncomputable section

variable {K : ℕ} {Item Model : Type*} [Fintype Item] [Fintype Model]

/-- One Euclidean coordinate for each item/model latent-factor coordinate. -/
abbrev SourceFactorParameter (Item Model : Type*) (K : ℕ) :=
  EuclideanSpace ℝ ((Item ⊕ Model) × Fin K)

/-- The exact item-model prediction array, with its Euclidean norm. -/
abbrev SourcePredictionArray (Item Model : Type*) := EuclideanSpace ℝ (Item × Model)

/-- Evaluation of a factor-array coordinate is a continuous linear map. -/
def sourceFactorCoordinate (a : (Item ⊕ Model) × Fin K) :
    SourceFactorParameter Item Model K →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj a).comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : (Item ⊕ Model) × Fin K => ℝ)).toContinuousLinearMap

/-- The fitted item vector as a continuous linear projection of the full parameter. -/
def sourceItemFactor (i : Item) :
    SourceFactorParameter Item Model K →L[ℝ] EuclideanSpace ℝ (Fin K) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin K => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun k => sourceFactorCoordinate (Sum.inl i, k)))

/-- The fitted model vector as a continuous linear projection of the full parameter. -/
def sourceModelFactor (j : Model) :
    SourceFactorParameter Item Model K →L[ℝ] EuclideanSpace ℝ (Fin K) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin K => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun k => sourceFactorCoordinate (Sum.inr j, k)))

@[simp] theorem sourceItemFactor_apply (z : SourceFactorParameter Item Model K)
    (i : Item) (k : Fin K) : sourceItemFactor i z k = z (Sum.inl i, k) := rfl

@[simp] theorem sourceModelFactor_apply (z : SourceFactorParameter Item Model K)
    (j : Model) (k : Fin K) : sourceModelFactor j z k = z (Sum.inr j, k) := rfl

/-- The source prediction map for an arbitrary finite-dimensional latent link. -/
def sourcePrediction
    (link : EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin K) → ℝ)
    (z : SourceFactorParameter Item Model K) : SourcePredictionArray Item Model :=
  WithLp.toLp 2 (fun ij => link (sourceItemFactor ij.1 z, sourceModelFactor ij.2 z))

@[simp] theorem sourcePrediction_apply
    (link : EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin K) → ℝ)
    (z : SourceFactorParameter Item Model K) (i : Item) (j : Model) :
    sourcePrediction link z (i, j) = link (sourceItemFactor i z, sourceModelFactor j z) := rfl

/-- Source smoothness implies smoothness of the actual full prediction array. -/
theorem sourcePrediction_contDiff
    (link : EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin K) → ℝ)
    (hsmooth : ContDiff ℝ 2 link) :
    ContDiff ℝ 2 (sourcePrediction (Item := Item) (Model := Model) link) := by
  apply (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Item × Model => ℝ)).symm.contDiff.comp
  apply contDiff_pi.mpr
  intro ij
  have hi : ContDiff ℝ 2 (sourceItemFactor (K := K) (Model := Model) ij.1) :=
    (sourceItemFactor (K := K) (Model := Model) ij.1).contDiff
  have hj : ContDiff ℝ 2 (sourceModelFactor (K := K) (Item := Item) ij.2) :=
    (sourceModelFactor (K := K) (Item := Item) ij.2).contDiff
  exact hsmooth.comp (hi.prodMk hj)

/-- Exact observational equivalence is equality in every source item-model cell. -/
theorem source_exactPredictionFiber_eq
    (link : EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin K) → ℝ)
    (fit : SourceFactorParameter Item Model K) :
    exactPredictionFiber (sourcePrediction link) fit =
      {z | ∀ i j, link (sourceItemFactor i z, sourceModelFactor j z) =
        link (sourceItemFactor i fit, sourceModelFactor j fit)} := by
  ext z
  constructor
  · intro hz i j
    exact congrArg (fun a : SourcePredictionArray Item Model => a (i, j)) hz
  · intro hz
    apply PiLp.ext
    intro ij
    exact hz ij.1 ij.2

/-- The array norm is exactly the manuscript's sum of squared prediction errors. -/
theorem sourcePrediction_error_norm_sq
    (link : EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin K) → ℝ)
    (z fit : SourceFactorParameter Item Model K) :
    ‖sourcePrediction link z - sourcePrediction link fit‖ ^ 2 =
      ∑ i, ∑ j,
        (link (sourceItemFactor i z, sourceModelFactor j z) -
          link (sourceItemFactor i fit, sourceModelFactor j fit)) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  simp only [PiLp.sub_apply, sourcePrediction_apply, Real.norm_eq_abs, sq_abs]

/-- The parameter norm uses the source sum of item and model squared coordinates. -/
theorem sourceFactorParameter_norm_sq (z : SourceFactorParameter Item Model K) :
    ‖z‖ ^ 2 =
      (∑ i : Item, ∑ k : Fin K, (sourceItemFactor i z k) ^ 2) +
        ∑ j : Model, ∑ k : Fin K, (sourceModelFactor j z k) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Fintype.sum_sum_type]
  simp only [Real.norm_eq_abs, sq_abs, sourceItemFactor_apply, sourceModelFactor_apply]

/-- The source's local squared-error set agrees with the Euclidean-map set. -/
theorem source_localEquivalenceSet_eq
    (link : EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin K) → ℝ)
    (fit : SourceFactorParameter Item Model K) (radius epsilon : ℝ) :
    {z | dist z fit < radius ∧
      (∑ i, ∑ j,
        (link (sourceItemFactor i z, sourceModelFactor j z) -
          link (sourceItemFactor i fit, sourceModelFactor j fit)) ^ 2) ≤ epsilon ^ 2} =
      localPredictionEquivalenceSet (sourcePrediction link) fit radius epsilon := by
  ext z
  simp only [localPredictionEquivalenceSet, Set.mem_setOf_eq, sourcePrediction_error_norm_sq]

/-- Theorem 5 for the actual source arrays and displayed squared-error constraint. -/
theorem source_theorem5_local_heterogeneity
    (link : EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin K) → ℝ)
    (fit : SourceFactorParameter Item Model K) {c h : ℝ}
    (hc : 0 < c) (hh : 0 < h) (hsmooth : ContDiff ℝ 2 link)
    (hid : HasLocalIdentificationAt (sourcePrediction link) fit c h) :
    ∃ radius > 0, ∃ C > 0, ∀ epsilon > 0,
      sSup ((fun z => Metric.infDist z (exactPredictionFiber (sourcePrediction link) fit)) ''
        {z | dist z fit < radius ∧
          (∑ i, ∑ j,
            (link (sourceItemFactor i z, sourceModelFactor j z) -
              link (sourceItemFactor i fit, sourceModelFactor j fit)) ^ 2) ≤ epsilon ^ 2}) ≤
        (C / Real.sqrt h) * epsilon := by
  simpa only [source_localEquivalenceSet_eq] using
    localHeterogeneityStability_sup (sourcePrediction link) fit hc hh
      (sourcePrediction_contDiff link hsmooth) hid

/-- At fixed identification strength, the coefficient is uniform in heterogeneity. -/
theorem source_theorem5_uniform_coefficient
    (link : EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin K) → ℝ)
    (fit : SourceFactorParameter Item Model K) {c h : ℝ}
    (hc : 0 < c) (hh : 0 < h) (hsmooth : ContDiff ℝ 2 link)
    (hid : HasLocalIdentificationAt (sourcePrediction link) fit c h) :
    ∃ radius > 0, ∀ epsilon > 0,
      sSup ((fun z => Metric.infDist z (exactPredictionFiber (sourcePrediction link) fit)) ''
        {z | dist z fit < radius ∧
          (∑ i, ∑ j,
            (link (sourceItemFactor i z, sourceModelFactor j z) -
              link (sourceItemFactor i fit, sourceModelFactor j fit)) ^ 2) ≤ epsilon ^ 2}) ≤
        ((4 / Real.sqrt c) / Real.sqrt h) * epsilon := by
  obtain ⟨radius, hrad, hbound⟩ :=
    localHeterogeneityStability (sourcePrediction link) fit hc hh
      (sourcePrediction_contDiff link hsmooth) hid
  refine ⟨radius, hrad, ?_⟩
  intro epsilon hepsilon
  have hnonempty : ((fun z => Metric.infDist z
      (exactPredictionFiber (sourcePrediction link) fit)) ''
      {z | dist z fit < radius ∧
        (∑ i, ∑ j,
          (link (sourceItemFactor i z, sourceModelFactor j z) -
            link (sourceItemFactor i fit, sourceModelFactor j fit)) ^ 2) ≤ epsilon ^ 2}).Nonempty := by
    refine ⟨_, fit, ?_, rfl⟩
    exact ⟨by simpa using hrad, by simp; positivity⟩
  apply csSup_le hnonempty
  rintro _ ⟨z, hz, rfl⟩
  have hnorm : ‖sourcePrediction link z - sourcePrediction link fit‖ ≤ epsilon := by
    have hsq := hz.2
    rw [← sourcePrediction_error_norm_sq] at hsq
    nlinarith [norm_nonneg (sourcePrediction link z - sourcePrediction link fit)]
  exact (hbound z hz.1).trans
    (mul_le_mul_of_nonneg_left hnorm (by positivity))

end

end JGR26SubjectivityMonoculture
