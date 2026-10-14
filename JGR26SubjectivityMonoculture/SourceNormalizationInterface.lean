import JGR26SubjectivityMonoculture.BalancedSourceBridge
import JGR26SubjectivityMonoculture.BalancedNormalizationExamples

/-!
# Normalization of the fitted source representation

For an unrestricted invertible bilinear link, the canonical convention chooses
an exact balanced representation in the fixed latent dimension. Its
heterogeneity is the singular value at that dimension, including zero for
rank-deficient fits. Other links and fixed-coordinate models use a specified
admissible exact representation. Maximizing heterogeneity alone does not imply
balance.
-/

namespace JGR26SubjectivityMonoculture

open Module Function Set
open scoped BigOperators RealInnerProductSpace

noncomputable section

variable {K : ℕ} {Item Model : Type*} [Fintype Item] [Fintype Model]

/-- A specified admissible representation of the fitted probability array. -/
def sourceSpecifiedAdmissibleFit
    (link : EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin K) → ℝ)
    (admissible : Set (SourceFactorParameter Item Model K))
    (probabilities : SourcePredictionArray Item Model)
    (fit : SourceFactorParameter Item Model K) : Prop :=
  fit ∈ admissible ∧ sourcePrediction link fit = probabilities

/-- An attained finite maximum over admissible exact representations of one fitted array. -/
def sourceMaximumHeterogeneityFit (hK : 0 < K)
    (link : EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin K) → ℝ)
    (admissible : Set (SourceFactorParameter Item Model K))
    (probabilities : SourcePredictionArray Item Model)
    (fit : SourceFactorParameter Item Model K) : Prop :=
  fit ∈ admissible ∧ sourcePrediction link fit = probabilities ∧
    ∀ z : SourceFactorParameter Item Model K,
      z ∈ admissible → sourcePrediction link z = probabilities →
        sourceHeterogeneity hK z ≤ sourceHeterogeneity hK fit

/-- The canonical unrestricted convention: exact fitted probabilities and equal actual Grams. -/
def sourceBalancedNormalizedFit (g : ℝ → ℝ)
    (probabilities : SourcePredictionArray Item Model)
    (fit : SourceFactorParameter Item Model K) : Prop :=
  sourcePrediction (fun uv => g ⟪uv.1, uv.2⟫) fit = probabilities ∧
    sourceFactorGramMatrix (fun i k => sourceItemFactor i fit k) =
      sourceFactorGramMatrix (fun j k => sourceModelFactor j fit k)

/-- The source's intrinsic heterogeneity at its fixed positive latent dimension. -/
def sourceIntrinsicBilinearHeterogeneity (_hK : 0 < K)
    (inverseLink : ℝ → ℝ) (probabilities : SourcePredictionArray Item Model) : ℝ :=
  (matrixEuclideanOperatorEquiv
    (Matrix.of (fun i j => inverseLink (probabilities (i, j))))).toLinearMap.singularValues (K - 1)

/-- Covariance heterogeneity is always nonnegative. -/
theorem sourceHeterogeneity_nonneg (hK : 0 < K)
    (fit : SourceFactorParameter Item Model K) : 0 ≤ sourceHeterogeneity hK fit := by
  apply (sourceHeterogeneity_lowerBound_iff hK fit 0).mpr
  constructor <;> intro x <;> simp only [zero_mul]
  · exact Finset.sum_nonneg fun i _ => sq_nonneg _
  · exact Finset.sum_nonneg fun j _ => sq_nonneg _

/-- The fitted bilinear matrix never exceeds the latent dimension in rank. -/
theorem sourceBilinearMatrix_rank_le_dimension
    (fit : SourceFactorParameter Item Model K) :
    finrank ℝ (matrixEuclideanOperatorEquiv (sourceBilinearMatrix fit)).toLinearMap.range ≤ K := by
  rw [sourceBilinearMatrix_operator]
  have hle : finrank ℝ
      ((sourceFactorOperatorEquiv fit).1.toLinearMap ∘ₗ
        (sourceFactorOperatorEquiv fit).2.toLinearMap.adjoint).range ≤
      finrank ℝ (sourceFactorOperatorEquiv fit).1.toLinearMap.range :=
    Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)
  have hdim : finrank ℝ (sourceFactorOperatorEquiv fit).1.toLinearMap.range ≤ K := by
    simpa only [finrank_euclideanSpace_fin] using
      (sourceFactorOperatorEquiv fit).1.toLinearMap.finrank_range_le
  exact hle.trans hdim

/-- Every representation of a rank-deficient matrix has zero covariance heterogeneity. -/
theorem sourceHeterogeneity_eq_zero_of_rank_lt (hK : 0 < K)
    (fit : SourceFactorParameter Item Model K)
    (hrank : finrank ℝ (matrixEuclideanOperatorEquiv (sourceBilinearMatrix fit)).toLinearMap.range < K) :
    sourceHeterogeneity hK fit = 0 := by
  apply le_antisymm _ (sourceHeterogeneity_nonneg hK fit)
  by_contra h
  have hh : 0 < sourceHeterogeneity hK fit := lt_of_not_ge h
  obtain ⟨hU, hV⟩ := sourceHeterogeneity_lowerBounds hK fit
  have hf := sourceFactorOperator_fullRank_of_gramLowerBounds fit hh hU hV
  have heq := sourceBilinearMatrix_rank_of_fullRank fit hf
  omega

/-- The first `r` coordinate vectors embed the rank-dimensional spectral factors into `K` coordinates. -/
def sourceCoordinateEmbedding {r : ℕ} (hr : r ≤ K) :
    EuclideanSpace ℝ (Fin r) →ₗ[ℝ] EuclideanSpace ℝ (Fin K) :=
  weightedSynthesis (fun i => EuclideanSpace.single (Fin.castLE hr i) (1 : ℝ)) (fun _ => 1)

/-- Coordinate padding followed by its adjoint recovers every original latent coordinate. -/
theorem sourceCoordinateEmbedding_adjoint_comp {r : ℕ} (hr : r ≤ K) :
    (sourceCoordinateEmbedding hr).adjoint ∘ₗ sourceCoordinateEmbedding hr = LinearMap.id := by
  have hw : Orthonormal ℝ (fun i : Fin r => EuclideanSpace.single (Fin.castLE hr i) (1 : ℝ)) :=
    (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin K)).comp (Fin.castLE hr)
      (fun i j hij => Fin.ext (congrArg (fun k : Fin K => k.val) hij))
  ext x i
  simpa only [sourceCoordinateEmbedding, LinearMap.comp_apply, LinearMap.id_apply,
    one_pow, one_mul] using weightedSynthesis_gram_apply _ hw (fun _ => (1 : ℝ)) x i

section Padding

variable {E H F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]

omit [FiniteDimensional ℝ F] in
/-- Isometric padding of both factors leaves their bilinear product unchanged. -/
theorem sourcePaddedFactors_product (U : E →ₗ[ℝ] F) (V : E →ₗ[ℝ] G)
    (J : E →ₗ[ℝ] H) (hJ : J.adjoint ∘ₗ J = LinearMap.id) :
    (U ∘ₗ J.adjoint) ∘ₗ (V ∘ₗ J.adjoint).adjoint = U ∘ₗ V.adjoint := by
  rw [LinearMap.adjoint_comp, LinearMap.adjoint_adjoint]
  ext y
  have h := LinearMap.congr_fun hJ (V.adjoint y)
  exact congrArg U h

/-- Isometric padding preserves equality of the two covariance Grams. -/
theorem sourcePaddedFactors_balanced (U : E →ₗ[ℝ] F) (V : E →ₗ[ℝ] G)
    (J : E →ₗ[ℝ] H) (hbal : U.adjoint ∘ₗ U = V.adjoint ∘ₗ V) :
    (U ∘ₗ J.adjoint).adjoint ∘ₗ (U ∘ₗ J.adjoint) =
      (V ∘ₗ J.adjoint).adjoint ∘ₗ (V ∘ₗ J.adjoint) := by
  rw [LinearMap.adjoint_comp, LinearMap.adjoint_comp, LinearMap.adjoint_adjoint]
  ext x
  exact congrArg J (LinearMap.congr_fun hbal (J.adjoint x))

end Padding

/-- Actual `K`-coordinate source arrays obtained by padding the spectral balanced factors. -/
def sourcePaddedBalancedFit (Θ : Matrix Item Model ℝ)
    (hrank : finrank ℝ (matrixEuclideanOperatorEquiv Θ).toLinearMap.range ≤ K) :
    SourceFactorParameter Item Model K :=
  sourceFactorOperatorEquiv.symm
    (((balancedLeftFactor (matrixEuclideanOperatorEquiv Θ).toLinearMap) ∘ₗ
      (sourceCoordinateEmbedding hrank).adjoint).toContinuousLinearMap,
     ((balancedRightFactor (matrixEuclideanOperatorEquiv Θ).toLinearMap) ∘ₗ
      (sourceCoordinateEmbedding hrank).adjoint).toContinuousLinearMap)

@[simp] theorem sourcePaddedBalancedFit_left_operator (Θ : Matrix Item Model ℝ)
    (hrank : finrank ℝ (matrixEuclideanOperatorEquiv Θ).toLinearMap.range ≤ K) :
    (sourceFactorOperatorEquiv (sourcePaddedBalancedFit Θ hrank)).1.toLinearMap =
      balancedLeftFactor (matrixEuclideanOperatorEquiv Θ).toLinearMap ∘ₗ
        (sourceCoordinateEmbedding hrank).adjoint := by
  simp only [sourcePaddedBalancedFit, ContinuousLinearEquiv.apply_symm_apply]
  rfl

@[simp] theorem sourcePaddedBalancedFit_right_operator (Θ : Matrix Item Model ℝ)
    (hrank : finrank ℝ (matrixEuclideanOperatorEquiv Θ).toLinearMap.range ≤ K) :
    (sourceFactorOperatorEquiv (sourcePaddedBalancedFit Θ hrank)).2.toLinearMap =
      balancedRightFactor (matrixEuclideanOperatorEquiv Θ).toLinearMap ∘ₗ
        (sourceCoordinateEmbedding hrank).adjoint := by
  simp only [sourcePaddedBalancedFit, ContinuousLinearEquiv.apply_symm_apply]
  rfl

/-- Padded balanced source arrays reconstruct the fitted matrix without a full-rank hypothesis. -/
theorem sourcePaddedBalancedFit_product (Θ : Matrix Item Model ℝ)
    (hrank : finrank ℝ (matrixEuclideanOperatorEquiv Θ).toLinearMap.range ≤ K) :
    sourceBilinearMatrix (sourcePaddedBalancedFit Θ hrank) = Θ := by
  apply matrix_eq_of_euclideanOperator_eq
  exact (sourceBilinearMatrix_operator (sourcePaddedBalancedFit Θ hrank)).trans
    ((congrArg₂ (fun
      (U : EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ Item)
      (V : EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ Model) => U ∘ₗ V.adjoint)
      (sourcePaddedBalancedFit_left_operator Θ hrank)
      (sourcePaddedBalancedFit_right_operator Θ hrank)).trans
      ((sourcePaddedFactors_product
        (balancedLeftFactor (matrixEuclideanOperatorEquiv Θ).toLinearMap)
        (balancedRightFactor (matrixEuclideanOperatorEquiv Θ).toLinearMap)
        (sourceCoordinateEmbedding hrank) (sourceCoordinateEmbedding_adjoint_comp hrank)).trans
        (balancedFactors_product_eq (matrixEuclideanOperatorEquiv Θ).toLinearMap)))

/-- The padded arrays have equal actual source covariance matrices in all ranks. -/
theorem sourcePaddedBalancedFit_balanced (Θ : Matrix Item Model ℝ)
    (hrank : finrank ℝ (matrixEuclideanOperatorEquiv Θ).toLinearMap.range ≤ K) :
    sourceFactorGramMatrix (fun i k => sourceItemFactor i (sourcePaddedBalancedFit Θ hrank) k) =
      sourceFactorGramMatrix (fun j k => sourceModelFactor j (sourcePaddedBalancedFit Θ hrank) k) := by
  apply (sourceFactorGramMatrix_eq_iff_operator_balance _).mpr
  have hU := congrArg (fun U : EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ Item => U.adjoint ∘ₗ U)
    (sourcePaddedBalancedFit_left_operator Θ hrank)
  have hV := congrArg (fun V : EuclideanSpace ℝ (Fin K) →ₗ[ℝ] EuclideanSpace ℝ Model => V.adjoint ∘ₗ V)
    (sourcePaddedBalancedFit_right_operator Θ hrank)
  exact hU.trans ((sourcePaddedFactors_balanced
    (balancedLeftFactor (matrixEuclideanOperatorEquiv Θ).toLinearMap)
    (balancedRightFactor (matrixEuclideanOperatorEquiv Θ).toLinearMap)
    (sourceCoordinateEmbedding hrank)
    (balancedFactors_gram_eq (matrixEuclideanOperatorEquiv Θ).toLinearMap)).trans hV.symm)

/-- A balanced exact representation exists at the original fixed dimension, including rank zero. -/
theorem sourceBalancedNormalizedFit_exists (g : ℝ → ℝ)
    (fit : SourceFactorParameter Item Model K) :
    ∃ z : SourceFactorParameter Item Model K,
      sourceBalancedNormalizedFit g
        (sourcePrediction (fun uv => g ⟪uv.1, uv.2⟫) fit) z := by
  let hrank := sourceBilinearMatrix_rank_le_dimension fit
  refine ⟨sourcePaddedBalancedFit (sourceBilinearMatrix fit) hrank, ?_,
    sourcePaddedBalancedFit_balanced _ hrank⟩
  apply PiLp.ext
  rintro ⟨i, j⟩
  rw [sourceBilinearPrediction_apply, sourceBilinearPrediction_apply,
    sourcePaddedBalancedFit_product]

/-- Adopted unrestricted normalization: exact balanced attainment at the fixed latent dimension,
with the intrinsic value determined by the actual inverse-link probability matrix. -/
def sourceUnrestrictedNormalizationSpec (hK : 0 < K)
    (g inverseLink : ℝ → ℝ) (fit : SourceFactorParameter Item Model K) : Prop :=
  LeftInverse inverseLink g → ∃ z : SourceFactorParameter Item Model K,
    sourceBalancedNormalizedFit g
      (sourcePrediction (fun uv => g ⟪uv.1, uv.2⟫) fit) z ∧
    sourceMaximumHeterogeneityFit hK (fun uv => g ⟪uv.1, uv.2⟫) Set.univ
      (sourcePrediction (fun uv => g ⟪uv.1, uv.2⟫) fit) z ∧
    sourceHeterogeneity hK z = sourceIntrinsicBilinearHeterogeneity hK inverseLink
      (sourcePrediction (fun uv => g ⟪uv.1, uv.2⟫) fit)

/-- The fixed-dimensional unrestricted normalization exists in every rank. -/
theorem sourceUnrestrictedNormalization (hK : 0 < K)
    (g inverseLink : ℝ → ℝ) (fit : SourceFactorParameter Item Model K) :
    sourceUnrestrictedNormalizationSpec hK g inverseLink fit := by
  intro hinverse
  have hrank := sourceBilinearMatrix_rank_le_dimension fit
  by_cases heq : finrank ℝ (matrixEuclideanOperatorEquiv (sourceBilinearMatrix fit)).toLinearMap.range = K
  · obtain ⟨z, hprod, hfull, hbal, hvalue, hmax⟩ := sourceHeterogeneity_maximum_exists
      hK (sourceBilinearMatrix fit) heq
    have hprob := (sourceBilinearPrediction_eq_iff_matrix_eq g hinverse.injective z fit).mpr hprod
    refine ⟨z, ⟨hprob, hbal⟩, ⟨Set.mem_univ _, hprob, ?_⟩, ?_⟩
    · intro w _hw hw
      exact hmax w ((sourceBilinearPrediction_eq_iff_matrix_eq g hinverse.injective w fit).mp hw)
    · unfold sourceIntrinsicBilinearHeterogeneity
      rw [← sourceBilinearMatrix_eq_inverseLink g inverseLink hinverse fit]
      exact hvalue
  · have hlt : finrank ℝ (matrixEuclideanOperatorEquiv (sourceBilinearMatrix fit)).toLinearMap.range < K :=
      lt_of_le_of_ne hrank heq
    let z := sourcePaddedBalancedFit (sourceBilinearMatrix fit) hrank
    have hprod : sourceBilinearMatrix z = sourceBilinearMatrix fit := sourcePaddedBalancedFit_product _ hrank
    have hprob := (sourceBilinearPrediction_eq_iff_matrix_eq g hinverse.injective z fit).mpr hprod
    have hzrank : finrank ℝ (matrixEuclideanOperatorEquiv (sourceBilinearMatrix z)).toLinearMap.range < K := by
      rwa [hprod]
    have hzvalue := sourceHeterogeneity_eq_zero_of_rank_lt hK z hzrank
    refine ⟨z, ⟨hprob, sourcePaddedBalancedFit_balanced _ hrank⟩,
      ⟨Set.mem_univ _, hprob, ?_⟩, ?_⟩
    · intro w _hw hw
      have hwprod := (sourceBilinearPrediction_eq_iff_matrix_eq g hinverse.injective w fit).mp hw
      have hwrank : finrank ℝ (matrixEuclideanOperatorEquiv (sourceBilinearMatrix w)).toLinearMap.range < K := by
        rwa [hwprod]
      rw [sourceHeterogeneity_eq_zero_of_rank_lt hK w hwrank, hzvalue]
    · unfold sourceIntrinsicBilinearHeterogeneity
      rw [← sourceBilinearMatrix_eq_inverseLink g inverseLink hinverse fit, hzvalue]
      exact ((matrixEuclideanOperatorEquiv (sourceBilinearMatrix fit)).toLinearMap.singularValues_eq_zero_iff_le_finrank_range.mpr (Nat.le_sub_one_of_lt hlt)).symm

/-- Positive source heterogeneity forces full column rank and hence rank equal to the latent dimension. -/
theorem sourcePositiveHeterogeneity_fullRank (hK : 0 < K)
    (fit : SourceFactorParameter Item Model K) (hh : 0 < sourceHeterogeneity hK fit) :
    FullRankOperatorFactors (sourceFactorOperatorEquiv fit) ∧
      finrank ℝ (matrixEuclideanOperatorEquiv (sourceBilinearMatrix fit)).toLinearMap.range = K := by
  obtain ⟨hU, hV⟩ := sourceHeterogeneity_lowerBounds hK fit
  have hfull := sourceFactorOperator_fullRank_of_gramLowerBounds fit hh hU hV
  exact ⟨hfull, sourceBilinearMatrix_rank_of_fullRank fit hfull⟩

/-- Canonical normalization preserves positivity and supplies the source Gram bounds used by stability. -/
theorem sourcePositiveHeterogeneity_normalization (hK : 0 < K)
    (g inverseLink : ℝ → ℝ) (hinverse : LeftInverse inverseLink g)
    (fit : SourceFactorParameter Item Model K) (hh : 0 < sourceHeterogeneity hK fit) :
    ∃ z : SourceFactorParameter Item Model K,
      sourceBalancedNormalizedFit g
        (sourcePrediction (fun uv => g ⟪uv.1, uv.2⟫) fit) z ∧
      sourceMaximumHeterogeneityFit hK (fun uv => g ⟪uv.1, uv.2⟫) Set.univ
        (sourcePrediction (fun uv => g ⟪uv.1, uv.2⟫) fit) z ∧
      sourceHeterogeneity hK z = sourceIntrinsicBilinearHeterogeneity hK inverseLink
        (sourcePrediction (fun uv => g ⟪uv.1, uv.2⟫) fit) ∧
      0 < sourceHeterogeneity hK z ∧
      FactorGramLowerBound (sourceHeterogeneity hK z) (fun i k => sourceItemFactor i z k) ∧
      FactorGramLowerBound (sourceHeterogeneity hK z) (fun j k => sourceModelFactor j z k) := by
  obtain ⟨z, hbal, hmax, hvalue⟩ := sourceUnrestrictedNormalization hK g inverseLink fit hinverse
  have hzpos : 0 < sourceHeterogeneity hK z :=
    hh.trans_le (hmax.2.2 fit (Set.mem_univ _) rfl)
  obtain ⟨hU, hV⟩ := sourceHeterogeneity_lowerBounds hK z
  exact ⟨z, hbal, hmax, hvalue, hzpos, hU, hV⟩

section OrthogonalUniqueness

variable {D E F G : Type*} [AddCommGroup D] [Module ℝ D]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]

/-- Two linear families with the same norms differ by one orthogonal transformation
of their common finite-dimensional ambient space. -/
theorem sourceLinearFamilies_equal_norm_rotation (L M : D →ₗ[ℝ] E)
    (hnorm : ∀ x, ‖L x‖ = ‖M x‖) :
    ∃ R : E ≃ₗᵢ[ℝ] E, ∀ x, R (L x) = M x := by
  have hker : L.ker ≤ M.ker := by
    intro x hx
    change M x = 0
    apply norm_eq_zero.mp
    rw [← hnorm x, LinearMap.mem_ker.mp hx, norm_zero]
  let H : L.range →ₗ[ℝ] E :=
    ((L.ker).liftQ M hker).comp L.quotKerEquivRange.symm.toLinearMap
  have hH : ∀ x, H ⟨L x, LinearMap.mem_range_self L x⟩ = M x := by
    intro x
    simp only [H, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  let I : L.range →ₗᵢ[ℝ] E :=
    { toLinearMap := H
      norm_map' := by
        rintro ⟨v, hv⟩
        obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hv
        rw [hH]
        exact (hnorm x).symm }
  let R : E ≃ₗᵢ[ℝ] E := LinearIsometryEquiv.ofSurjective I.extend
    (LinearMap.surjective_of_injective (f := I.extend.toLinearMap) I.extend.injective)
  refine ⟨R, ?_⟩
  intro x
  change I.extend (L x) = M x
  exact (I.extend_apply ⟨L x, LinearMap.mem_range_self L x⟩).trans (hH x)

/-- Balanced pairs of any rank representing the same operator differ by a common rotation. -/
theorem sourceBalancedFactors_anyRank_unique_up_to_rotation
    (U U' : E →ₗ[ℝ] F) (V V' : E →ₗ[ℝ] G)
    (hbal : U.adjoint ∘ₗ U = V.adjoint ∘ₗ V)
    (hbal' : U'.adjoint ∘ₗ U' = V'.adjoint ∘ₗ V')
    (hprod : U ∘ₗ V.adjoint = U' ∘ₗ V'.adjoint) :
    ∃ R : E ≃ₗᵢ[ℝ] E, (∀ x, U' (R x) = U x) ∧ (∀ x, V' (R x) = V x) := by
  have houterU := balanced_sameProduct_outerGram_eq U U' V V' hbal hbal' hprod
  have hprodAdj : V ∘ₗ U.adjoint = V' ∘ₗ U'.adjoint := by
    simpa only [LinearMap.adjoint_comp, LinearMap.adjoint_adjoint] using
      congrArg LinearMap.adjoint hprod
  have houterV := balanced_sameProduct_outerGram_eq V V' U U' hbal.symm hbal'.symm hprodAdj
  have hUU : ∀ f : F, ⟪U.adjoint f, U.adjoint f⟫ = ⟪U'.adjoint f, U'.adjoint f⟫ := by
    intro f
    rw [U.adjoint_inner_right, U'.adjoint_inner_right]
    exact congrArg (fun y : F => ⟪y, f⟫) (LinearMap.congr_fun houterU f)
  have hVV : ∀ g : G, ⟪V.adjoint g, V.adjoint g⟫ = ⟪V'.adjoint g, V'.adjoint g⟫ := by
    intro g
    rw [V.adjoint_inner_right, V'.adjoint_inner_right]
    exact congrArg (fun y : G => ⟪y, g⟫) (LinearMap.congr_fun houterV g)
  have hUV : ∀ f : F, ∀ g : G,
      ⟪U.adjoint f, V.adjoint g⟫ = ⟪U'.adjoint f, V'.adjoint g⟫ := by
    intro f g
    rw [U.adjoint_inner_left, U'.adjoint_inner_left]
    exact congrArg (fun y : F => ⟪f, y⟫) (LinearMap.congr_fun hprod g)
  have hnorm : ∀ x : F × G,
      ‖U.adjoint.coprod V.adjoint x‖ = ‖U'.adjoint.coprod V'.adjoint x‖ := by
    rintro ⟨f, g⟩
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    have hVU : ⟪V.adjoint g, U.adjoint f⟫ = ⟪V'.adjoint g, U'.adjoint f⟫ :=
      (real_inner_comm _ _).trans ((hUV f g).trans (real_inner_comm _ _))
    simp only [LinearMap.coprod_apply, inner_add_left, inner_add_right, hUU, hVV, hUV, hVU]

  obtain ⟨R, hR⟩ := sourceLinearFamilies_equal_norm_rotation
    (U.adjoint.coprod V.adjoint) (U'.adjoint.coprod V'.adjoint) hnorm
  have hRU : ∀ f : F, R (U.adjoint f) = U'.adjoint f := by
    intro f
    simpa only [LinearMap.coprod_apply, map_zero, add_zero] using hR (f, 0)
  have hRV : ∀ g : G, R (V.adjoint g) = V'.adjoint g := by
    intro g
    simpa only [LinearMap.coprod_apply, map_zero, zero_add] using hR (0, g)
  refine ⟨R, ?_, ?_⟩
  · intro x
    apply ext_inner_right ℝ
    intro f
    rw [← U'.adjoint_inner_right, ← hRU, R.inner_map_map, U.adjoint_inner_right]
  · intro x
    apply ext_inner_right ℝ
    intro g
    rw [← V'.adjoint_inner_right, ← hRV, R.inner_map_map, V.adjoint_inner_right]

end OrthogonalUniqueness

/-- The canonical balanced fit is an actual specified unrestricted fitted model. -/
theorem sourceBalancedNormalizedFit_specified (g : ℝ → ℝ)
    (probabilities : SourcePredictionArray Item Model) (fit : SourceFactorParameter Item Model K)
    (hfit : sourceBalancedNormalizedFit g probabilities fit) :
    sourceSpecifiedAdmissibleFit (fun uv => g ⟪uv.1, uv.2⟫) Set.univ probabilities fit :=
  ⟨Set.mem_univ _, hfit.1⟩

/-- An attained admissible maximum is, in particular, the specified fitted model. -/
theorem sourceMaximumHeterogeneityFit_specified (hK : 0 < K)
    (link : EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin K) → ℝ)
    (admissible : Set (SourceFactorParameter Item Model K))
    (probabilities : SourcePredictionArray Item Model) (fit : SourceFactorParameter Item Model K)
    (hfit : sourceMaximumHeterogeneityFit hK link admissible probabilities fit) :
    sourceSpecifiedAdmissibleFit link admissible probabilities fit := ⟨hfit.1, hfit.2.1⟩

/-- Any two attained admissible maxima have the same heterogeneity value. -/
theorem sourceMaximumHeterogeneityFit_value_unique (hK : 0 < K)
    (link : EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin K) → ℝ)
    (admissible : Set (SourceFactorParameter Item Model K))
    (probabilities : SourcePredictionArray Item Model) (z w : SourceFactorParameter Item Model K)
    (hz : sourceMaximumHeterogeneityFit hK link admissible probabilities z)
    (hw : sourceMaximumHeterogeneityFit hK link admissible probabilities w) :
    sourceHeterogeneity hK z = sourceHeterogeneity hK w :=
  le_antisymm (hw.2.2 z hz.1 hz.2.1) (hz.2.2 w hw.1 hw.2.1)

/-- In the exact probability fiber of an injective bilinear link, every balanced fit
is unique up to a common latent rotation, including rank-deficient fits. -/
theorem sourceBalancedNormalizedFit_unique_up_to_rotation (g : ℝ → ℝ) (hg : Injective g)
    (probabilities : SourcePredictionArray Item Model) (z w : SourceFactorParameter Item Model K)
    (hz : sourceBalancedNormalizedFit g probabilities z)
    (hw : sourceBalancedNormalizedFit g probabilities w) :
    ∃ R : EuclideanSpace ℝ (Fin K) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin K),
      (∀ x : EuclideanSpace ℝ (Fin K), ∀ i : Item,
        finiteDot (fun k => sourceItemFactor i w k) (fun k => R x k) =
          finiteDot (fun k => sourceItemFactor i z k) (fun k => x k)) ∧
      (∀ x : EuclideanSpace ℝ (Fin K), ∀ j : Model,
        finiteDot (fun k => sourceModelFactor j w k) (fun k => R x k) =
          finiteDot (fun k => sourceModelFactor j z k) (fun k => x k)) := by
  have hprod := (sourceBilinearPrediction_eq_iff_matrix_eq g hg z w).mp (hz.1.trans hw.1.symm)
  have hop : (sourceFactorOperatorEquiv z).1.toLinearMap ∘ₗ
      (sourceFactorOperatorEquiv z).2.toLinearMap.adjoint =
    (sourceFactorOperatorEquiv w).1.toLinearMap ∘ₗ
      (sourceFactorOperatorEquiv w).2.toLinearMap.adjoint := by
    rw [← sourceBilinearMatrix_operator, ← sourceBilinearMatrix_operator, hprod]
  obtain ⟨R, hU, hV⟩ := sourceBalancedFactors_anyRank_unique_up_to_rotation
    (sourceFactorOperatorEquiv z).1.toLinearMap (sourceFactorOperatorEquiv w).1.toLinearMap
    (sourceFactorOperatorEquiv z).2.toLinearMap (sourceFactorOperatorEquiv w).2.toLinearMap
    ((sourceFactorGramMatrix_eq_iff_operator_balance z).mp hz.2)
    ((sourceFactorGramMatrix_eq_iff_operator_balance w).mp hw.2) hop
  refine ⟨R, ?_, ?_⟩
  · intro x i
    exact congrArg (fun y : EuclideanSpace ℝ Item => y i) (hU x)
  · intro x j
    exact congrArg (fun y : EuclideanSpace ℝ Model => y j) (hV x)

/-- Common orthogonal changes of latent coordinates preserve every factor Gram lower bound. -/
theorem sourceFactorGramLowerBound_rotation_iff {A : Type*} [Fintype A]
    (U V : Matrix A (Fin K) ℝ)
    (R : EuclideanSpace ℝ (Fin K) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin K))
    (hrot : ∀ x, matrixEuclideanOperatorEquiv V (R x) = matrixEuclideanOperatorEquiv U x)
    (h : ℝ) : FactorGramLowerBound h U ↔ FactorGramLowerBound h V := by
  rw [sourceFactorGramLowerBound_iff_operator, sourceFactorGramLowerBound_iff_operator]
  constructor
  · intro hU y
    have hb := hU (R.symm y)
    have heq := hrot (R.symm y)
    rw [R.apply_symm_apply] at heq
    rw [← heq] at hb
    simpa only [R.symm.norm_map] using hb
  · intro hV x
    have hb := hV (R x)
    rw [hrot] at hb
    simpa only [R.norm_map] using hb

/-- One common latent rotation preserves the actual minimum-eigenvalue heterogeneity. -/
theorem sourceHeterogeneity_eq_of_common_rotation (hK : 0 < K)
    (z w : SourceFactorParameter Item Model K)
    (R : EuclideanSpace ℝ (Fin K) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin K))
    (hU : ∀ x : EuclideanSpace ℝ (Fin K), ∀ i : Item,
      finiteDot (fun k => sourceItemFactor i w k) (fun k => R x k) =
        finiteDot (fun k => sourceItemFactor i z k) (fun k => x k))
    (hV : ∀ x : EuclideanSpace ℝ (Fin K), ∀ j : Model,
      finiteDot (fun k => sourceModelFactor j w k) (fun k => R x k) =
        finiteDot (fun k => sourceModelFactor j z k) (fun k => x k)) :
    sourceHeterogeneity hK z = sourceHeterogeneity hK w := by
  have hUop : ∀ x, matrixEuclideanOperatorEquiv (Matrix.of (fun i k => sourceItemFactor i w k)) (R x) =
      matrixEuclideanOperatorEquiv (Matrix.of (fun i k => sourceItemFactor i z k)) x := by
    intro x
    apply PiLp.ext
    intro i
    exact hU x i
  have hVop : ∀ x, matrixEuclideanOperatorEquiv (Matrix.of (fun j k => sourceModelFactor j w k)) (R x) =
      matrixEuclideanOperatorEquiv (Matrix.of (fun j k => sourceModelFactor j z k)) x := by
    intro x
    apply PiLp.ext
    intro j
    exact hV x j
  have hiff : ∀ h : ℝ, h ≤ sourceHeterogeneity hK z ↔ h ≤ sourceHeterogeneity hK w := by
    intro h
    rw [sourceHeterogeneity_lowerBound_iff, sourceHeterogeneity_lowerBound_iff]
    exact and_congr (sourceFactorGramLowerBound_rotation_iff _ _ R hUop h)
      (sourceFactorGramLowerBound_rotation_iff _ _ R hVop h)
  exact le_antisymm ((hiff _).mp le_rfl) ((hiff _).mpr le_rfl)

/-- Every exact balanced fit implements the canonical maximizing convention and intrinsic value. -/
theorem sourceBalancedNormalizedFit_maximum_and_value (hK : 0 < K)
    (g inverseLink : ℝ → ℝ) (hinverse : LeftInverse inverseLink g)
    (fit z : SourceFactorParameter Item Model K)
    (hz : sourceBalancedNormalizedFit g
      (sourcePrediction (fun uv => g ⟪uv.1, uv.2⟫) fit) z) :
    sourceMaximumHeterogeneityFit hK (fun uv => g ⟪uv.1, uv.2⟫) Set.univ
      (sourcePrediction (fun uv => g ⟪uv.1, uv.2⟫) fit) z ∧
    sourceHeterogeneity hK z = sourceIntrinsicBilinearHeterogeneity hK inverseLink
      (sourcePrediction (fun uv => g ⟪uv.1, uv.2⟫) fit) := by
  obtain ⟨w, hw, hmax, hvalue⟩ := sourceUnrestrictedNormalization hK g inverseLink fit hinverse
  obtain ⟨R, hU, hV⟩ := sourceBalancedNormalizedFit_unique_up_to_rotation
    g hinverse.injective _ z w hz hw
  have heq := sourceHeterogeneity_eq_of_common_rotation hK z w R hU hV
  refine ⟨⟨Set.mem_univ _, hz.1, ?_⟩, heq.trans hvalue⟩
  intro v hv hvprob
  rw [heq]
  exact hmax.2.2 v hv hvprob

/-- The unrestricted normalization claim, including attainment, intrinsic value and
balanced-class rotation uniqueness, holds in the exact fitted probability fiber at every rank. -/
def sourceAdoptedNormalizationSpec (hK : 0 < K)
    (g inverseLink : ℝ → ℝ) (fit : SourceFactorParameter Item Model K) : Prop :=
  LeftInverse inverseLink g →
    (∃ z : SourceFactorParameter Item Model K,
      sourceBalancedNormalizedFit g (sourcePrediction (fun uv => g ⟪uv.1, uv.2⟫) fit) z) ∧
    (∀ z : SourceFactorParameter Item Model K,
      sourceBalancedNormalizedFit g (sourcePrediction (fun uv => g ⟪uv.1, uv.2⟫) fit) z →
      sourceSpecifiedAdmissibleFit (fun uv => g ⟪uv.1, uv.2⟫) Set.univ
        (sourcePrediction (fun uv => g ⟪uv.1, uv.2⟫) fit) z ∧
      sourceMaximumHeterogeneityFit hK (fun uv => g ⟪uv.1, uv.2⟫) Set.univ
        (sourcePrediction (fun uv => g ⟪uv.1, uv.2⟫) fit) z ∧
      sourceHeterogeneity hK z = sourceIntrinsicBilinearHeterogeneity hK inverseLink
        (sourcePrediction (fun uv => g ⟪uv.1, uv.2⟫) fit)) ∧
    (∀ z w : SourceFactorParameter Item Model K,
      sourceBalancedNormalizedFit g (sourcePrediction (fun uv => g ⟪uv.1, uv.2⟫) fit) z →
      sourceBalancedNormalizedFit g (sourcePrediction (fun uv => g ⟪uv.1, uv.2⟫) fit) w →
      ∃ R : EuclideanSpace ℝ (Fin K) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin K),
        (∀ x : EuclideanSpace ℝ (Fin K), ∀ i : Item,
          finiteDot (fun k => sourceItemFactor i w k) (fun k => R x k) =
            finiteDot (fun k => sourceItemFactor i z k) (fun k => x k)) ∧
        (∀ x : EuclideanSpace ℝ (Fin K), ∀ j : Model,
          finiteDot (fun k => sourceModelFactor j w k) (fun k => R x k) =
            finiteDot (fun k => sourceModelFactor j z k) (fun k => x k)))

theorem sourceAdoptedNormalization (hK : 0 < K)
    (g inverseLink : ℝ → ℝ) (fit : SourceFactorParameter Item Model K) :
    sourceAdoptedNormalizationSpec hK g inverseLink fit := by
  intro hinverse
  refine ⟨sourceBalancedNormalizedFit_exists g fit, ?_, ?_⟩
  · intro z hz
    obtain ⟨hmax, hvalue⟩ := sourceBalancedNormalizedFit_maximum_and_value
      hK g inverseLink hinverse fit z hz
    exact ⟨sourceBalancedNormalizedFit_specified g _ z hz, hmax, hvalue⟩
  · intro z w hz hw
    exact sourceBalancedNormalizedFit_unique_up_to_rotation g hinverse.injective _ z w hz hw

end
end JGR26SubjectivityMonoculture
