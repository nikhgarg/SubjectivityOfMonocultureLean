import JGR26SubjectivityMonoculture.BalancedFactors
import JGR26SubjectivityMonoculture.MIRTIdentification
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Balanced representations in the source's finite factor coordinates

The source covariance matrix is the actual matrix `Uᵀ U`. Its operator is the
factor's adjoint Gram, and its least eigenvalue is equivalently the largest
Rayleigh lower bound used by `FactorGramLowerBound`. All factor coordinates
are free real parameters. The balanced construction realizes each fitted
bilinear matrix of positive rank in its rank-dimensional latent space.
-/

namespace JGR26SubjectivityMonoculture

open Module Function
open scoped BigOperators RealInnerProductSpace

noncomputable section

variable {K : ℕ} {Item Model A B C : Type*}
  [Fintype Item] [Fintype Model]

/-- The source covariance matrix, the sum of the factor row outer products. -/
def sourceFactorGramMatrix [Fintype A] (U : Matrix A (Fin K) ℝ) :
    Matrix (Fin K) (Fin K) ℝ := U.transpose * U

@[simp] theorem sourceFactorGramMatrix_apply [Fintype A]
    (U : Matrix A (Fin K) ℝ) (k l : Fin K) :
    sourceFactorGramMatrix U k l = ∑ a, U a k * U a l := rfl

/-- Source real Gram matrices are Hermitian. -/
theorem sourceFactorGramMatrix_isHermitian [Fintype A]
    (U : Matrix A (Fin K) ℝ) : (sourceFactorGramMatrix U).IsHermitian := by
  simpa [sourceFactorGramMatrix] using Matrix.isHermitian_conjTranspose_mul_self U

/-- Matrix multiplication is composition in the finite Euclidean coordinates. -/
theorem matrixEuclideanOperatorEquiv_mul [Fintype A] [Fintype B] [Fintype C]
    (U : Matrix A B ℝ) (V : Matrix B C ℝ) :
    (matrixEuclideanOperatorEquiv (U * V)).toLinearMap =
      (matrixEuclideanOperatorEquiv U).toLinearMap ∘ₗ
        (matrixEuclideanOperatorEquiv V).toLinearMap := by
  classical
  exact Matrix.toLpLin_mul 2 2 2 U V

/-- Equality of Euclidean operators determines every entry of a finite matrix. -/
theorem matrix_eq_of_euclideanOperator_eq [Fintype A] [Fintype B]
    {M N : Matrix A B ℝ}
    (h : (matrixEuclideanOperatorEquiv M).toLinearMap =
      (matrixEuclideanOperatorEquiv N).toLinearMap) : M = N := by
  apply matrixEuclideanOperatorEquiv.injective
  apply ContinuousLinearMap.ext
  intro x
  exact LinearMap.congr_fun h x

/-- The source transpose is the Euclidean adjoint of the factor operator. -/
theorem matrixEuclideanOperatorEquiv_transpose [Fintype A] [Fintype B]
    (U : Matrix A B ℝ) :
    (matrixEuclideanOperatorEquiv U.transpose).toLinearMap =
      (matrixEuclideanOperatorEquiv U).toLinearMap.adjoint := by
  classical
  simpa using Matrix.toEuclideanLin_conjTranspose_eq_adjoint U

/-- The source covariance matrix and actual factor-adjoint Gram are the same operator. -/
theorem sourceFactorGramMatrix_operator [Fintype A] (U : Matrix A (Fin K) ℝ) :
    (matrixEuclideanOperatorEquiv (sourceFactorGramMatrix U)).toLinearMap =
      (matrixEuclideanOperatorEquiv U).toLinearMap.adjoint ∘ₗ
        (matrixEuclideanOperatorEquiv U).toLinearMap := by
  rw [sourceFactorGramMatrix, matrixEuclideanOperatorEquiv_mul,
    matrixEuclideanOperatorEquiv_transpose]

/-- Finite-coordinate Gram bounds are exactly the factor operator's norm bounds. -/
theorem sourceFactorGramLowerBound_iff_operator [Fintype A]
    (U : Matrix A (Fin K) ℝ) (h : ℝ) :
    FactorGramLowerBound h U ↔
      ∀ x : EuclideanSpace ℝ (Fin K),
        h * ‖x‖ ^ 2 ≤ ‖matrixEuclideanOperatorEquiv U x‖ ^ 2 := by
  constructor
  · intro hU x
    simpa only [finiteSqNorm, EuclideanSpace.real_norm_sq_eq, finiteDot,
      matrixEuclideanOperatorEquiv_apply] using hU (fun k => x k)
  · intro hU x
    simpa only [finiteSqNorm, EuclideanSpace.real_norm_sq_eq, finiteDot,
      matrixEuclideanOperatorEquiv_apply] using hU (WithLp.toLp 2 x)

/-- The least eigenvalue of the actual source covariance matrix. -/
def sourceFactorLeastGramEigenvalue {n : ℕ} [Fintype A]
    (U : Matrix A (Fin (n + 1)) ℝ) : ℝ := by
  classical
  exact (Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (sourceFactorGramMatrix_isHermitian U)).eigenvalues
      finrank_euclideanSpace_fin (Fin.last n)

/-- Equal symmetric operators have the same ordered eigenvalues. -/
theorem symmetricOperator_eigenvalues_congr
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {L M : E →ₗ[ℝ] E} (hL : L.IsSymmetric) (hM : M.IsSymmetric)
    (h : L = M) {n : ℕ} (hn : finrank ℝ E = n) (i : Fin n) :
    hL.eigenvalues hn i = hM.eigenvalues hn i := by
  subst M
  rfl

/-- The actual source-matrix eigenvalue agrees with the factor-adjoint eigenvalue. -/
theorem sourceFactorLeastGramEigenvalue_eq_operator {n : ℕ} [Fintype A]
    (U : Matrix A (Fin (n + 1)) ℝ) :
    sourceFactorLeastGramEigenvalue U =
      (matrixEuclideanOperatorEquiv U).toLinearMap.isSymmetric_adjoint_comp_self.eigenvalues
        finrank_euclideanSpace_fin (Fin.last n) := by
  classical
  have heq : (sourceFactorGramMatrix U).toEuclideanLin =
      (matrixEuclideanOperatorEquiv U).toLinearMap.adjoint ∘ₗ
        (matrixEuclideanOperatorEquiv U).toLinearMap := sourceFactorGramMatrix_operator U
  unfold sourceFactorLeastGramEigenvalue
  exact symmetricOperator_eigenvalues_congr _ _ heq finrank_euclideanSpace_fin (Fin.last n)

/-- The source's Gram condition is precisely a lower bound on its smallest eigenvalue. -/
theorem sourceFactorGramLowerBound_iff_le_leastEigenvalue {n : ℕ} [Fintype A]
    (U : Matrix A (Fin (n + 1)) ℝ) (h : ℝ) :
    FactorGramLowerBound h U ↔ h ≤ sourceFactorLeastGramEigenvalue U := by
  rw [sourceFactorGramLowerBound_iff_operator, sourceFactorLeastGramEigenvalue_eq_operator]
  exact gram_lowerBound_iff_le_smallestEigenvalue
    (matrixEuclideanOperatorEquiv U).toLinearMap finrank_euclideanSpace_fin h

/-- The least source Gram eigenvalue in any positive latent dimension. -/
def sourceFactorSmallestGramEigenvalue [Fintype A]
    (U : Matrix A (Fin K) ℝ) (hK : 0 < K) : ℝ := by
  classical
  exact (Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (sourceFactorGramMatrix_isHermitian U)).eigenvalues
      finrank_euclideanSpace_fin ⟨K - 1, Nat.sub_one_lt_of_lt hK⟩

/-- Ordered source Gram eigenvalues are those of the actual adjoint-composition Gram. -/
theorem sourceFactorSmallestGramEigenvalue_eq_operator [Fintype A]
    (U : Matrix A (Fin K) ℝ) (hK : 0 < K) :
    sourceFactorSmallestGramEigenvalue U hK =
      (matrixEuclideanOperatorEquiv U).toLinearMap.isSymmetric_adjoint_comp_self.eigenvalues
        finrank_euclideanSpace_fin ⟨K - 1, Nat.sub_one_lt_of_lt hK⟩ := by
  classical
  unfold sourceFactorSmallestGramEigenvalue
  exact symmetricOperator_eigenvalues_congr _ _
    (sourceFactorGramMatrix_operator U) finrank_euclideanSpace_fin _

/-- Source coordinate Gram bounds are exactly the actual smallest-eigenvalue bounds. -/
theorem sourceFactorGramLowerBound_iff_le_smallestEigenvalue [Fintype A]
    (U : Matrix A (Fin K) ℝ) (hK : 0 < K) (h : ℝ) :
    FactorGramLowerBound h U ↔ h ≤ sourceFactorSmallestGramEigenvalue U hK := by
  cases K with
  | zero => omega
  | succ n =>
    have heq : sourceFactorSmallestGramEigenvalue U hK =
        sourceFactorLeastGramEigenvalue U := by
      unfold sourceFactorSmallestGramEigenvalue sourceFactorLeastGramEigenvalue
      congr 1
    rw [heq]
    exact sourceFactorGramLowerBound_iff_le_leastEigenvalue U h

/-- The heterogeneity of a source factor fit, using its two actual Gram matrices. -/
def sourceHeterogeneity (hK : 0 < K) (z : SourceFactorParameter Item Model K) : ℝ :=
  min (sourceFactorSmallestGramEigenvalue (Matrix.of (fun i k => sourceItemFactor i z k)) hK)
    (sourceFactorSmallestGramEigenvalue (Matrix.of (fun j k => sourceModelFactor j z k)) hK)

/-- A scalar Rayleigh bound holds for both source factors exactly when it is at most `h`. -/
theorem sourceHeterogeneity_lowerBound_iff (hK : 0 < K)
    (z : SourceFactorParameter Item Model K) (h : ℝ) :
    h ≤ sourceHeterogeneity hK z ↔
      FactorGramLowerBound h (fun i k => sourceItemFactor i z k) ∧
      FactorGramLowerBound h (fun j k => sourceModelFactor j z k) := by
  unfold sourceHeterogeneity
  rw [le_min_iff, ← sourceFactorGramLowerBound_iff_le_smallestEigenvalue,
    ← sourceFactorGramLowerBound_iff_le_smallestEigenvalue]
  rfl

/-- The actual source heterogeneity supplies both Gram bounds without additional premises. -/
theorem sourceHeterogeneity_lowerBounds (hK : 0 < K)
    (z : SourceFactorParameter Item Model K) :
    FactorGramLowerBound (sourceHeterogeneity hK z) (fun i k => sourceItemFactor i z k) ∧
      FactorGramLowerBound (sourceHeterogeneity hK z) (fun j k => sourceModelFactor j z k) :=
  (sourceHeterogeneity_lowerBound_iff hK z _).mp le_rfl

/-- The source inverse-link matrix for a free bilinear representation. -/
def sourceBilinearMatrix (z : SourceFactorParameter Item Model K) : Matrix Item Model ℝ :=
  Matrix.of (fun i k => sourceItemFactor i z k) *
    (Matrix.of (fun j k => sourceModelFactor j z k)).transpose

omit [Fintype Item] [Fintype Model] in
@[simp] theorem sourceBilinearMatrix_apply
    (z : SourceFactorParameter Item Model K) (i : Item) (j : Model) :
    sourceBilinearMatrix z i j = finiteDot
      (fun k => sourceItemFactor i z k) (fun k => sourceModelFactor j z k) := rfl

/-- Source bilinear cells and the factor-adjoint product give the same operator. -/
theorem sourceBilinearMatrix_operator (z : SourceFactorParameter Item Model K) :
    (matrixEuclideanOperatorEquiv (sourceBilinearMatrix z)).toLinearMap =
      (sourceFactorOperatorEquiv z).1.toLinearMap ∘ₗ
        (sourceFactorOperatorEquiv z).2.toLinearMap.adjoint := by
  rw [sourceBilinearMatrix, matrixEuclideanOperatorEquiv_mul,
    matrixEuclideanOperatorEquiv_transpose]
  rfl

/-- The actual finite arrays obtained from the spectral balanced factors. -/
def balancedSourceFactorParameter (Θ : Matrix Item Model ℝ) :
    SourceFactorParameter Item Model
      (finrank ℝ (matrixEuclideanOperatorEquiv Θ).toLinearMap.range) :=
  sourceFactorOperatorEquiv.symm
    ((balancedLeftFactor (matrixEuclideanOperatorEquiv Θ).toLinearMap).toContinuousLinearMap,
      (balancedRightFactor (matrixEuclideanOperatorEquiv Θ).toLinearMap).toContinuousLinearMap)

@[simp] theorem balancedSourceFactorParameter_left_operator (Θ : Matrix Item Model ℝ) :
    (sourceFactorOperatorEquiv (balancedSourceFactorParameter Θ)).1.toLinearMap =
      balancedLeftFactor (matrixEuclideanOperatorEquiv Θ).toLinearMap := by
  simp only [balancedSourceFactorParameter, ContinuousLinearEquiv.apply_symm_apply]
  rfl

@[simp] theorem balancedSourceFactorParameter_right_operator (Θ : Matrix Item Model ℝ) :
    (sourceFactorOperatorEquiv (balancedSourceFactorParameter Θ)).2.toLinearMap =
      balancedRightFactor (matrixEuclideanOperatorEquiv Θ).toLinearMap := by
  simp only [balancedSourceFactorParameter, ContinuousLinearEquiv.apply_symm_apply]
  rfl

/-- The source arrays reconstruct the fitted bilinear matrix in every cell. -/
theorem balancedSourceFactorParameter_product (Θ : Matrix Item Model ℝ) :
    sourceBilinearMatrix (balancedSourceFactorParameter Θ) = Θ := by
  apply matrix_eq_of_euclideanOperator_eq
  exact (sourceBilinearMatrix_operator (balancedSourceFactorParameter Θ)).trans
    ((congrArg₂ (fun
      (U : EuclideanSpace ℝ (Fin (finrank ℝ (matrixEuclideanOperatorEquiv Θ).toLinearMap.range)) →ₗ[ℝ]
        EuclideanSpace ℝ Item)
      (V : EuclideanSpace ℝ (Fin (finrank ℝ (matrixEuclideanOperatorEquiv Θ).toLinearMap.range)) →ₗ[ℝ]
        EuclideanSpace ℝ Model) => U ∘ₗ V.adjoint)
      (balancedSourceFactorParameter_left_operator Θ)
      (balancedSourceFactorParameter_right_operator Θ)).trans
      (balancedFactors_product_eq (matrixEuclideanOperatorEquiv Θ).toLinearMap))

/-- The source arrays have equal actual covariance matrices. -/
theorem balancedSourceFactorParameter_gram (Θ : Matrix Item Model ℝ) :
    sourceFactorGramMatrix (fun i k => sourceItemFactor i (balancedSourceFactorParameter Θ) k) =
      sourceFactorGramMatrix (fun j k => sourceModelFactor j (balancedSourceFactorParameter Θ) k) := by
  apply matrix_eq_of_euclideanOperator_eq
  have hU := congrArg (fun U => U.adjoint ∘ₗ U)
    (balancedSourceFactorParameter_left_operator Θ)
  have hV := congrArg (fun V => V.adjoint ∘ₗ V)
    (balancedSourceFactorParameter_right_operator Θ)
  exact (sourceFactorGramMatrix_operator
    (Matrix.of (fun i k => sourceItemFactor i (balancedSourceFactorParameter Θ) k))).trans
      (hU.trans ((balancedFactors_gram_eq (matrixEuclideanOperatorEquiv Θ).toLinearMap).trans
        (hV.symm.trans (sourceFactorGramMatrix_operator
          (Matrix.of (fun j k => sourceModelFactor j (balancedSourceFactorParameter Θ) k))).symm)))

/-- Positive fitted rank gives genuine full-column-rank source factors. -/
theorem balancedSourceFactorParameter_fullRank (Θ : Matrix Item Model ℝ)
    (hΘ : 0 < finrank ℝ (matrixEuclideanOperatorEquiv Θ).toLinearMap.range) :
    FullRankOperatorFactors (sourceFactorOperatorEquiv (balancedSourceFactorParameter Θ)) := by
  obtain ⟨hU, hV⟩ := balancedFactors_injective (matrixEuclideanOperatorEquiv Θ).toLinearMap hΘ
  constructor
  · change Injective (sourceFactorOperatorEquiv (balancedSourceFactorParameter Θ)).1.toLinearMap
    rwa [balancedSourceFactorParameter_left_operator]
  · change Injective (sourceFactorOperatorEquiv (balancedSourceFactorParameter Θ)).2.toLinearMap
    rwa [balancedSourceFactorParameter_right_operator]

/-- Both source Gram matrices attain the last positive singular-value lower bound. -/
theorem balancedSourceFactorParameter_gramLowerBounds (Θ : Matrix Item Model ℝ) :
    FactorGramLowerBound
      ((matrixEuclideanOperatorEquiv Θ).toLinearMap.singularValues
        (finrank ℝ (matrixEuclideanOperatorEquiv Θ).toLinearMap.range - 1))
      (fun i k => sourceItemFactor i (balancedSourceFactorParameter Θ) k) ∧
    FactorGramLowerBound
      ((matrixEuclideanOperatorEquiv Θ).toLinearMap.singularValues
        (finrank ℝ (matrixEuclideanOperatorEquiv Θ).toLinearMap.range - 1))
      (fun j k => sourceModelFactor j (balancedSourceFactorParameter Θ) k) := by
  rw [sourceFactorGramLowerBound_iff_operator, sourceFactorGramLowerBound_iff_operator]
  constructor
  · intro x
    change _ ≤ ‖(sourceFactorOperatorEquiv (balancedSourceFactorParameter Θ)).1.toLinearMap x‖ ^ 2
    rw [balancedSourceFactorParameter_left_operator]
    exact (balancedFactors_common_gram_lowerBound (matrixEuclideanOperatorEquiv Θ).toLinearMap x).1
  · intro x
    change _ ≤ ‖(sourceFactorOperatorEquiv (balancedSourceFactorParameter Θ)).2.toLinearMap x‖ ^ 2
    rw [balancedSourceFactorParameter_right_operator]
    exact (balancedFactors_common_gram_lowerBound (matrixEuclideanOperatorEquiv Θ).toLinearMap x).2

/-- Every exact source factorization has common Gram strength at most `σ_K(Θ)`. -/
theorem sourceFactorization_gramLowerBound_le_singularValue
    (Θ : Matrix Item Model ℝ) (z : SourceFactorParameter Item Model K)
    (hΘ : 0 < finrank ℝ (matrixEuclideanOperatorEquiv Θ).toLinearMap.range)
    (hprod : sourceBilinearMatrix z = Θ) (h : ℝ)
    (hU : FactorGramLowerBound h (fun i k => sourceItemFactor i z k))
    (hV : FactorGramLowerBound h (fun j k => sourceModelFactor j z k)) :
    h ≤ (matrixEuclideanOperatorEquiv Θ).toLinearMap.singularValues
      (finrank ℝ (matrixEuclideanOperatorEquiv Θ).toLinearMap.range - 1) := by
  have hop : (sourceFactorOperatorEquiv z).1.toLinearMap ∘ₗ
      (sourceFactorOperatorEquiv z).2.toLinearMap.adjoint =
      (matrixEuclideanOperatorEquiv Θ).toLinearMap := by
    rw [← sourceBilinearMatrix_operator, hprod]
  have hk : finrank ℝ (matrixEuclideanOperatorEquiv Θ).toLinearMap.range - 1 <
      finrank ℝ ((sourceFactorOperatorEquiv z).1.toLinearMap ∘ₗ
        (sourceFactorOperatorEquiv z).2.toLinearMap.adjoint).range := by
    rw [hop]
    exact Nat.sub_one_lt_of_lt hΘ
  have hb := common_gram_lowerBound_le_singularValue
    (sourceFactorOperatorEquiv z).1.toLinearMap (sourceFactorOperatorEquiv z).2.toLinearMap
    ((sourceFactorGramLowerBound_iff_operator _ h).mp hU)
    ((sourceFactorGramLowerBound_iff_operator _ h).mp hV) hk
  simpa only [hop] using hb

/-- For any positive rank `K`, actual `K`-coordinate source arrays attain the maximum. -/
theorem sourceBalancedRepresentation_exists (Θ : Matrix Item Model ℝ)
    (hK : 0 < K) (hrank : finrank ℝ (matrixEuclideanOperatorEquiv Θ).toLinearMap.range = K) :
    ∃ z : SourceFactorParameter Item Model K,
      sourceBilinearMatrix z = Θ ∧
      FullRankOperatorFactors (sourceFactorOperatorEquiv z) ∧
      sourceFactorGramMatrix (fun i k => sourceItemFactor i z k) =
        sourceFactorGramMatrix (fun j k => sourceModelFactor j z k) ∧
      FactorGramLowerBound ((matrixEuclideanOperatorEquiv Θ).toLinearMap.singularValues (K - 1))
        (fun i k => sourceItemFactor i z k) ∧
      FactorGramLowerBound ((matrixEuclideanOperatorEquiv Θ).toLinearMap.singularValues (K - 1))
        (fun j k => sourceModelFactor j z k) := by
  subst K
  exact ⟨balancedSourceFactorParameter Θ, balancedSourceFactorParameter_product Θ,
    balancedSourceFactorParameter_fullRank Θ hK, balancedSourceFactorParameter_gram Θ,
    (balancedSourceFactorParameter_gramLowerBounds Θ).1,
    (balancedSourceFactorParameter_gramLowerBounds Θ).2⟩

/-- The source finite-array heterogeneity cannot exceed the fitted matrix's last positive singular value. -/
theorem sourceHeterogeneity_le_singularValue (hK : 0 < K)
    (Θ : Matrix Item Model ℝ) (z : SourceFactorParameter Item Model K)
    (hrank : finrank ℝ (matrixEuclideanOperatorEquiv Θ).toLinearMap.range = K)
    (hprod : sourceBilinearMatrix z = Θ) :
    sourceHeterogeneity hK z ≤ (matrixEuclideanOperatorEquiv Θ).toLinearMap.singularValues (K - 1) := by
  obtain ⟨hU, hV⟩ := sourceHeterogeneity_lowerBounds hK z
  have hp : 0 < finrank ℝ (matrixEuclideanOperatorEquiv Θ).toLinearMap.range := by
    rwa [hrank]
  simpa only [hrank] using sourceFactorization_gramLowerBound_le_singularValue
    Θ z hp hprod (sourceHeterogeneity hK z) hU hV

/-- Actual finite factor arrays attain the maximum of the source minimum-Gram eigenvalue objective. -/
theorem sourceHeterogeneity_maximum_exists (hK : 0 < K)
    (Θ : Matrix Item Model ℝ)
    (hrank : finrank ℝ (matrixEuclideanOperatorEquiv Θ).toLinearMap.range = K) :
    ∃ z : SourceFactorParameter Item Model K,
      sourceBilinearMatrix z = Θ ∧
      FullRankOperatorFactors (sourceFactorOperatorEquiv z) ∧
      sourceFactorGramMatrix (fun i k => sourceItemFactor i z k) =
        sourceFactorGramMatrix (fun j k => sourceModelFactor j z k) ∧
      sourceHeterogeneity hK z = (matrixEuclideanOperatorEquiv Θ).toLinearMap.singularValues (K - 1) ∧
      ∀ w : SourceFactorParameter Item Model K, sourceBilinearMatrix w = Θ →
        sourceHeterogeneity hK w ≤ sourceHeterogeneity hK z := by
  obtain ⟨z, hprod, hfull, hbal, hU, hV⟩ := sourceBalancedRepresentation_exists Θ hK hrank
  have hlo := (sourceHeterogeneity_lowerBound_iff hK z _).mpr ⟨hU, hV⟩
  have hhi := sourceHeterogeneity_le_singularValue hK Θ z hrank hprod
  have heq := le_antisymm hhi hlo
  refine ⟨z, hprod, hfull, hbal, heq, ?_⟩
  intro w hw
  rw [heq]
  exact sourceHeterogeneity_le_singularValue hK Θ w hrank hw

/-- Equality of the source covariance matrices is precisely balance of the factor operators. -/
theorem sourceFactorGramMatrix_eq_iff_operator_balance
    (z : SourceFactorParameter Item Model K) :
    sourceFactorGramMatrix (fun i k => sourceItemFactor i z k) =
      sourceFactorGramMatrix (fun j k => sourceModelFactor j z k) ↔
    (sourceFactorOperatorEquiv z).1.toLinearMap.adjoint ∘ₗ
      (sourceFactorOperatorEquiv z).1.toLinearMap =
    (sourceFactorOperatorEquiv z).2.toLinearMap.adjoint ∘ₗ
      (sourceFactorOperatorEquiv z).2.toLinearMap := by
  constructor
  · intro h
    have hop := congrArg (fun M => (matrixEuclideanOperatorEquiv M).toLinearMap) h
    simpa only [sourceFactorGramMatrix_operator] using hop
  · intro h
    apply matrix_eq_of_euclideanOperator_eq
    simpa only [sourceFactorGramMatrix_operator] using h

/-- Balanced full-column-rank source fits of the same matrix have one common latent rotation. -/
theorem sourceBalancedRepresentations_unique_up_to_rotation
    (z w : SourceFactorParameter Item Model K)
    (hz : FullRankOperatorFactors (sourceFactorOperatorEquiv z))
    (hw : FullRankOperatorFactors (sourceFactorOperatorEquiv w))
    (hzbal : sourceFactorGramMatrix (fun i k => sourceItemFactor i z k) =
      sourceFactorGramMatrix (fun j k => sourceModelFactor j z k))
    (hwbal : sourceFactorGramMatrix (fun i k => sourceItemFactor i w k) =
      sourceFactorGramMatrix (fun j k => sourceModelFactor j w k))
    (hprod : sourceBilinearMatrix z = sourceBilinearMatrix w) :
    ∃ R : EuclideanSpace ℝ (Fin K) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin K),
      (∀ x : EuclideanSpace ℝ (Fin K), ∀ i : Item,
        finiteDot (fun k => sourceItemFactor i w k) (fun k => R x k) =
          finiteDot (fun k => sourceItemFactor i z k) (fun k => x k)) ∧
      (∀ x : EuclideanSpace ℝ (Fin K), ∀ j : Model,
        finiteDot (fun k => sourceModelFactor j w k) (fun k => R x k) =
          finiteDot (fun k => sourceModelFactor j z k) (fun k => x k)) := by
  have hop : (sourceFactorOperatorEquiv z).1.toLinearMap ∘ₗ
      (sourceFactorOperatorEquiv z).2.toLinearMap.adjoint =
    (sourceFactorOperatorEquiv w).1.toLinearMap ∘ₗ
      (sourceFactorOperatorEquiv w).2.toLinearMap.adjoint := by
    rw [← sourceBilinearMatrix_operator, ← sourceBilinearMatrix_operator, hprod]
  obtain ⟨R, hU, hV⟩ := balancedFactors_unique_up_to_rotation
    (sourceFactorOperatorEquiv z).1.toLinearMap (sourceFactorOperatorEquiv w).1.toLinearMap
    (sourceFactorOperatorEquiv z).2.toLinearMap (sourceFactorOperatorEquiv w).2.toLinearMap
    hz.1 hw.1 hz.2 hw.2
    ((sourceFactorGramMatrix_eq_iff_operator_balance z).mp hzbal)
    ((sourceFactorGramMatrix_eq_iff_operator_balance w).mp hwbal) hop
  refine ⟨R, ?_, ?_⟩
  · intro x i
    exact congrArg (fun y : EuclideanSpace ℝ Item => y i) (hU x)
  · intro x j
    exact congrArg (fun y : EuclideanSpace ℝ Model => y j) (hV x)

/-- Source fitted probabilities are the link applied to the bilinear matrix entries. -/
theorem sourceBilinearPrediction_apply (g : ℝ → ℝ)
    (z : SourceFactorParameter Item Model K) (i : Item) (j : Model) :
    sourcePrediction (fun uv => g ⟪uv.1, uv.2⟫) z (i, j) = g (sourceBilinearMatrix z i j) := by
  rw [sourcePrediction_apply, euclidean_inner_eq_finiteDot, sourceBilinearMatrix_apply]

/-- An actual inverse link reconstructs the matrix from the source fitted probabilities. -/
theorem sourceBilinearMatrix_eq_inverseLink (g inverseLink : ℝ → ℝ)
    (hinverse : LeftInverse inverseLink g) (z : SourceFactorParameter Item Model K) :
    sourceBilinearMatrix z = Matrix.of (fun i j =>
      inverseLink (sourcePrediction (fun uv => g ⟪uv.1, uv.2⟫) z (i, j))) := by
  ext i j
  rw [Matrix.of_apply, sourceBilinearPrediction_apply, hinverse]

/-- Injective links identify the entire bilinear matrix from the source probability array. -/
theorem sourceBilinearPrediction_eq_iff_matrix_eq (g : ℝ → ℝ) (hg : Injective g)
    (z w : SourceFactorParameter Item Model K) :
    sourcePrediction (fun uv => g ⟪uv.1, uv.2⟫) z =
      sourcePrediction (fun uv => g ⟪uv.1, uv.2⟫) w ↔
        sourceBilinearMatrix z = sourceBilinearMatrix w := by
  constructor
  · intro h
    ext i j
    apply hg
    simpa only [sourceBilinearPrediction_apply] using
      congrArg (fun q : SourcePredictionArray Item Model => q (i, j)) h
  · intro h
    apply PiLp.ext
    rintro ⟨i, j⟩
    rw [sourceBilinearPrediction_apply, sourceBilinearPrediction_apply, h]

/-- Source matrix rank and its Euclidean operator range dimension agree. -/
theorem matrixEuclideanOperatorEquiv_finrank_range_eq_rank
    [Fintype A] [Fintype B] (Θ : Matrix A B ℝ) :
    finrank ℝ (matrixEuclideanOperatorEquiv Θ).toLinearMap.range = Θ.rank := by
  classical
  exact (Θ.rank_eq_finrank_range_toLin
    (EuclideanSpace.basisFun A ℝ).toBasis (EuclideanSpace.basisFun B ℝ).toBasis).symm

/-- Under an injective link, equal fitted probabilities determine every singular value. -/
theorem sourceBilinearPrediction_singularValues_eq (g : ℝ → ℝ) (hg : Injective g)
    (z w : SourceFactorParameter Item Model K)
    (hprob : sourcePrediction (fun uv => g ⟪uv.1, uv.2⟫) z =
      sourcePrediction (fun uv => g ⟪uv.1, uv.2⟫) w) :
    (matrixEuclideanOperatorEquiv (sourceBilinearMatrix z)).toLinearMap.singularValues =
      (matrixEuclideanOperatorEquiv (sourceBilinearMatrix w)).toLinearMap.singularValues := by
  rw [(sourceBilinearPrediction_eq_iff_matrix_eq g hg z w).mp hprob]

/-- Full-column-rank source factors make the fitted matrix rank equal to the latent dimension. -/
theorem sourceBilinearMatrix_rank_of_fullRank
    (z : SourceFactorParameter Item Model K)
    (hz : FullRankOperatorFactors (sourceFactorOperatorEquiv z)) :
    finrank ℝ (matrixEuclideanOperatorEquiv (sourceBilinearMatrix z)).toLinearMap.range = K := by
  rw [sourceBilinearMatrix_operator]
  exact (factorProduct_rank_of_injective
    (sourceFactorOperatorEquiv z).1.toLinearMap (sourceFactorOperatorEquiv z).2.toLinearMap
    hz.1 hz.2).trans finrank_euclideanSpace_fin

/-- Every unrestricted full-rank source fit has a balanced fit with the same probabilities
and the maximal heterogeneity determined by its fitted inverse-link matrix. -/
theorem sourceFullRankFit_balanced_heterogeneity_maximum (hK : 0 < K)
    (g : ℝ → ℝ) (fit : SourceFactorParameter Item Model K)
    (hfit : FullRankOperatorFactors (sourceFactorOperatorEquiv fit)) :
    ∃ z : SourceFactorParameter Item Model K,
      sourcePrediction (fun uv => g ⟪uv.1, uv.2⟫) z =
        sourcePrediction (fun uv => g ⟪uv.1, uv.2⟫) fit ∧
      sourceBilinearMatrix z = sourceBilinearMatrix fit ∧
      FullRankOperatorFactors (sourceFactorOperatorEquiv z) ∧
      sourceFactorGramMatrix (fun i k => sourceItemFactor i z k) =
        sourceFactorGramMatrix (fun j k => sourceModelFactor j z k) ∧
      sourceHeterogeneity hK z =
        (matrixEuclideanOperatorEquiv (sourceBilinearMatrix fit)).toLinearMap.singularValues (K - 1) ∧
      ∀ w : SourceFactorParameter Item Model K, sourceBilinearMatrix w = sourceBilinearMatrix fit →
        sourceHeterogeneity hK w ≤ sourceHeterogeneity hK z := by
  obtain ⟨z, hprod, hfull, hbal, heq, hmax⟩ := sourceHeterogeneity_maximum_exists hK
    (sourceBilinearMatrix fit) (sourceBilinearMatrix_rank_of_fullRank fit hfit)
  refine ⟨z, ?_, hprod, hfull, hbal, heq, hmax⟩
  apply PiLp.ext
  rintro ⟨i, j⟩
  rw [sourceBilinearPrediction_apply, sourceBilinearPrediction_apply, hprod]

end

end JGR26SubjectivityMonoculture
