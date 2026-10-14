import JGR26SubjectivityMonoculture.SourcePredictionBridge
import JGR26SubjectivityMonoculture.BilinearConstantRank
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Data.Finset.Max

/-!
# Identification of the actual finite Euclidean MIRT prediction array

The source derivative is the link derivative times the bilinear linearization
in every item-model cell. Its Euclidean norm and kernel orthogonality therefore
instantiate the transverse Gram bound. Full-rank factor operators supply the
locally constant derivative rank.
-/

namespace JGR26SubjectivityMonoculture

open Filter Function Set
open scoped Topology BigOperators RealInnerProductSpace

noncomputable section

variable {K : ℕ} {Item Model : Type*} [Fintype Item] [Fintype Model]

/-- The source Euclidean array is linearly equivalent to the two factor matrices. -/
def sourceFactorArrayEquiv : SourceFactorParameter Item Model K ≃ₗ[ℝ]
    (Item → Fin K → ℝ) × (Model → Fin K → ℝ) where
  toFun z := (fun i k => z (Sum.inl i, k), fun j k => z (Sum.inr j, k))
  invFun factors := WithLp.toLp 2 (fun a => match a.1 with
    | Sum.inl i => factors.1 i a.2
    | Sum.inr j => factors.2 j a.2)
  left_inv z := by
    apply PiLp.ext
    rintro ⟨a, k⟩
    cases a <;> rfl
  right_inv factors := by
    apply Prod.ext <;> funext i k <;> rfl
  map_add' z w := by
    apply Prod.ext <;> funext i k <;> rfl
  map_smul' c z := by
    apply Prod.ext <;> funext i k <;> rfl

omit [Fintype Item] [Fintype Model] in
@[simp] theorem sourceFactorArrayEquiv_apply
    (z : SourceFactorParameter Item Model K) :
    sourceFactorArrayEquiv z =
      (fun i k => sourceItemFactor i z k, fun j k => sourceModelFactor j z k) := rfl

/-- Finite Euclidean inner products are the source dot products. -/
theorem euclidean_inner_eq_finiteDot (u v : EuclideanSpace ℝ (Fin K)) :
    ⟪u, v⟫ = finiteDot (fun k => u k) (fun k => v k) := by
  simp [PiLp.inner_apply, finiteDot, real_inner_eq_re_inner, RCLike.inner_apply, mul_comm]

/-- The real Euclidean inner product is a sum of coordinate products. -/
theorem realEuclidean_inner_eq_sum {A : Type*} [Fintype A] (u v : EuclideanSpace ℝ A) :
    ⟪u, v⟫ = ∑ a, u a * v a := by
  simp [PiLp.inner_apply, real_inner_eq_re_inner, RCLike.inner_apply, mul_comm]

/-- The source parameter inner product splits into its item and model dot products. -/
theorem sourceFactorParameter_inner
    (d e : SourceFactorParameter Item Model K) :
    ⟪d, e⟫ =
      (∑ i, finiteDot (fun k => sourceItemFactor i d k) (fun k => sourceItemFactor i e k)) +
        ∑ j, finiteDot (fun k => sourceModelFactor j d k) (fun k => sourceModelFactor j e k) := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type, Fintype.sum_sum_type]
  simp [finiteDot, real_inner_eq_re_inner, RCLike.inner_apply, mul_comm]

/-- The exact bilinear derivative in one source item-model cell. -/
def sourceBilinearCellDerivative (z : SourceFactorParameter Item Model K) (i : Item) (j : Model) :
    SourceFactorParameter Item Model K →L[ℝ] ℝ :=
  (fderivInnerCLM ℝ (sourceItemFactor i z, sourceModelFactor j z)).comp
    ((sourceItemFactor i).prod (sourceModelFactor j))

theorem hasFDerivAt_sourceBilinearCell
    (z : SourceFactorParameter Item Model K) (i : Item) (j : Model) :
    HasFDerivAt (fun w => ⟪sourceItemFactor i w, sourceModelFactor j w⟫)
      (sourceBilinearCellDerivative z i j) z :=
  (sourceItemFactor i).hasFDerivAt.inner ℝ (sourceModelFactor j).hasFDerivAt

omit [Fintype Item] [Fintype Model] in
@[simp] theorem sourceBilinearCellDerivative_apply
    (z d : SourceFactorParameter Item Model K) (i : Item) (j : Model) :
    sourceBilinearCellDerivative z i j d =
      finiteDot (fun k => sourceModelFactor j z k) (fun k => sourceItemFactor i d k) +
        finiteDot (fun k => sourceItemFactor i z k) (fun k => sourceModelFactor j d k) := by
  rw [sourceBilinearCellDerivative, ContinuousLinearMap.comp_apply, fderivInnerCLM_apply]
  simp only [ContinuousLinearMap.prod_apply]
  rw [real_inner_comm (sourceModelFactor j z) (sourceItemFactor i d), euclidean_inner_eq_finiteDot,
    euclidean_inner_eq_finiteDot, add_comm]

/-- The full link-weighted source derivative, with the source Euclidean codomain. -/
def sourceMIRTDerivative (g' : ℝ → ℝ) (z : SourceFactorParameter Item Model K) :
    SourceFactorParameter Item Model K →L[ℝ] SourcePredictionArray Item Model :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Item × Model => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun ij =>
      (g' ⟪sourceItemFactor ij.1 z, sourceModelFactor ij.2 z⟫) •
        sourceBilinearCellDerivative z ij.1 ij.2))

omit [Fintype Item] [Fintype Model] in
@[simp] theorem sourceMIRTDerivative_apply
    (g' : ℝ → ℝ) (z d : SourceFactorParameter Item Model K) (i : Item) (j : Model) :
    sourceMIRTDerivative g' z d (i, j) =
      (g' ⟪sourceItemFactor i z, sourceModelFactor j z⟫) *
        (finiteDot (fun k => sourceModelFactor j z k) (fun k => sourceItemFactor i d k) +
          finiteDot (fun k => sourceItemFactor i z k) (fun k => sourceModelFactor j d k)) := by
  change ((g' ⟪sourceItemFactor i z, sourceModelFactor j z⟫) •
    sourceBilinearCellDerivative z i j) d = _
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, sourceBilinearCellDerivative_apply]

/-- The source Jacobian is derived from actual derivatives of the scalar link. -/
theorem hasFDerivAt_sourceMIRTPrediction
    (g g' : ℝ → ℝ) (hg : ∀ t, HasDerivAt g (g' t) t)
    (z : SourceFactorParameter Item Model K) :
    HasFDerivAt (sourcePrediction (fun uv => g ⟪uv.1, uv.2⟫)) (sourceMIRTDerivative g' z) z := by
  apply (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Item × Model => ℝ)).symm.toContinuousLinearMap.hasFDerivAt.comp z
  apply hasFDerivAt_pi.mpr
  intro ij
  exact (hg ⟪sourceItemFactor ij.1 z, sourceModelFactor ij.2 z⟫).comp_hasFDerivAt z
    (hasFDerivAt_sourceBilinearCell z ij.1 ij.2)

/-- Normality to the actual Euclidean Jacobian kernel gives the source finite-array normality. -/
theorem sourceMIRT_kernelOrthogonal_of_actual
    (g' : ℝ → ℝ) (z d : SourceFactorParameter Item Model K)
    (horth : ∀ e, sourceMIRTDerivative g' z e = 0 → ⟪d, e⟫ = 0) :
    IsMIRTKernelOrthogonal
      (fun i k => sourceItemFactor i z k) (fun j k => sourceModelFactor j z k)
      (fun i j => g' ⟪sourceItemFactor i z, sourceModelFactor j z⟫)
      (fun i k => sourceItemFactor i d k) (fun j k => sourceModelFactor j d k) := by
  intro eU eV he
  let e := sourceFactorArrayEquiv.symm (eU, eV)
  have hzero : sourceMIRTDerivative g' z e = 0 := by
    apply PiLp.ext
    rintro ⟨i, j⟩
    simpa [e, sourceFactorArrayEquiv] using he i j
  have h := horth e hzero
  rw [sourceFactorParameter_inner] at h
  simpa [e, sourceFactorArrayEquiv] using h

/-- The Gram bounds prove the exact `m² h` inequality for the actual source Jacobian. -/
theorem sourceMIRTDerivative_sq_lower_bound
    (g' : ℝ → ℝ) (z d : SourceFactorParameter Item Model K) {m h : ℝ}
    (hm : 0 ≤ m)
    (hweight : ∀ i j, m ≤ g' ⟪sourceItemFactor i z, sourceModelFactor j z⟫)
    (hU : FactorGramLowerBound h (fun i k => sourceItemFactor i z k))
    (hV : FactorGramLowerBound h (fun j k => sourceModelFactor j z k))
    (horth : ∀ e, sourceMIRTDerivative g' z e = 0 → ⟪d, e⟫ = 0) :
    (m ^ 2 * h) * ‖d‖ ^ 2 ≤ ‖sourceMIRTDerivative g' z d‖ ^ 2 := by
  have h := mirtLinearizedSq_lower_bound_of_kernelOrthogonal
    (fun i k => sourceItemFactor i z k) (fun j k => sourceModelFactor j z k)
    (fun i k => sourceItemFactor i d k) (fun j k => sourceModelFactor j d k)
    (fun i j => g' ⟪sourceItemFactor i z, sourceModelFactor j z⟫) hm hweight hU hV
    (sourceMIRT_kernelOrthogonal_of_actual g' z d horth)
  rw [sourceFactorParameter_norm_sq, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  simpa only [heterogeneityParameterSq, finiteSqNorm, sourceMIRTDerivative_apply,
    Real.norm_eq_abs, sq_abs] using h

/-- A finite matrix and its operator on the corresponding Euclidean spaces are equivalent. -/
def matrixEuclideanOperatorEquiv {A B : Type*} [Fintype A] [Fintype B] :
    Matrix A B ℝ ≃ₗ[ℝ] (EuclideanSpace ℝ B →L[ℝ] EuclideanSpace ℝ A) := by
  classical
  exact Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap

@[simp] theorem matrixEuclideanOperatorEquiv_apply {A B : Type*} [Fintype A] [Fintype B]
    (M : Matrix A B ℝ) (x : EuclideanSpace ℝ B) (a : A) :
    matrixEuclideanOperatorEquiv M x a = ∑ b, M a b * x b := rfl

/-- Applying the adjoint to a coordinate vector selects the corresponding matrix row. -/
theorem matrixEuclideanOperatorEquiv_adjoint_single
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (M : Matrix A B ℝ) (a : A) (b : B) :
    (matrixEuclideanOperatorEquiv M).adjoint (EuclideanSpace.single a 1) b = M a b := by
  have h := (matrixEuclideanOperatorEquiv M).adjoint_inner_right
    (EuclideanSpace.single b 1) (EuclideanSpace.single a 1)
  simpa [realEuclidean_inner_eq_sum, matrixEuclideanOperatorEquiv_apply,
    PiLp.single_apply, mul_comm] using h

/-- The source factors as the two actual full-column-rank operators. -/
def sourceFactorOperatorEquiv : SourceFactorParameter Item Model K ≃L[ℝ]
    ((EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ Item) ×
      (EuclideanSpace ℝ (Fin K) →L[ℝ] EuclideanSpace ℝ Model)) :=
  (sourceFactorArrayEquiv.trans
    (matrixEuclideanOperatorEquiv.prodCongr matrixEuclideanOperatorEquiv)).toContinuousLinearEquiv

@[simp] theorem sourceFactorOperatorEquiv_fst (z : SourceFactorParameter Item Model K) :
    (sourceFactorOperatorEquiv z).1 =
      matrixEuclideanOperatorEquiv (fun i k => sourceItemFactor i z k) := rfl

@[simp] theorem sourceFactorOperatorEquiv_snd (z : SourceFactorParameter Item Model K) :
    (sourceFactorOperatorEquiv z).2 =
      matrixEuclideanOperatorEquiv (fun j k => sourceModelFactor j z k) := rfl

/-- Euclidean prediction arrays are linearly equivalent to their cell matrices. -/
def sourcePredictionMatrixEquiv : SourcePredictionArray Item Model ≃ₗ[ℝ] Matrix Item Model ℝ where
  toFun q i j := q (i, j)
  invFun M := WithLp.toLp 2 (fun ij => M ij.1 ij.2)
  left_inv q := by apply PiLp.ext; rintro ⟨i, j⟩; rfl
  right_inv M := by funext i j; rfl
  map_add' q r := by funext i j; rfl
  map_smul' c q := by funext i j; rfl

/-- The source prediction array as an operator from model to item coordinates. -/
def sourcePredictionOperatorEquiv : SourcePredictionArray Item Model ≃L[ℝ]
    (EuclideanSpace ℝ Model →L[ℝ] EuclideanSpace ℝ Item) :=
  (sourcePredictionMatrixEquiv.trans matrixEuclideanOperatorEquiv).toContinuousLinearEquiv

theorem sourcePredictionOperatorEquiv_single [DecidableEq Model] (q : SourcePredictionArray Item Model)
    (i : Item) (j : Model) :
    sourcePredictionOperatorEquiv q (EuclideanSpace.single j 1) i = q (i, j) := by
  classical
  change (matrixEuclideanOperatorEquiv (fun i j => q (i, j))) (EuclideanSpace.single j 1) i = _
  rw [matrixEuclideanOperatorEquiv_apply]
  simp [PiLp.single_apply]

/-- Positive source Gram strength forces the corresponding factor operator to be injective. -/
theorem matrixEuclideanOperatorEquiv_injective_of_gramLowerBound
    {A : Type*} [Fintype A] (U : A → Fin K → ℝ) {h : ℝ}
    (hh : 0 < h) (hU : FactorGramLowerBound h U) :
    Injective (matrixEuclideanOperatorEquiv U) := by
  intro x y hxy
  have hx' : matrixEuclideanOperatorEquiv U (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have h := hU (fun k => (x - y) k)
  have hzero : ∀ a, finiteDot (U a) (fun k => (x - y) k) = 0 := by
    intro a
    have hpoint := congrArg (fun v : EuclideanSpace ℝ A => v a) hx'
    exact hpoint
  simp only [hzero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero] at h
  have hnorm : finiteSqNorm (fun k => (x - y) k) = ‖x - y‖ ^ 2 := by
    simp only [finiteSqNorm, EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
  rw [hnorm] at h
  have hsq : ‖x - y‖ ^ 2 ≤ 0 :=
    le_of_not_gt (fun hs => not_lt_of_ge h (mul_pos hh hs))
  have hn : ‖x - y‖ = 0 := sq_eq_zero_iff.mp (le_antisymm hsq (sq_nonneg _))
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

/-- The two positive Gram bounds give the native full-rank factor condition. -/
theorem sourceFactorOperator_fullRank_of_gramLowerBounds
    (z : SourceFactorParameter Item Model K) {h : ℝ} (hh : 0 < h)
    (hU : FactorGramLowerBound h (fun i k => sourceItemFactor i z k))
    (hV : FactorGramLowerBound h (fun j k => sourceModelFactor j z k)) :
    FullRankOperatorFactors (sourceFactorOperatorEquiv z) := by
  exact ⟨matrixEuclideanOperatorEquiv_injective_of_gramLowerBound _ hh hU,
    matrixEuclideanOperatorEquiv_injective_of_gramLowerBound _ hh hV⟩

/-- The unweighted source Jacobian is the native bilinear operator Jacobian in source coordinates. -/
theorem sourceBilinearDerivative_operator_transport
    (z d : SourceFactorParameter Item Model K) :
    sourcePredictionOperatorEquiv (sourceMIRTDerivative (fun _ => 1) z d) =
      bilinearOperatorDerivative (sourceFactorOperatorEquiv z).1 (sourceFactorOperatorEquiv z).2
        (sourceFactorOperatorEquiv d) := by
  classical
  let L := sourcePredictionOperatorEquiv (sourceMIRTDerivative (fun _ => 1) z d)
  let R := bilinearOperatorDerivative
    (sourceFactorOperatorEquiv z).1 (sourceFactorOperatorEquiv z).2 (sourceFactorOperatorEquiv d)
  have hlinear : L.toLinearMap = R.toLinearMap := by
    apply (EuclideanSpace.basisFun Model ℝ).toBasis.ext
    intro j
    change L (EuclideanSpace.basisFun Model ℝ j) = R (EuclideanSpace.basisFun Model ℝ j)
    rw [EuclideanSpace.basisFun_apply]
    apply PiLp.ext
    intro i
    simp [L, R, sourcePredictionOperatorEquiv_single, bilinearOperatorDerivative_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      matrixEuclideanOperatorEquiv_adjoint_single, matrixEuclideanOperatorEquiv_apply,
      sourceMIRTDerivative_apply, finiteDot, mul_comm]
  apply ContinuousLinearMap.ext
  intro x
  exact congrArg (fun T : EuclideanSpace ℝ Model →ₗ[ℝ] EuclideanSpace ℝ Item => T x) hlinear

/-- Zero source bilinear derivative is equivalent to zero native operator derivative. -/
theorem sourceBilinearDerivative_eq_zero_iff_operator
    (z d : SourceFactorParameter Item Model K) :
    sourceMIRTDerivative (fun _ => 1) z d = 0 ↔
      bilinearOperatorDerivative (sourceFactorOperatorEquiv z).1 (sourceFactorOperatorEquiv z).2
        (sourceFactorOperatorEquiv d) = 0 := by
  constructor
  · intro hd
    rw [← sourceBilinearDerivative_operator_transport, hd, map_zero]
  · intro hd
    apply (sourcePredictionOperatorEquiv (Item := Item) (Model := Model)).injective
    rw [sourceBilinearDerivative_operator_transport, hd, map_zero]

/-- Source and operator-coordinate bilinear kernels are actually linearly equivalent. -/
def sourceBilinearKernelEquiv (z : SourceFactorParameter Item Model K) :
    (sourceMIRTDerivative (fun _ => 1) z).ker ≃ₗ[ℝ]
      (bilinearOperatorDerivative (sourceFactorOperatorEquiv z).1 (sourceFactorOperatorEquiv z).2).ker where
  toFun d := ⟨sourceFactorOperatorEquiv d.val,
    (sourceBilinearDerivative_eq_zero_iff_operator z d.val).mp d.property⟩
  invFun d := ⟨sourceFactorOperatorEquiv.symm d.val,
    (sourceBilinearDerivative_eq_zero_iff_operator z _).mpr
      (by simpa only [ContinuousLinearEquiv.apply_symm_apply] using d.property)⟩
  left_inv d := Subtype.ext (ContinuousLinearEquiv.symm_apply_apply sourceFactorOperatorEquiv d.val)
  right_inv d := Subtype.ext (ContinuousLinearEquiv.apply_symm_apply sourceFactorOperatorEquiv d.val)
  map_add' d e := Subtype.ext (map_add sourceFactorOperatorEquiv d.val e.val)
  map_smul' c d := Subtype.ext (map_smul sourceFactorOperatorEquiv c d.val)

omit [Fintype Item] [Fintype Model] in
/-- Nonzero link derivatives leave the bilinear Jacobian kernel unchanged. -/
theorem sourceMIRTDerivative_ker_eq_unweighted
    (g' : ℝ → ℝ) (z : SourceFactorParameter Item Model K)
    (hweight : ∀ i j, g' ⟪sourceItemFactor i z, sourceModelFactor j z⟫ ≠ 0) :
    (sourceMIRTDerivative g' z).ker = (sourceMIRTDerivative (fun _ => 1) z).ker := by
  ext d
  constructor
  · intro hd
    have hd' : sourceMIRTDerivative g' z d = 0 := hd
    apply PiLp.ext
    rintro ⟨i, j⟩
    have hpoint := congrArg (fun q : SourcePredictionArray Item Model => q (i, j)) hd'
    change sourceMIRTDerivative g' z d (i, j) = 0 at hpoint
    rw [sourceMIRTDerivative_apply] at hpoint
    have hzero := (mul_eq_zero.mp hpoint).resolve_left (hweight i j)
    change sourceMIRTDerivative (fun _ => 1) z d (i, j) = 0
    rw [sourceMIRTDerivative_apply, one_mul]
    exact hzero
  · intro hd
    have hd' : sourceMIRTDerivative (fun _ => 1) z d = 0 := hd
    apply PiLp.ext
    rintro ⟨i, j⟩
    have hpoint := congrArg (fun q : SourcePredictionArray Item Model => q (i, j)) hd'
    change sourceMIRTDerivative (fun _ => 1) z d (i, j) = 0 at hpoint
    rw [sourceMIRTDerivative_apply, one_mul] at hpoint
    change sourceMIRTDerivative g' z d (i, j) = 0
    rw [sourceMIRTDerivative_apply, hpoint, mul_zero]

/-- The actual link-weighted source kernel has dimension `K²` on full-rank factors. -/
theorem sourceMIRTDerivative_ker_finrank
    (g' : ℝ → ℝ) (z : SourceFactorParameter Item Model K)
    (hfull : FullRankOperatorFactors (sourceFactorOperatorEquiv z))
    (hweight : ∀ i j, g' ⟪sourceItemFactor i z, sourceModelFactor j z⟫ ≠ 0) :
    Module.finrank ℝ (sourceMIRTDerivative g' z).ker = K ^ 2 := by
  rw [sourceMIRTDerivative_ker_eq_unweighted g' z hweight,
    (sourceBilinearKernelEquiv z).finrank_eq]
  simpa using finrank_bilinearOperatorDerivative_ker
    (sourceFactorOperatorEquiv z).1 (sourceFactorOperatorEquiv z).2 hfull.1 hfull.2

/-- Full-rank source predictions have a factor-independent link-weighted derivative rank. -/
theorem sourceMIRTDerivative_range_finrank
    (g' : ℝ → ℝ) (z : SourceFactorParameter Item Model K)
    (hfull : FullRankOperatorFactors (sourceFactorOperatorEquiv z))
    (hweight : ∀ i j, g' ⟪sourceItemFactor i z, sourceModelFactor j z⟫ ≠ 0) :
    Module.finrank ℝ (sourceMIRTDerivative g' z).range =
      Module.finrank ℝ (SourceFactorParameter Item Model K) - K ^ 2 := by
  have h := (sourceMIRTDerivative g' z).toLinearMap.finrank_range_add_finrank_ker
  rw [sourceMIRTDerivative_ker_finrank g' z hfull hweight] at h
  exact Nat.eq_sub_of_add_eq h

/-- Source positive Gram bounds and nonzero link derivatives give actual local constant rank. -/
theorem sourceMIRTDerivative_eventually_rank_eq
    (g' : ℝ → ℝ) (hpositive : ∀ t, g' t ≠ 0)
    (fit : SourceFactorParameter Item Model K) {h : ℝ} (hh : 0 < h)
    (hU : FactorGramLowerBound h (fun i k => sourceItemFactor i fit k))
    (hV : FactorGramLowerBound h (fun j k => sourceModelFactor j fit k)) :
    ∀ᶠ z in 𝓝 fit, Module.finrank ℝ (sourceMIRTDerivative g' z).range =
      Module.finrank ℝ (sourceMIRTDerivative g' fit).range := by
  have hfull := sourceFactorOperator_fullRank_of_gramLowerBounds fit hh hU hV
  have hnear := sourceFactorOperatorEquiv.continuous.tendsto fit |>.eventually
    (isOpen_fullRankOperatorFactors.mem_nhds hfull)
  filter_upwards [hnear] with z hz
  rw [sourceMIRTDerivative_range_finrank g' z hz (fun i j => hpositive _),
    sourceMIRTDerivative_range_finrank g' fit hfull (fun i j => hpositive _)]

/-- Constant rank of the literal source Fréchet derivative follows from the MIRT primitives. -/
theorem sourceMIRTPrediction_eventually_fderiv_rank_eq
    (g g' : ℝ → ℝ) (hg : ∀ t, HasDerivAt g (g' t) t) (hpositive : ∀ t, g' t ≠ 0)
    (fit : SourceFactorParameter Item Model K) {h : ℝ} (hh : 0 < h)
    (hU : FactorGramLowerBound h (fun i k => sourceItemFactor i fit k))
    (hV : FactorGramLowerBound h (fun j k => sourceModelFactor j fit k)) :
    ∀ᶠ z in 𝓝 fit,
      Module.finrank ℝ (fderiv ℝ (sourcePrediction (fun uv => g ⟪uv.1, uv.2⟫)) z).range =
        Module.finrank ℝ (fderiv ℝ (sourcePrediction (fun uv => g ⟪uv.1, uv.2⟫)) fit).range := by
  filter_upwards [sourceMIRTDerivative_eventually_rank_eq g' hpositive fit hh hU hV] with z hz
  rw [(hasFDerivAt_sourceMIRTPrediction g g' hg z).fderiv,
    (hasFDerivAt_sourceMIRTPrediction g g' hg fit).fderiv]
  exact hz

/-- Lemma 8 constructs Assumption 1 for the actual Euclidean source prediction map. -/
theorem source_mirt_localIdentification_of_gramLowerBounds
    (g : ℝ → ℝ) (hsmooth : ContDiff ℝ 2 g) (hpositive : ∀ t, 0 < deriv g t)
    (fit : SourceFactorParameter Item Model K) {m h : ℝ} (hm : 0 < m) (hh : 0 < h)
    (hweight : ∀ i j, m ≤ deriv g ⟪sourceItemFactor i fit, sourceModelFactor j fit⟫)
    (hU : FactorGramLowerBound h (fun i k => sourceItemFactor i fit k))
    (hV : FactorGramLowerBound h (fun j k => sourceModelFactor j fit k)) :
    HasLocalIdentificationAt (sourcePrediction (fun uv => g ⟪uv.1, uv.2⟫)) fit (m ^ 2) h := by
  have hg : ∀ t, HasDerivAt g (deriv g t) t :=
    fun t => (hsmooth.differentiable (by norm_num) t).hasDerivAt
  refine ⟨sourceMIRTPrediction_eventually_fderiv_rank_eq g (deriv g) hg
    (fun t => ne_of_gt (hpositive t)) fit hh hU hV, ?_⟩
  intro d hd
  rw [(hasFDerivAt_sourceMIRTPrediction g (deriv g) hg fit).fderiv] at hd ⊢
  exact sourceMIRTDerivative_sq_lower_bound (deriv g) fit d hm.le hweight hU hV hd

/-- On nonempty finite populations, the fitted link-derivative minimum is positive. -/
theorem exists_positive_fitted_linkDerivative_minimum [Nonempty Item] [Nonempty Model]
    (g' : ℝ → ℝ) (hpositive : ∀ t, 0 < g' t)
    (fit : SourceFactorParameter Item Model K) :
    ∃ m > 0,
      (∃ i j, m = g' ⟪sourceItemFactor i fit, sourceModelFactor j fit⟫) ∧
      ∀ i j, m ≤ g' ⟪sourceItemFactor i fit, sourceModelFactor j fit⟫ := by
  classical
  let values : Finset ℝ := Finset.univ.image
    (fun ij : Item × Model => g' ⟪sourceItemFactor ij.1 fit, sourceModelFactor ij.2 fit⟫)
  have hne : values.Nonempty := Finset.univ_nonempty.image _
  have hpositive' : 0 < values.min' hne := (Finset.lt_min'_iff _ _).mpr (by
    intro value hv
    obtain ⟨ij, _, rfl⟩ := Finset.mem_image.mp hv
    exact hpositive _)
  refine ⟨values.min' hne, hpositive', ?_, ?_⟩
  · obtain ⟨ij, _, hij⟩ := Finset.mem_image.mp (values.min'_mem hne)
    exact ⟨ij.1, ij.2, hij.symm⟩
  · intro i j
    exact values.min'_le _ (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩)

/-- Lemma 8 constructs identification with `c = m²` for the actual fitted derivative minimum. -/
theorem source_lemma8_mirt_identification [Nonempty Item] [Nonempty Model]
    (g : ℝ → ℝ) (hsmooth : ContDiff ℝ 2 g) (hpositive : ∀ t, 0 < deriv g t)
    (fit : SourceFactorParameter Item Model K) {h : ℝ} (hh : 0 < h)
    (hU : FactorGramLowerBound h (fun i k => sourceItemFactor i fit k))
    (hV : FactorGramLowerBound h (fun j k => sourceModelFactor j fit k)) :
    ∃ m > 0,
      (∃ i j, m = deriv g ⟪sourceItemFactor i fit, sourceModelFactor j fit⟫) ∧
      (∀ i j, m ≤ deriv g ⟪sourceItemFactor i fit, sourceModelFactor j fit⟫) ∧
      HasLocalIdentificationAt (sourcePrediction (fun uv => g ⟪uv.1, uv.2⟫)) fit (m ^ 2) h := by
  obtain ⟨m, hm, hattain, hlower⟩ :=
    exists_positive_fitted_linkDerivative_minimum (deriv g) hpositive fit
  exact ⟨m, hm, hattain, hlower,
    source_mirt_localIdentification_of_gramLowerBounds g hsmooth hpositive fit hm hh hlower hU hV⟩

/-- Source perturbations retaining every selected fixed model coordinate. -/
def sourceFixedFactorPerturbations (fixed : Finset (Fin K)) :
    Submodule ℝ (SourceFactorParameter Item Model K) where
  carrier := {d | ∀ j k, k ∈ fixed → d (Sum.inr j, k) = 0}
  zero_mem' := by intro j k hk; rfl
  add_mem' := by intro d e hd he j k hk; simp [hd j k hk, he j k hk]
  smul_mem' := by intro c d hd j k hk; simp [hd j k hk]

/-- The actual source derivative restricted to the fixed-coordinate tangent space. -/
def sourceMIRTDerivativeWithin (fixed : Finset (Fin K)) (g' : ℝ → ℝ)
    (fit : SourceFactorParameter Item Model K) :
    sourceFixedFactorPerturbations (Item := Item) (Model := Model) fixed →L[ℝ]
      SourcePredictionArray Item Model :=
  (sourceMIRTDerivative g' fit).comp (sourceFixedFactorPerturbations fixed).subtypeL

/-- Source Euclidean kernel normality supplies the fixed-coordinate array normality. -/
theorem sourceMIRT_kernelOrthogonalWithin_of_actual
    (fixed : Finset (Fin K)) (g' : ℝ → ℝ) (z : SourceFactorParameter Item Model K)
    (d : sourceFixedFactorPerturbations (Item := Item) (Model := Model) fixed)
    (horth : ∀ e, sourceMIRTDerivativeWithin fixed g' z e = 0 → ⟪d, e⟫ = 0) :
    IsMIRTKernelOrthogonalWithin fixed
      (fun i k => sourceItemFactor i z k) (fun j k => sourceModelFactor j z k)
      (fun i j => g' ⟪sourceItemFactor i z, sourceModelFactor j z⟫)
      (fun i k => sourceItemFactor i d.val k) (fun j k => sourceModelFactor j d.val k) := by
  intro eU eV heFixed he
  let e₀ := sourceFactorArrayEquiv.symm (eU, eV)
  have he₀ : e₀ ∈ sourceFixedFactorPerturbations (Item := Item) (Model := Model) fixed := by
    intro j k hk
    exact heFixed j k hk
  let e : sourceFixedFactorPerturbations (Item := Item) (Model := Model) fixed := ⟨e₀, he₀⟩
  have hzero : sourceMIRTDerivativeWithin fixed g' z e = 0 := by
    apply PiLp.ext
    rintro ⟨i, j⟩
    change sourceMIRTDerivative g' z e₀ (i, j) = 0
    simpa [e₀, sourceFactorArrayEquiv] using he i j
  have hnormal := horth e hzero
  change ⟪d.val, e₀⟫ = 0 at hnormal
  rw [sourceFactorParameter_inner] at hnormal
  simpa [e₀, sourceFactorArrayEquiv] using hnormal

/-- The exact source `m² h` normal bound holds with selected model coordinates fixed. -/
theorem sourceMIRTDerivativeWithin_sq_lower_bound
    (fixed : Finset (Fin K)) (g' : ℝ → ℝ) (z : SourceFactorParameter Item Model K)
    (d : sourceFixedFactorPerturbations (Item := Item) (Model := Model) fixed) {m h : ℝ}
    (hm : 0 ≤ m)
    (hweight : ∀ i j, m ≤ g' ⟪sourceItemFactor i z, sourceModelFactor j z⟫)
    (hU : FactorGramLowerBound h (fun i k => sourceItemFactor i z k))
    (hV : FactorGramLowerBound h (fun j k => sourceModelFactor j z k))
    (horth : ∀ e, sourceMIRTDerivativeWithin fixed g' z e = 0 → ⟪d, e⟫ = 0) :
    (m ^ 2 * h) * ‖d‖ ^ 2 ≤ ‖sourceMIRTDerivativeWithin fixed g' z d‖ ^ 2 := by
  have hd : HasZeroFixedCoordinates fixed (fun j k => sourceModelFactor j d.val k) := d.property
  have hbound := mirtLinearizedSq_lower_bound_of_kernelOrthogonalWithin fixed
    (fun i k => sourceItemFactor i z k) (fun j k => sourceModelFactor j z k)
    (fun i k => sourceItemFactor i d.val k) (fun j k => sourceModelFactor j d.val k)
    (fun i j => g' ⟪sourceItemFactor i z, sourceModelFactor j z⟫) hm hweight hU hV hd
    (sourceMIRT_kernelOrthogonalWithin_of_actual fixed g' z d horth)
  change (m ^ 2 * h) * ‖d.val‖ ^ 2 ≤ ‖sourceMIRTDerivative g' z d.val‖ ^ 2
  rw [sourceFactorParameter_norm_sq, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  simpa only [heterogeneityParameterSq, finiteSqNorm, sourceMIRTDerivative_apply,
    Real.norm_eq_abs, sq_abs] using hbound

/-- The latent coordinate subspace spanned by the held-fixed coordinates. -/
def fixedLatentCoordinateSubspace (fixed : Finset (Fin K)) :
    Submodule ℝ (EuclideanSpace ℝ (Fin K)) where
  carrier := {w | ∀ k, k ∉ fixed → w k = 0}
  zero_mem' := by intro k hk; rfl
  add_mem' := by intro w v hw hv k hk; simp [hw k hk, hv k hk]
  smul_mem' := by intro c w hw k hk; simp [hw k hk]

/-- Fixed source columns are exactly operator perturbations vanishing on the fixed latent subspace. -/
theorem sourceFactorOperatorEquiv_fixed_iff
    (fixed : Finset (Fin K)) (d : SourceFactorParameter Item Model K) :
    d ∈ sourceFixedFactorPerturbations fixed ↔
      sourceFactorOperatorEquiv d ∈ fixedOperatorPerturbations
        (I := EuclideanSpace ℝ Item) (J := EuclideanSpace ℝ Model)
        (fixedLatentCoordinateSubspace fixed) := by
  classical
  constructor
  · intro hd w hw
    apply PiLp.ext
    intro j
    rw [sourceFactorOperatorEquiv_snd, matrixEuclideanOperatorEquiv_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k ∈ fixed
    · rw [show sourceModelFactor j d k = 0 from hd j k hk, zero_mul]
    · rw [show w k = 0 from hw k hk, mul_zero]
  · intro hd j k hk
    have hsingle : EuclideanSpace.single k (1 : ℝ) ∈ fixedLatentCoordinateSubspace fixed := by
      intro a ha
      have hne : a ≠ k := fun heq => ha (heq ▸ hk)
      simp [hne]
    have hpoint := congrArg (fun v : EuclideanSpace ℝ Model => v j)
      (hd (EuclideanSpace.single k 1) hsingle)
    simpa [sourceFactorOperatorEquiv_snd, matrixEuclideanOperatorEquiv_apply,
      PiLp.single_apply] using hpoint

/-- The actual source and operator admissible perturbation spaces are linearly equivalent. -/
def sourceFixedFactorOperatorEquiv (fixed : Finset (Fin K)) :
    sourceFixedFactorPerturbations (Item := Item) (Model := Model) fixed ≃ₗ[ℝ]
      fixedOperatorPerturbations (I := EuclideanSpace ℝ Item) (J := EuclideanSpace ℝ Model)
        (fixedLatentCoordinateSubspace fixed) where
  toFun d := ⟨sourceFactorOperatorEquiv d.val,
    (sourceFactorOperatorEquiv_fixed_iff fixed d.val).mp d.property⟩
  invFun d := ⟨sourceFactorOperatorEquiv.symm d.val,
    (sourceFactorOperatorEquiv_fixed_iff fixed _).mpr
      (by simpa only [ContinuousLinearEquiv.apply_symm_apply] using d.property)⟩
  left_inv d := Subtype.ext (ContinuousLinearEquiv.symm_apply_apply sourceFactorOperatorEquiv d.val)
  right_inv d := Subtype.ext (ContinuousLinearEquiv.apply_symm_apply sourceFactorOperatorEquiv d.val)
  map_add' d e := Subtype.ext (map_add sourceFactorOperatorEquiv d.val e.val)
  map_smul' c d := Subtype.ext (map_smul sourceFactorOperatorEquiv c d.val)

/-- Coordinate changes in both spaces preserve the rank of a linear map. -/
theorem finrank_range_eq_of_linear_transport
    {E F E' F' : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup F] [Module ℝ F] [AddCommGroup E'] [Module ℝ E']
    [AddCommGroup F'] [Module ℝ F']
    (a : E ≃ₗ[ℝ] E') (b : F ≃ₗ[ℝ] F') (L : E →ₗ[ℝ] F) (R : E' →ₗ[ℝ] F')
    (htransport : b.toLinearMap.comp L = R.comp a.toLinearMap) :
    Module.finrank ℝ L.range = Module.finrank ℝ R.range := by
  have hr := congrArg (fun T : E →ₗ[ℝ] F' => Module.finrank ℝ T.range) htransport
  change Module.finrank ℝ (b.toLinearMap.comp L).range =
    Module.finrank ℝ (R.comp a.toLinearMap).range at hr
  rw [LinearMap.range_comp, b.finrank_map_eq, LinearMap.range_comp,
    a.range, Submodule.map_top] at hr
  exact hr

/-- The fixed-coordinate source bilinear derivative has exactly the native admissible rank. -/
theorem sourceBilinearDerivativeWithin_rank_eq_operator
    (fixed : Finset (Fin K)) (z : SourceFactorParameter Item Model K) :
    Module.finrank ℝ (sourceMIRTDerivativeWithin fixed (fun _ => 1) z).range =
      Module.finrank ℝ (bilinearOperatorDerivativeWithin (fixedLatentCoordinateSubspace fixed)
        (sourceFactorOperatorEquiv z).1 (sourceFactorOperatorEquiv z).2).range := by
  apply finrank_range_eq_of_linear_transport (sourceFixedFactorOperatorEquiv fixed)
    sourcePredictionOperatorEquiv.toLinearEquiv
  apply LinearMap.ext
  intro d
  exact sourceBilinearDerivative_operator_transport z d.val

omit [Fintype Item] [Fintype Model] in
/-- Nonzero link derivatives preserve the kernel on the fixed source tangent space. -/
theorem sourceMIRTDerivativeWithin_ker_eq_unweighted
    (fixed : Finset (Fin K)) (g' : ℝ → ℝ) (z : SourceFactorParameter Item Model K)
    (hpositive : ∀ t, g' t ≠ 0) :
    (sourceMIRTDerivativeWithin fixed g' z).ker =
      (sourceMIRTDerivativeWithin fixed (fun _ => 1) z).ker := by
  ext d
  change d.val ∈ (sourceMIRTDerivative g' z).ker ↔
    d.val ∈ (sourceMIRTDerivative (fun _ => 1) z).ker
  rw [sourceMIRTDerivative_ker_eq_unweighted g' z (fun i j => hpositive _)]

/-- Nonzero link derivatives preserve the rank on the fixed source tangent space. -/
theorem sourceMIRTDerivativeWithin_rank_eq_unweighted
    (fixed : Finset (Fin K)) (g' : ℝ → ℝ) (z : SourceFactorParameter Item Model K)
    (hpositive : ∀ t, g' t ≠ 0) :
    Module.finrank ℝ (sourceMIRTDerivativeWithin fixed g' z).range =
      Module.finrank ℝ (sourceMIRTDerivativeWithin fixed (fun _ => 1) z).range := by
  have h₁ := (sourceMIRTDerivativeWithin fixed g' z).toLinearMap.finrank_range_add_finrank_ker
  have h₂ := (sourceMIRTDerivativeWithin fixed (fun _ => 1) z).toLinearMap.finrank_range_add_finrank_ker
  rw [sourceMIRTDerivativeWithin_ker_eq_unweighted fixed g' z hpositive] at h₁
  exact Nat.add_right_cancel (h₁.trans h₂.symm)

/-- The fixed-source derivative rank is locally constant at positive-Gram factors. -/
theorem sourceMIRTDerivativeWithin_eventually_rank_eq
    (fixed : Finset (Fin K)) (g' : ℝ → ℝ) (hpositive : ∀ t, g' t ≠ 0)
    (fit : SourceFactorParameter Item Model K) {h : ℝ} (hh : 0 < h)
    (hU : FactorGramLowerBound h (fun i k => sourceItemFactor i fit k))
    (hV : FactorGramLowerBound h (fun j k => sourceModelFactor j fit k)) :
    ∀ᶠ z in 𝓝 fit, Module.finrank ℝ (sourceMIRTDerivativeWithin fixed g' z).range =
      Module.finrank ℝ (sourceMIRTDerivativeWithin fixed g' fit).range := by
  have ht := sourceFactorOperatorEquiv.continuous.tendsto fit
  filter_upwards [ht.eventually (eventually_bilinearOperatorDerivativeWithin_rank_eq
    (fixedLatentCoordinateSubspace fixed) (sourceFactorOperatorEquiv fit)
    (sourceFactorOperator_fullRank_of_gramLowerBounds fit hh hU hV))] with z hz
  rw [sourceMIRTDerivativeWithin_rank_eq_unweighted fixed g' z hpositive,
    sourceMIRTDerivativeWithin_rank_eq_unweighted fixed g' fit hpositive,
    sourceBilinearDerivativeWithin_rank_eq_operator, sourceBilinearDerivativeWithin_rank_eq_operator]
  exact hz

/-- The source MIRT link is twice continuously differentiable. -/
theorem sourceMIRTLink_contDiff (g : ℝ → ℝ) (hsmooth : ContDiff ℝ 2 g) :
    ContDiff ℝ 2 (fun uv : EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin K) => g ⟪uv.1, uv.2⟫) :=
  hsmooth.comp (contDiff_fst.inner ℝ contDiff_snd)

/-- Predictions on the literal affine source space of fixed model coordinates. -/
def sourceMIRTPredictionWithin (fixed : Finset (Fin K)) (g : ℝ → ℝ)
    (fit : SourceFactorParameter Item Model K)
    (d : sourceFixedFactorPerturbations (Item := Item) (Model := Model) fixed) :
    SourcePredictionArray Item Model :=
  sourcePrediction (fun uv => g ⟪uv.1, uv.2⟫) (fit + d.val)

/-- The affine source derivative is the actual link-weighted derivative on admissible perturbations. -/
theorem hasFDerivAt_sourceMIRTPredictionWithin
    (fixed : Finset (Fin K)) (g g' : ℝ → ℝ) (hg : ∀ t, HasDerivAt g (g' t) t)
    (fit : SourceFactorParameter Item Model K)
    (d : sourceFixedFactorPerturbations (Item := Item) (Model := Model) fixed) :
    HasFDerivAt (sourceMIRTPredictionWithin fixed g fit)
      (sourceMIRTDerivativeWithin fixed g' (fit + d.val)) d := by
  have hsub : HasFDerivAt
      (fun e : sourceFixedFactorPerturbations (Item := Item) (Model := Model) fixed => e.val)
      (sourceFixedFactorPerturbations (Item := Item) (Model := Model) fixed).subtypeL d :=
    (sourceFixedFactorPerturbations (Item := Item) (Model := Model) fixed).subtypeL.hasFDerivAt
  have harg : HasFDerivAt
      (fun e : sourceFixedFactorPerturbations (Item := Item) (Model := Model) fixed => fit + e.val)
      (sourceFixedFactorPerturbations (Item := Item) (Model := Model) fixed).subtypeL d :=
    HasFDerivAt.const_add (𝕜 := ℝ)
      (E := sourceFixedFactorPerturbations (Item := Item) (Model := Model) fixed)
      (F := SourceFactorParameter Item Model K) fit hsub
  exact HasFDerivAt.comp (𝕜 := ℝ)
    (E := sourceFixedFactorPerturbations (Item := Item) (Model := Model) fixed)
    (F := SourceFactorParameter Item Model K) (G := SourcePredictionArray Item Model) d
    (hasFDerivAt_sourceMIRTPrediction g g' hg (fit + d.val)) harg

/-- The actual affine source prediction map inherits twice continuous differentiability. -/
theorem sourceMIRTPredictionWithin_contDiff
    (fixed : Finset (Fin K)) (g : ℝ → ℝ) (hsmooth : ContDiff ℝ 2 g)
    (fit : SourceFactorParameter Item Model K) :
    ContDiff ℝ 2 (sourceMIRTPredictionWithin fixed g fit) := by
  have hsub : ContDiff ℝ 2
      (fun e : sourceFixedFactorPerturbations (Item := Item) (Model := Model) fixed => e.val) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ)
      (E := sourceFixedFactorPerturbations (Item := Item) (Model := Model) fixed)
      (F := SourceFactorParameter Item Model K) (sourceFixedFactorPerturbations fixed).subtypeL
  exact (sourcePrediction_contDiff _ (sourceMIRTLink_contDiff g hsmooth)).comp
    (contDiff_const.add hsub)

/-- Local constant rank holds for the actual affine fixed-coordinate source Fréchet derivative. -/
theorem sourceMIRTPredictionWithin_eventually_fderiv_rank_eq
    (fixed : Finset (Fin K)) (g g' : ℝ → ℝ)
    (hg : ∀ t, HasDerivAt g (g' t) t) (hpositive : ∀ t, g' t ≠ 0)
    (fit : SourceFactorParameter Item Model K) {h : ℝ} (hh : 0 < h)
    (hU : FactorGramLowerBound h (fun i k => sourceItemFactor i fit k))
    (hV : FactorGramLowerBound h (fun j k => sourceModelFactor j fit k)) :
    ∀ᶠ d in 𝓝 (0 : sourceFixedFactorPerturbations (Item := Item) (Model := Model) fixed),
      Module.finrank ℝ (fderiv ℝ (sourceMIRTPredictionWithin fixed g fit) d).range =
        Module.finrank ℝ (fderiv ℝ (sourceMIRTPredictionWithin fixed g fit) 0).range := by
  have ht : Tendsto
      (fun d : sourceFixedFactorPerturbations (Item := Item) (Model := Model) fixed => fit + d.val)
      (𝓝 0) (𝓝 fit) := by
    have harg : Continuous
        (fun d : sourceFixedFactorPerturbations (Item := Item) (Model := Model) fixed => fit + d.val) :=
      continuous_const.add continuous_subtype_val
    convert harg.tendsto 0 using 1
    simp
  filter_upwards [ht.eventually
    (sourceMIRTDerivativeWithin_eventually_rank_eq fixed g' hpositive fit hh hU hV)] with d hd
  rw [(hasFDerivAt_sourceMIRTPredictionWithin fixed g g' hg fit d).fderiv,
    (hasFDerivAt_sourceMIRTPredictionWithin fixed g g' hg fit 0).fderiv]
  have hzero : fit +
      ((0 : sourceFixedFactorPerturbations (Item := Item) (Model := Model) fixed) :
        SourceFactorParameter Item Model K) = fit := by simp
  rw [hzero]
  exact hd

/-- MIRT identification is proved on the actual Euclidean affine fixed-coordinate domain. -/
theorem source_mirt_localIdentificationWithin_of_gramLowerBounds
    (fixed : Finset (Fin K)) (g : ℝ → ℝ)
    (hsmooth : ContDiff ℝ 2 g) (hpositive : ∀ t, 0 < deriv g t)
    (fit : SourceFactorParameter Item Model K) {m h : ℝ} (hm : 0 < m) (hh : 0 < h)
    (hweight : ∀ i j, m ≤ deriv g ⟪sourceItemFactor i fit, sourceModelFactor j fit⟫)
    (hU : FactorGramLowerBound h (fun i k => sourceItemFactor i fit k))
    (hV : FactorGramLowerBound h (fun j k => sourceModelFactor j fit k)) :
    HasLocalIdentificationAt (sourceMIRTPredictionWithin fixed g fit) 0 (m ^ 2) h := by
  have hg : ∀ t, HasDerivAt g (deriv g t) t :=
    fun t => (hsmooth.differentiable (by norm_num) t).hasDerivAt
  refine ⟨sourceMIRTPredictionWithin_eventually_fderiv_rank_eq fixed g (deriv g) hg
    (fun t => ne_of_gt (hpositive t)) fit hh hU hV, ?_⟩
  intro d hd
  have hfd := (hasFDerivAt_sourceMIRTPredictionWithin fixed g (deriv g) hg fit 0).fderiv
  have hzero : fit +
      ((0 : sourceFixedFactorPerturbations (Item := Item) (Model := Model) fixed) :
        SourceFactorParameter Item Model K) = fit := by simp
  rw [hzero] at hfd
  rw [hfd] at hd ⊢
  exact sourceMIRTDerivativeWithin_sq_lower_bound fixed (deriv g) fit d hm.le hweight hU hV hd

/-- Lemma 8's actual fitted-minimum coefficient also identifies every fixed-coordinate affine model. -/
theorem source_lemma8_mirt_identificationWithin [Nonempty Item] [Nonempty Model]
    (fixed : Finset (Fin K)) (g : ℝ → ℝ)
    (hsmooth : ContDiff ℝ 2 g) (hpositive : ∀ t, 0 < deriv g t)
    (fit : SourceFactorParameter Item Model K) {h : ℝ} (hh : 0 < h)
    (hU : FactorGramLowerBound h (fun i k => sourceItemFactor i fit k))
    (hV : FactorGramLowerBound h (fun j k => sourceModelFactor j fit k)) :
    ∃ m > 0,
      (∃ i j, m = deriv g ⟪sourceItemFactor i fit, sourceModelFactor j fit⟫) ∧
      (∀ i j, m ≤ deriv g ⟪sourceItemFactor i fit, sourceModelFactor j fit⟫) ∧
      HasLocalIdentificationAt (sourceMIRTPredictionWithin fixed g fit) 0 (m ^ 2) h := by
  obtain ⟨m, hm, hattain, hlower⟩ :=
    exists_positive_fitted_linkDerivative_minimum (deriv g) hpositive fit
  exact ⟨m, hm, hattain, hlower,
    source_mirt_localIdentificationWithin_of_gramLowerBounds fixed g hsmooth hpositive fit
      hm hh hlower hU hV⟩

end

end JGR26SubjectivityMonoculture
