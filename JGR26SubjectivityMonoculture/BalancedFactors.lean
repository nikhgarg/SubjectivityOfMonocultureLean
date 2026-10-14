import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic

/-!
# Unrestricted bilinear factors and Gram bounds

This module uses Mathlib's actual adjoints, eigenvalues and singular values.
The source's `r`-th singular value is `singularValues (r - 1)` because Mathlib
uses zero-based indices. The factors here are free linear maps: no coordinate
is held fixed as an intercept. Balanced factors are not claimed to be the only
maximizers of the minimum-Gram objective.

## Foundation provenance

The imported foundational APIs are the repository's existing Mathlib dependency,
Lean/Mathlib `v4.30.0-rc2`, commit
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`, released under Apache 2.0:

* `Mathlib.Analysis.InnerProductSpace.SingularValues`, by Niels Voss and Arnav
  Mehta: <https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/InnerProductSpace/SingularValues.lean>.
* `Mathlib.Analysis.InnerProductSpace.Spectrum`, for the orthonormal spectral
  basis: <https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/InnerProductSpace/Spectrum.lean>.
* `Mathlib.Analysis.Matrix.Order` and the continuous-functional-calculus
  positive-square uniqueness theorem, used only to prove balanced-class
  uniqueness: <https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/Matrix/Order.lean>
  and <https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean>.

No external SVD implementation has been copied or added as an axiom.
-/

open scoped BigOperators RealInnerProductSpace
open Module

namespace JGR26SubjectivityMonoculture

noncomputable section

section GramBounds

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]

/-- Spectral expansion of a symmetric quadratic form in its orthonormal eigenbasis. -/
theorem symmetric_quadraticForm_eq_sum
    (A : E →ₗ[ℝ] E) (hA : A.IsSymmetric) {n : ℕ}
    (hn : finrank ℝ E = n) (x : E) :
    ⟪A x, x⟫ = ∑ i : Fin n,
      hA.eigenvalues hn i * ((hA.eigenvectorBasis hn).repr x i) ^ 2 := by
  rw [← (hA.eigenvectorBasis hn).sum_inner_mul_inner (A x) x]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [← real_inner_comm (A x) (hA.eigenvectorBasis hn i),
    ← OrthonormalBasis.repr_apply_apply,
    ← OrthonormalBasis.repr_apply_apply,
    hA.eigenvectorBasis_apply_self_apply hn]
  change hA.eigenvalues hn i * _ * _ = _
  ring

/-- The last, hence smallest, eigenvalue is a lower Rayleigh bound. -/
theorem smallestEigenvalue_quadraticForm_lowerBound
    (A : E →ₗ[ℝ] E) (hA : A.IsSymmetric) {n : ℕ}
    (hn : finrank ℝ E = n + 1) (x : E) :
    hA.eigenvalues hn (Fin.last n) * ‖x‖ ^ 2 ≤ ⟪A x, x⟫ := by
  rw [symmetric_quadraticForm_eq_sum A hA hn x]
  have hnorm : ∑ i : Fin (n + 1),
      ((hA.eigenvectorBasis hn).repr x i) ^ 2 = ‖x‖ ^ 2 := by
    simpa only [OrthonormalBasis.repr_apply_apply, Real.norm_eq_abs, sq_abs]
      using (hA.eigenvectorBasis hn).sum_sq_norm_inner_right x
  rw [← hnorm, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _hi => mul_le_mul_of_nonneg_right
    (hA.eigenvalues_antitone hn (Fin.le_last i)) (sq_nonneg _)

/-- A universal Rayleigh lower bound cannot exceed the smallest eigenvalue. -/
theorem le_smallestEigenvalue_of_quadraticForm_lowerBound
    (A : E →ₗ[ℝ] E) (hA : A.IsSymmetric) {n : ℕ}
    (hn : finrank ℝ E = n + 1) {h : ℝ}
    (hbound : ∀ x : E, h * ‖x‖ ^ 2 ≤ ⟪A x, x⟫) :
    h ≤ hA.eigenvalues hn (Fin.last n) := by
  have hb := hbound (hA.eigenvectorBasis hn (Fin.last n))
  simpa only [hA.apply_eigenvectorBasis, inner_smul_left,
    RCLike.conj_to_real, real_inner_self_eq_norm_sq,
    (hA.eigenvectorBasis hn).orthonormal.norm_eq_one,
    one_pow, mul_one] using hb

/-- Minimum eigenvalue and the minimum-Rayleigh description of a factor Gram agree. -/
theorem gram_lowerBound_iff_le_smallestEigenvalue
    (U : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n + 1) (h : ℝ) :
    (∀ x : E, h * ‖x‖ ^ 2 ≤ ‖U x‖ ^ 2) ↔
      h ≤ U.isSymmetric_adjoint_comp_self.eigenvalues hn (Fin.last n) := by
  have hgram : ∀ x : E, ⟪(U.adjoint ∘ₗ U) x, x⟫ = ‖U x‖ ^ 2 := by
    intro x
    simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_left,
      real_inner_self_eq_norm_sq]
  constructor
  · intro hb
    apply le_smallestEigenvalue_of_quadraticForm_lowerBound
      (U.adjoint ∘ₗ U) U.isSymmetric_adjoint_comp_self hn
    simpa only [hgram] using hb
  · intro hle x
    exact (mul_le_mul_of_nonneg_right hle (sq_nonneg ‖x‖)).trans
      (by simpa only [hgram] using (smallestEigenvalue_quadraticForm_lowerBound
        (U.adjoint ∘ₗ U) U.isSymmetric_adjoint_comp_self hn x))

/-- A Gram lower bound transfers to the adjoint on the factor's range. -/
theorem gram_lowerBound_adjoint_on_range
    (V : E →ₗ[ℝ] G) {h : ℝ} (hh : 0 ≤ h)
    (hV : ∀ x : E, h * ‖x‖ ^ 2 ≤ ‖V x‖ ^ 2)
    {y : G} (hy : y ∈ V.range) : h * ‖y‖ ^ 2 ≤ ‖V.adjoint y‖ ^ 2 := by
  obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
  by_cases hz : V x = 0
  · simp only [hz, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero,
      map_zero, le_refl]
  have hp : 0 < ‖V x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
  have hc := real_inner_mul_inner_self_le (V.adjoint (V x)) x
  rw [V.adjoint_inner_left, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hc
  have hc' := mul_le_mul_of_nonneg_left hc hh
  have hv' := mul_le_mul_of_nonneg_left (hV x) (sq_nonneg ‖V.adjoint (V x)‖)
  nlinarith

/--
Every positive singular value of `U V†` bounds any common factor-Gram lower
bound. In particular, choosing the last positive singular value gives the
unrestricted normalization's upper bound. No balancing hypothesis is used.
-/
theorem common_gram_lowerBound_le_singularValue
    (U : E →ₗ[ℝ] F) (V : E →ₗ[ℝ] G) {h : ℝ}
    (hU : ∀ x : E, h * ‖x‖ ^ 2 ≤ ‖U x‖ ^ 2)
    (hV : ∀ x : E, h * ‖x‖ ^ 2 ≤ ‖V x‖ ^ 2)
    {k : ℕ} (hk : k < finrank ℝ (U ∘ₗ V.adjoint).range) :
    h ≤ (U ∘ₗ V.adjoint).singularValues k := by
  let T := U ∘ₗ V.adjoint
  by_cases hh : h ≤ 0
  · exact hh.trans (T.singularValues_nonneg k)
  have hhpos : 0 < h := lt_of_not_ge hh
  have hkdim : k < finrank ℝ G := hk.trans_le T.finrank_range_le
  let i : Fin (finrank ℝ G) := ⟨k, hkdim⟩
  let y := T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl i
  have hnorm : ‖y‖ = 1 :=
    (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl).orthonormal.norm_eq_one i
  have hs : 0 < T.singularValues k := T.singularValues_pos_iff_lt_finrank_range.mpr hk
  have heig : (T.adjoint ∘ₗ T) y = (T.singularValues k ^ 2) • y := by
    rw [T.sq_singularValues_fin rfl i]
    exact T.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis rfl i
  have hy : y ∈ V.range := by
    have hm : (T.adjoint ∘ₗ T) y ∈ V.range := by
      change T.adjoint (T y) ∈ V.range
      dsimp [T]
      rw [LinearMap.adjoint_comp, LinearMap.adjoint_adjoint]
      exact LinearMap.mem_range.mpr ⟨U.adjoint (U (V.adjoint y)), rfl⟩
    rw [heig] at hm
    have hm' := V.range.smul_mem ((T.singularValues k ^ 2)⁻¹) hm
    simpa only [smul_smul, inv_mul_cancel₀ (ne_of_gt (sq_pos_of_pos hs)), one_smul]
      using hm'
  have hadj := gram_lowerBound_adjoint_on_range V (le_of_lt hhpos) hV hy
  have hu := hU (V.adjoint y)
  have ht : ‖T y‖ ^ 2 = T.singularValues k ^ 2 := by
    have htinner : ‖T y‖ ^ 2 = ⟪(T.adjoint ∘ₗ T) y, y⟫ := by
      simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_left,
        real_inner_self_eq_norm_sq]
    rw [htinner, heig]
    simp only [inner_smul_left, RCLike.conj_to_real, real_inner_self_eq_norm_sq,
      hnorm, one_pow, mul_one]
  have hu' : h * ‖V.adjoint y‖ ^ 2 ≤ T.singularValues k ^ 2 := by
    simpa only [← ht] using hu
  simp only [hnorm, one_pow, mul_one] at hadj
  have hsnonneg := T.singularValues_nonneg k
  nlinarith

end GramBounds

section SpectralConstruction

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A linear synthesis map whose columns are weighted members of a vector family. -/
def weightedSynthesis (w : ι → E) (a : ι → ℝ) : EuclideanSpace ℝ ι →ₗ[ℝ] E where
  toFun x := ∑ i : ι, (a i * x i) • w i
  map_add' x y := by
    simp only [PiLp.add_apply, mul_add, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    change (∑ i : ι, (a i * (c * x i)) • w i) = c • ∑ i : ι, (a i * x i) • w i
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    rw [smul_smul]
    congr 1
    ring

omit [FiniteDimensional ℝ E] in
@[simp]
theorem weightedSynthesis_single (w : ι → E) (a : ι → ℝ) (i : ι) :
    weightedSynthesis w a (EuclideanSpace.single i 1) = a i • w i := by
  classical
  simp [weightedSynthesis, PiLp.single_apply]

theorem weightedSynthesis_adjoint_apply (w : ι → E) (a : ι → ℝ) (y : E) (i : ι) :
    ((weightedSynthesis w a).adjoint y) i = a i * ⟪w i, y⟫ := by
  have h := (weightedSynthesis w a).adjoint_inner_right (EuclideanSpace.single i 1) y
  simpa +instances only [PiLp.inner_apply, RCLike.toInnerProductSpaceReal,
    Inner.rclikeToReal, RCLike.inner_apply, RCLike.conj_to_real, RCLike.re_to_real,
    PiLp.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, weightedSynthesis_single, inner_smul_left] using h

theorem weightedSynthesis_gram_apply (w : ι → E) (hw : Orthonormal ℝ w)
    (a : ι → ℝ) (x : EuclideanSpace ℝ ι) (i : ι) :
    ((weightedSynthesis w a).adjoint (weightedSynthesis w a x)) i = a i ^ 2 * x i := by
  rw [weightedSynthesis_adjoint_apply]
  change a i * ⟪w i, ∑ j : ι, (a j * x j) • w j⟫ = _
  rw [hw.inner_right_fintype]
  ring

theorem weightedSynthesis_norm_sq (w : ι → E) (hw : Orthonormal ℝ w)
    (a : ι → ℝ) (x : EuclideanSpace ℝ ι) :
    ‖weightedSynthesis w a x‖ ^ 2 = ∑ i : ι, a i ^ 2 * (x i) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← (weightedSynthesis w a).adjoint_inner_right,
    PiLp.inner_apply]
  simp_rw [weightedSynthesis_gram_apply w hw]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  simp +instances only [RCLike.toInnerProductSpaceReal, Inner.rclikeToReal,
    RCLike.inner_apply, RCLike.conj_to_real, RCLike.re_to_real]
  ring

variable {F G : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]

/-- Positive-mode right singular vectors, constructed from the actual Gram eigenbasis. -/
def rightSingularVector (T : G →ₗ[ℝ] F) (i : Fin (finrank ℝ T.range)) : G :=
  T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl
    (Fin.castLE T.finrank_range_le i)

/-- Positive-mode left singular vectors, obtained by normalizing the image of the right ones. -/
def leftSingularVector (T : G →ₗ[ℝ] F) (i : Fin (finrank ℝ T.range)) : F :=
  (T.singularValues i)⁻¹ • T (rightSingularVector T i)

theorem rightSingularVector_orthonormal (T : G →ₗ[ℝ] F) :
    Orthonormal ℝ (rightSingularVector T) := by
  apply (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl).orthonormal.comp
    (Fin.castLE T.finrank_range_le)
  intro i j hij
  exact Fin.ext (congrArg (fun k : Fin (finrank ℝ G) => k.val) hij)

theorem gram_apply_rightSingularVector (T : G →ₗ[ℝ] F)
    (i : Fin (finrank ℝ T.range)) :
    (T.adjoint ∘ₗ T) (rightSingularVector T i) =
      T.singularValues i ^ 2 • rightSingularVector T i := by
  have hs := T.sq_singularValues_fin rfl (Fin.castLE T.finrank_range_le i)
  change T.singularValues i ^ 2 = _ at hs
  rw [hs]
  exact T.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis rfl _

theorem inner_image_rightSingularVector (T : G →ₗ[ℝ] F)
    (i j : Fin (finrank ℝ T.range)) :
    ⟪T (rightSingularVector T i), T (rightSingularVector T j)⟫ =
      T.singularValues j ^ 2 * ⟪rightSingularVector T i, rightSingularVector T j⟫ := by
  rw [← T.adjoint_inner_right]
  change ⟪rightSingularVector T i, (T.adjoint ∘ₗ T) (rightSingularVector T j)⟫ = _
  rw [gram_apply_rightSingularVector, inner_smul_right]

theorem leftSingularVector_orthonormal (T : G →ₗ[ℝ] F) :
    Orthonormal ℝ (leftSingularVector T) := by
  apply orthonormal_iff_ite.mpr
  intro i j
  simp only [leftSingularVector, inner_smul_left, inner_smul_right,
    RCLike.conj_to_real, inner_image_rightSingularVector,
    orthonormal_iff_ite.mp (rightSingularVector_orthonormal T)]
  by_cases hij : i = j
  · subst j
    have hs : T.singularValues i ≠ 0 := ne_of_gt
      (T.singularValues_pos_iff_lt_finrank_range.mpr i.isLt)
    field_simp
  · simp only [if_neg hij, mul_zero]

/-- Balanced right factor: each right singular vector receives weight `sqrt σ`. -/
def balancedRightFactor (T : G →ₗ[ℝ] F) : EuclideanSpace ℝ (Fin (finrank ℝ T.range)) →ₗ[ℝ] G :=
  weightedSynthesis (rightSingularVector T) (fun i => Real.sqrt (T.singularValues i))

/-- Balanced left factor: each normalized left singular vector receives the same weight. -/
def balancedLeftFactor (T : G →ₗ[ℝ] F) : EuclideanSpace ℝ (Fin (finrank ℝ T.range)) →ₗ[ℝ] F :=
  weightedSynthesis (leftSingularVector T) (fun i => Real.sqrt (T.singularValues i))

theorem balancedRightFactor_gram_apply (T : G →ₗ[ℝ] F)
    (x : EuclideanSpace ℝ (Fin (finrank ℝ T.range))) (i : Fin (finrank ℝ T.range)) :
    ((balancedRightFactor T).adjoint (balancedRightFactor T x)) i = T.singularValues i * x i := by
  rw [balancedRightFactor, weightedSynthesis_gram_apply _ (rightSingularVector_orthonormal T)]
  rw [Real.sq_sqrt (T.singularValues_nonneg i)]

theorem balancedLeftFactor_gram_apply (T : G →ₗ[ℝ] F)
    (x : EuclideanSpace ℝ (Fin (finrank ℝ T.range))) (i : Fin (finrank ℝ T.range)) :
    ((balancedLeftFactor T).adjoint (balancedLeftFactor T x)) i = T.singularValues i * x i := by
  rw [balancedLeftFactor, weightedSynthesis_gram_apply _ (leftSingularVector_orthonormal T)]
  rw [Real.sq_sqrt (T.singularValues_nonneg i)]

/-- The constructed factors have identical Gram operators, not merely identical spectra. -/
theorem balancedFactors_gram_eq (T : G →ₗ[ℝ] F) :
    (balancedLeftFactor T).adjoint ∘ₗ balancedLeftFactor T =
      (balancedRightFactor T).adjoint ∘ₗ balancedRightFactor T := by
  ext x i
  exact (balancedLeftFactor_gram_apply T x i).trans
    (balancedRightFactor_gram_apply T x i).symm

/-- Truncating a finite sum drops only modes whose contributions are zero. -/
theorem sum_fin_truncate {M : Type*} [AddCommMonoid M] {r n : ℕ}
    (hr : r ≤ n) (f : Fin n → M) (hz : ∀ i : Fin n, r ≤ i.val → f i = 0) :
    (∑ i : Fin n, f i) = ∑ i : Fin r, f (Fin.castLE hr i) := by
  symm
  apply Fintype.sum_of_injective (Fin.castLE hr)
    (fun i j hij => Fin.ext (congrArg (fun k : Fin n => k.val) hij))
    (fun i => f (Fin.castLE hr i)) f
  · intro i hi
    apply hz i
    by_contra h
    have hlt : i.val < r := lt_of_not_ge h
    exact hi ⟨⟨i.val, hlt⟩, rfl⟩
  · intro i
    rfl

theorem image_rightSingularVector (T : G →ₗ[ℝ] F) (i : Fin (finrank ℝ T.range)) :
    T (rightSingularVector T i) = T.singularValues i • leftSingularVector T i := by
  have hs : T.singularValues i ≠ 0 := ne_of_gt
    (T.singularValues_pos_iff_lt_finrank_range.mpr i.isLt)
  simp only [leftSingularVector, smul_smul, mul_inv_cancel₀ hs, one_smul]

/-- The Gram eigenbasis modes after the rank lie in the kernel of the original map. -/
theorem image_eigenvectorBasis_eq_zero_of_rank_le (T : G →ₗ[ℝ] F)
    (i : Fin (finrank ℝ G)) (hi : finrank ℝ T.range ≤ i.val) :
    T (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl i) = 0 := by
  let b := T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl
  have hs : T.singularValues i = 0 := T.singularValues_eq_zero_iff_le_finrank_range.mpr hi
  have heigenzero : T.isSymmetric_adjoint_comp_self.eigenvalues rfl i = 0 := by
    rw [← T.sq_singularValues_fin rfl i, hs]
    norm_num
  have hg : (T.adjoint ∘ₗ T) (b i) = 0 := by
    simpa only [heigenzero, RCLike.ofReal_zero, zero_smul] using
      (T.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis rfl i)
  have hnorm : ‖T (b i)‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq, ← T.adjoint_inner_right]
    change ⟪b i, (T.adjoint ∘ₗ T) (b i)⟫ = 0
    rw [hg, inner_zero_right]
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)

/-- Actual rank-truncated singular-value reconstruction, derived from the spectral theorem. -/
theorem singularValue_reconstruction (T : G →ₗ[ℝ] F) (y : G) :
    T y = ∑ i : Fin (finrank ℝ T.range),
      (T.singularValues i * ⟪rightSingularVector T i, y⟫) • leftSingularVector T i := by
  let b := T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl
  calc
    T y = ∑ i : Fin (finrank ℝ G), ⟪b i, y⟫ • T (b i) := by
      nth_rw 1 [← b.sum_repr' y]
      rw [map_sum]
      simp only [map_smul]
    _ = ∑ i : Fin (finrank ℝ T.range),
        ⟪rightSingularVector T i, y⟫ • T (rightSingularVector T i) := by
      apply sum_fin_truncate T.finrank_range_le
      intro i hi
      rw [image_eigenvectorBasis_eq_zero_of_rank_le T i hi, smul_zero]
    _ = _ := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      rw [image_rightSingularVector, smul_smul, mul_comm]

/-- The explicit balanced factors reproduce the original operator exactly. -/
theorem balancedFactors_product_eq (T : G →ₗ[ℝ] F) :
    balancedLeftFactor T ∘ₗ (balancedRightFactor T).adjoint = T := by
  apply LinearMap.ext
  intro y
  change weightedSynthesis (leftSingularVector T) (fun i => Real.sqrt (T.singularValues i))
    ((balancedRightFactor T).adjoint y) = T y
  rw [singularValue_reconstruction T y]
  change (∑ i : Fin (finrank ℝ T.range),
    (Real.sqrt (T.singularValues i) * ((balancedRightFactor T).adjoint y) i) •
      leftSingularVector T i) = _
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [balancedRightFactor, weightedSynthesis_adjoint_apply]
  congr 1
  rw [← mul_assoc, Real.mul_self_sqrt (T.singularValues_nonneg i)]

theorem balancedRightFactor_norm_sq (T : G →ₗ[ℝ] F)
    (x : EuclideanSpace ℝ (Fin (finrank ℝ T.range))) :
    ‖balancedRightFactor T x‖ ^ 2 = ∑ i : Fin (finrank ℝ T.range),
      T.singularValues i * (x i) ^ 2 := by
  rw [balancedRightFactor, weightedSynthesis_norm_sq _ (rightSingularVector_orthonormal T)]
  simp_rw [Real.sq_sqrt (T.singularValues_nonneg _)]

theorem balancedLeftFactor_norm_sq (T : G →ₗ[ℝ] F)
    (x : EuclideanSpace ℝ (Fin (finrank ℝ T.range))) :
    ‖balancedLeftFactor T x‖ ^ 2 = ∑ i : Fin (finrank ℝ T.range),
      T.singularValues i * (x i) ^ 2 := by
  rw [balancedLeftFactor, weightedSynthesis_norm_sq _ (leftSingularVector_orthonormal T)]
  simp_rw [Real.sq_sqrt (T.singularValues_nonneg _)]

/-- Both constructed Gram forms are bounded below by the last positive singular value. -/
theorem balancedFactors_common_gram_lowerBound (T : G →ₗ[ℝ] F)
    (x : EuclideanSpace ℝ (Fin (finrank ℝ T.range))) :
    T.singularValues (finrank ℝ T.range - 1) * ‖x‖ ^ 2 ≤ ‖balancedLeftFactor T x‖ ^ 2 ∧
      T.singularValues (finrank ℝ T.range - 1) * ‖x‖ ^ 2 ≤ ‖balancedRightFactor T x‖ ^ 2 := by
  have hb : T.singularValues (finrank ℝ T.range - 1) * ‖x‖ ^ 2 ≤
      ∑ i : Fin (finrank ℝ T.range), T.singularValues i * (x i) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _hi
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact T.singularValues_antitone (Nat.le_sub_one_of_lt i.isLt)
  constructor
  · simpa only [balancedLeftFactor_norm_sq] using hb
  · simpa only [balancedRightFactor_norm_sq] using hb

end SpectralConstruction

section Attainment

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- A strictly positive Gram lower bound implies full column rank. -/
theorem injective_of_positive_gram_lowerBound (U : E →ₗ[ℝ] F)
    {h : ℝ} (hh : 0 < h) (hU : ∀ x : E, h * ‖x‖ ^ 2 ≤ ‖U x‖ ^ 2) :
    Function.Injective U := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  have hb := hU x
  rw [hx, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hb
  have hz : ‖x‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖x‖]
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)

/-- The spectral balanced construction supplies full-rank factors, not a degenerate witness. -/
theorem balancedFactors_injective (T : G →ₗ[ℝ] F) (hrank : 0 < finrank ℝ T.range) :
    Function.Injective (balancedLeftFactor T) ∧ Function.Injective (balancedRightFactor T) := by
  have hs : 0 < T.singularValues (finrank ℝ T.range - 1) :=
    T.singularValues_pos_iff_lt_finrank_range.mpr (Nat.sub_one_lt_of_lt hrank)
  constructor
  · apply injective_of_positive_gram_lowerBound (balancedLeftFactor T) hs
    intro x
    exact (balancedFactors_common_gram_lowerBound T x).1
  · apply injective_of_positive_gram_lowerBound (balancedRightFactor T) hs
    intro x
    exact (balancedFactors_common_gram_lowerBound T x).2

/-- Each constructed factor has smallest Gram eigenvalue exactly the last positive singular value. -/
theorem balancedFactors_smallestGramEigenvalue (T : G →ₗ[ℝ] F) {n : ℕ}
    (hn : finrank ℝ T.range = n + 1) :
    (balancedLeftFactor T).isSymmetric_adjoint_comp_self.eigenvalues
        (finrank_euclideanSpace_fin.trans hn) (Fin.last n) = T.singularValues n ∧
      (balancedRightFactor T).isSymmetric_adjoint_comp_self.eigenvalues
        (finrank_euclideanSpace_fin.trans hn) (Fin.last n) = T.singularValues n := by
  let hd : finrank ℝ (EuclideanSpace ℝ (Fin (finrank ℝ T.range))) = n + 1 :=
    finrank_euclideanSpace_fin.trans hn
  have hsL : ∀ x : EuclideanSpace ℝ (Fin (finrank ℝ T.range)),
      T.singularValues n * ‖x‖ ^ 2 ≤ ‖balancedLeftFactor T x‖ ^ 2 := by
    intro x
    simpa only [hn, Nat.add_sub_cancel] using (balancedFactors_common_gram_lowerBound T x).1
  have hsR : ∀ x : EuclideanSpace ℝ (Fin (finrank ℝ T.range)),
      T.singularValues n * ‖x‖ ^ 2 ≤ ‖balancedRightFactor T x‖ ^ 2 := by
    intro x
    simpa only [hn, Nat.add_sub_cancel] using (balancedFactors_common_gram_lowerBound T x).2
  have heq : ∀ x : EuclideanSpace ℝ (Fin (finrank ℝ T.range)),
      ‖balancedLeftFactor T x‖ ^ 2 = ‖balancedRightFactor T x‖ ^ 2 := by
    intro x
    rw [balancedLeftFactor_norm_sq, balancedRightFactor_norm_sq]
  have hk : n < finrank ℝ
      (balancedLeftFactor T ∘ₗ (balancedRightFactor T).adjoint).range := by
    rw [balancedFactors_product_eq, hn]
    exact Nat.lt_succ_self n
  have hleft := (gram_lowerBound_iff_le_smallestEigenvalue
    (balancedLeftFactor T) hd _).mpr (le_refl _)
  have hright := (gram_lowerBound_iff_le_smallestEigenvalue
    (balancedRightFactor T) hd _).mpr (le_refl _)
  constructor
  · apply le_antisymm
    · have hu := common_gram_lowerBound_le_singularValue
        (balancedLeftFactor T) (balancedRightFactor T) hleft
        (by simpa only [heq] using hleft) hk
      simpa only [balancedFactors_product_eq] using hu
    · exact (gram_lowerBound_iff_le_smallestEigenvalue (balancedLeftFactor T) hd _).mp hsL
  · apply le_antisymm
    · have hu := common_gram_lowerBound_le_singularValue
        (balancedLeftFactor T) (balancedRightFactor T)
        (by simpa only [heq] using hright) hright hk
      simpa only [balancedFactors_product_eq] using hu
    · exact (gram_lowerBound_iff_le_smallestEigenvalue (balancedRightFactor T) hd _).mp hsR

/--
For a positive-rank bilinear matrix, the explicit balanced factors attain the
largest possible common minimum-Rayleigh Gram bound. Together with
`gram_lowerBound_iff_le_smallestEigenvalue`, this is the unrestricted max-value
claim `max min(λmin(U†U), λmin(V†V)) = σ_r(T)`.
-/
theorem balancedFactors_attain_optimal_common_gram_bound
    (T : G →ₗ[ℝ] F) (hrank : 0 < finrank ℝ T.range) :
    balancedLeftFactor T ∘ₗ (balancedRightFactor T).adjoint = T ∧
      (balancedLeftFactor T).adjoint ∘ₗ balancedLeftFactor T =
        (balancedRightFactor T).adjoint ∘ₗ balancedRightFactor T ∧
      (∀ x : EuclideanSpace ℝ (Fin (finrank ℝ T.range)),
        T.singularValues (finrank ℝ T.range - 1) * ‖x‖ ^ 2 ≤ ‖balancedLeftFactor T x‖ ^ 2 ∧
          T.singularValues (finrank ℝ T.range - 1) * ‖x‖ ^ 2 ≤ ‖balancedRightFactor T x‖ ^ 2) ∧
      (∀ (U : E →ₗ[ℝ] F) (V : E →ₗ[ℝ] G) (h : ℝ), U ∘ₗ V.adjoint = T →
        (∀ x : E, h * ‖x‖ ^ 2 ≤ ‖U x‖ ^ 2) →
        (∀ x : E, h * ‖x‖ ^ 2 ≤ ‖V x‖ ^ 2) →
        h ≤ T.singularValues (finrank ℝ T.range - 1)) := by
  refine ⟨balancedFactors_product_eq T, balancedFactors_gram_eq T,
    balancedFactors_common_gram_lowerBound T, ?_⟩
  intro U V h hprod hU hV
  have hk : finrank ℝ T.range - 1 < finrank ℝ (U ∘ₗ V.adjoint).range := by
    rw [hprod]
    exact Nat.sub_one_lt_of_lt hrank
  simpa only [hprod] using common_gram_lowerBound_le_singularValue U V hU hV hk

/--
The unrestricted bilinear max-value statement, directly in the source's
minimum-eigenvalue objective. Both factors have `rank(T)` latent coordinates.
The first equality exhibits attainment; the universal inequality proves
optimality over all exact factorizations in that same latent dimension.
-/
theorem unrestricted_bilinear_heterogeneity_maximum (T : G →ₗ[ℝ] F) {n : ℕ}
    (hn : finrank ℝ T.range = n + 1) :
    min
      ((balancedLeftFactor T).isSymmetric_adjoint_comp_self.eigenvalues
        (finrank_euclideanSpace_fin.trans hn) (Fin.last n))
      ((balancedRightFactor T).isSymmetric_adjoint_comp_self.eigenvalues
        (finrank_euclideanSpace_fin.trans hn) (Fin.last n)) = T.singularValues n ∧
    ∀ (U : EuclideanSpace ℝ (Fin (finrank ℝ T.range)) →ₗ[ℝ] F)
      (V : EuclideanSpace ℝ (Fin (finrank ℝ T.range)) →ₗ[ℝ] G),
      U ∘ₗ V.adjoint = T →
      min
        (U.isSymmetric_adjoint_comp_self.eigenvalues
          (finrank_euclideanSpace_fin.trans hn) (Fin.last n))
        (V.isSymmetric_adjoint_comp_self.eigenvalues
          (finrank_euclideanSpace_fin.trans hn) (Fin.last n)) ≤ T.singularValues n := by
  constructor
  · obtain ⟨hL, hR⟩ := balancedFactors_smallestGramEigenvalue T hn
    rw [hL, hR, min_self]
  · intro U V hprod
    let h := min
      (U.isSymmetric_adjoint_comp_self.eigenvalues
        (finrank_euclideanSpace_fin.trans hn) (Fin.last n))
      (V.isSymmetric_adjoint_comp_self.eigenvalues
        (finrank_euclideanSpace_fin.trans hn) (Fin.last n))
    have hU := (gram_lowerBound_iff_le_smallestEigenvalue U
      (finrank_euclideanSpace_fin.trans hn) h).mpr (min_le_left _ _)
    have hV := (gram_lowerBound_iff_le_smallestEigenvalue V
      (finrank_euclideanSpace_fin.trans hn) h).mpr (min_le_right _ _)
    have hk : n < finrank ℝ (U ∘ₗ V.adjoint).range := by
      rw [hprod, hn]
      exact Nat.lt_succ_self n
    simpa only [hprod] using common_gram_lowerBound_le_singularValue U V hU hV hk

end Attainment

section BalancedUniqueness

open scoped MatrixOrder

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]

/-- Positive finite-dimensional real operators have unique positive square roots. -/
theorem positive_comp_self_injective (A B : E →ₗ[ℝ] E)
    (hA : A.IsPositive) (hB : B.IsPositive) (hsq : A ∘ₗ A = B ∘ₗ B) : A = B := by
  let b := stdOrthonormalBasis ℝ E
  have hm : A.toMatrix b.toBasis b.toBasis * A.toMatrix b.toBasis b.toBasis =
      B.toMatrix b.toBasis b.toBasis * B.toMatrix b.toBasis b.toBasis := by
    rw [← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp, hsq]
  have hpA : 0 ≤ A.toMatrix b.toBasis b.toBasis :=
    (LinearMap.posSemidef_toMatrix_iff b).mpr hA |>.nonneg
  have hpB : 0 ≤ B.toMatrix b.toBasis b.toBasis :=
    (LinearMap.posSemidef_toMatrix_iff b).mpr hB |>.nonneg
  apply (LinearMap.toMatrix b.toBasis b.toBasis).injective
  exact (CFC.mul_self_eq_mul_self_iff _ _ hpA hpB).mp hm

/-- In balanced coordinates, `U U†` is a positive square root of `T T†`. -/
theorem balanced_outerGram_square (U : E →ₗ[ℝ] F) (V : E →ₗ[ℝ] G)
    (hbal : U.adjoint ∘ₗ U = V.adjoint ∘ₗ V) :
    (U ∘ₗ U.adjoint) ∘ₗ (U ∘ₗ U.adjoint) =
      (U ∘ₗ V.adjoint) ∘ₗ (U ∘ₗ V.adjoint).adjoint := by
  rw [LinearMap.adjoint_comp, LinearMap.adjoint_adjoint]
  ext y
  exact congrArg U (congrArg (fun A : E →ₗ[ℝ] E => A (U.adjoint y)) hbal)

/-- Balanced factors of one operator have the same outer Gram operator. -/
theorem balanced_sameProduct_outerGram_eq
    (U U' : E →ₗ[ℝ] F) (V V' : E →ₗ[ℝ] G)
    (hbal : U.adjoint ∘ₗ U = V.adjoint ∘ₗ V)
    (hbal' : U'.adjoint ∘ₗ U' = V'.adjoint ∘ₗ V')
    (hprod : U ∘ₗ V.adjoint = U' ∘ₗ V'.adjoint) :
    U ∘ₗ U.adjoint = U' ∘ₗ U'.adjoint := by
  apply positive_comp_self_injective _ _
    U.isPositive_self_comp_adjoint U'.isPositive_self_comp_adjoint
  rw [balanced_outerGram_square U V hbal, balanced_outerGram_square U' V' hbal', hprod]

/-- Full column rank makes the adjoint onto the latent space. -/
theorem adjoint_surjective_of_injective (U : E →ₗ[ℝ] F) (hU : Function.Injective U) :
    Function.Surjective U.adjoint := by
  rw [← LinearMap.range_eq_top, ← U.orthogonal_ker, LinearMap.ker_eq_bot.mpr hU]
  simp

omit [FiniteDimensional ℝ F] in
/-- Two full-column-rank factors have the same product rank as their latent dimension. -/
theorem factorProduct_rank_of_injective (U : E →ₗ[ℝ] F) (V : E →ₗ[ℝ] G)
    (hU : Function.Injective U) (hV : Function.Injective V) :
    finrank ℝ (U ∘ₗ V.adjoint).range = finrank ℝ E := by
  rw [LinearMap.range_comp_of_range_eq_top U
    (LinearMap.range_eq_top.mpr (adjoint_surjective_of_injective V hV))]
  exact LinearMap.finrank_range_of_inj hU

/--
Balanced full-rank representations of the same bilinear operator are unique
up to one common real linear isometry (an orthogonal latent rotation). This is
uniqueness within the balanced class, not a claim that every maximizer of the
minimum-Gram objective is balanced.
-/
theorem balancedFactors_unique_up_to_rotation
    (U U' : E →ₗ[ℝ] F) (V V' : E →ₗ[ℝ] G)
    (hU : Function.Injective U) (hU' : Function.Injective U')
    (hV : Function.Injective V) (hV' : Function.Injective V')
    (hbal : U.adjoint ∘ₗ U = V.adjoint ∘ₗ V)
    (hbal' : U'.adjoint ∘ₗ U' = V'.adjoint ∘ₗ V')
    (hprod : U ∘ₗ V.adjoint = U' ∘ₗ V'.adjoint) :
    ∃ R : E ≃ₗᵢ[ℝ] E, (∀ x : E, U' (R x) = U x) ∧ (∀ x : E, V' (R x) = V x) := by
  have hrange : U.range = U'.range := by
    calc
      U.range = (U ∘ₗ V.adjoint).range := (LinearMap.range_comp_of_range_eq_top U
        (LinearMap.range_eq_top.mpr (adjoint_surjective_of_injective V hV))).symm
      _ = (U' ∘ₗ V'.adjoint).range := congrArg LinearMap.range hprod
      _ = U'.range := LinearMap.range_comp_of_range_eq_top U'
        (LinearMap.range_eq_top.mpr (adjoint_surjective_of_injective V' hV'))
  let q : E ≃ₗ[ℝ] E := (LinearEquiv.ofInjective U hU).trans
    ((LinearEquiv.ofEq U.range U'.range hrange).trans (LinearEquiv.ofInjective U' hU').symm)
  have hq : ∀ x : E, U' (q x) = U x := by
    intro x
    dsimp only [q, LinearEquiv.trans_apply]
    rw [LinearEquiv.ofInjective_symm_apply]
    rfl
  have hqmap : U' ∘ₗ q.toLinearMap = U := LinearMap.ext hq
  have hqadj : U.adjoint = q.toLinearMap.adjoint ∘ₗ U'.adjoint := by
    rw [← hqmap, LinearMap.adjoint_comp]
  have hout := balanced_sameProduct_outerGram_eq U U' V V' hbal hbal' hprod
  have hqid : ∀ x : E, q (q.toLinearMap.adjoint x) = x := by
    intro x
    obtain ⟨y, rfl⟩ := adjoint_surjective_of_injective U' hU' x
    apply hU'
    have houty := congrArg (fun A : F →ₗ[ℝ] F => A y) hout
    simpa only [LinearMap.comp_apply, hqadj, hq] using houty
  have hqadjid : ∀ x : E, q.toLinearMap.adjoint (q x) = x := by
    intro x
    apply q.injective
    exact hqid (q x)
  have hqinner : ∀ x y : E, ⟪q x, q y⟫ = ⟪x, y⟫ := by
    intro x y
    change ⟪q.toLinearMap x, q y⟫ = ⟪x, y⟫
    rw [← q.toLinearMap.adjoint_inner_right]
    rw [hqadjid]
  refine ⟨q.isometryOfInner hqinner, hq, ?_⟩
  have hqVadj : ∀ y : G, q (V.adjoint y) = V'.adjoint y := by
    intro y
    apply hU'
    rw [hq]
    exact congrArg (fun A : G →ₗ[ℝ] F => A y) hprod
  intro x
  apply ext_inner_right ℝ
  intro y
  change ⟪V' (q x), y⟫ = ⟪V x, y⟫
  rw [← V'.adjoint_inner_right, ← hqVadj, hqinner, V.adjoint_inner_right]

end BalancedUniqueness

end

end JGR26SubjectivityMonoculture
