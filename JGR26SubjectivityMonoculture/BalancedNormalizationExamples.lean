import JGR26SubjectivityMonoculture.BalancedSourceBridge

/-!
# Finite counterexamples for bilinear normalization

The minimum-Gram objective can have unbalanced maximizers. Fixing one model
factor coordinate also changes its feasible maximum: for the two-dimensional
identity matrix, fixing the last model coordinate to one makes the maximum
`1/2`, while its last positive singular value is `1`.
-/

namespace JGR26SubjectivityMonoculture

open Module Function
open scoped BigOperators RealInnerProductSpace

noncomputable section

/-- A two-dimensional diagonal matrix. -/
def twoDiagonal (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![a, b]

/-- The source array associated with two finite factor matrices. -/
def twoSourceFactors (U V : Matrix (Fin 2) (Fin 2) ℝ) :
    SourceFactorParameter (Fin 2) (Fin 2) 2 := sourceFactorArrayEquiv.symm (U, V)

@[simp] theorem twoSourceFactors_item (U V : Matrix (Fin 2) (Fin 2) ℝ) (i k : Fin 2) :
    sourceItemFactor i (twoSourceFactors U V) k = U i k := rfl

@[simp] theorem twoSourceFactors_model (U V : Matrix (Fin 2) (Fin 2) ℝ) (j k : Fin 2) :
    sourceModelFactor j (twoSourceFactors U V) k = V j k := rfl

/-- Source factor assembly has exactly the specified bilinear product. -/
theorem twoSourceFactors_product (U V : Matrix (Fin 2) (Fin 2) ℝ) :
    sourceBilinearMatrix (twoSourceFactors U V) = U * V.transpose := by
  ext i j
  simp only [sourceBilinearMatrix_apply, twoSourceFactors_item, twoSourceFactors_model,
    finiteDot, Matrix.mul_apply, Matrix.transpose_apply]

/-- `diag(2,1)` has a unit Gram lower bound. -/
theorem twoDiagonal_two_one_gramLowerBound : FactorGramLowerBound 1 (twoDiagonal 2 1) := by
  intro x
  norm_num [finiteSqNorm, finiteDot, Fin.sum_univ_two, twoDiagonal, Matrix.diagonal_apply]
  nlinarith [sq_nonneg (x 0)]

/-- A source Gram lower bound for `diag(2,1)` is at most one. -/
theorem twoDiagonal_two_one_gramLowerBound_le_one {h : ℝ}
    (hh : FactorGramLowerBound h (twoDiagonal 2 1)) : h ≤ 1 := by
  have hx := hh ![0, 1]
  norm_num [finiteSqNorm, finiteDot, Fin.sum_univ_two, twoDiagonal, Matrix.diagonal_apply] at hx
  exact hx

/-- The identity matrix has a unit Gram lower bound. -/
theorem twoIdentity_gramLowerBound : FactorGramLowerBound 1 (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  intro x
  simp [finiteSqNorm, finiteDot, Fin.sum_univ_two, Matrix.one_apply]

/-- A source Gram lower bound for the identity is at most one. -/
theorem twoIdentity_gramLowerBound_le_one {h : ℝ}
    (hh : FactorGramLowerBound h (1 : Matrix (Fin 2) (Fin 2) ℝ)) : h ≤ 1 := by
  have hx := hh ![0, 1]
  norm_num [finiteSqNorm, finiteDot, Fin.sum_univ_two, Matrix.one_apply] at hx
  exact hx

/-- The smallest actual Gram eigenvalue of `diag(2,1)` is one. -/
theorem twoDiagonal_two_one_smallestGramEigenvalue :
    sourceFactorSmallestGramEigenvalue (twoDiagonal 2 1) (by decide) = 1 := by
  apply le_antisymm
  · exact twoDiagonal_two_one_gramLowerBound_le_one
      ((sourceFactorGramLowerBound_iff_le_smallestEigenvalue _ (by decide) _).mpr le_rfl)
  · exact (sourceFactorGramLowerBound_iff_le_smallestEigenvalue _ (by decide) _).mp
      twoDiagonal_two_one_gramLowerBound

/-- The smallest actual Gram eigenvalue of the identity is one. -/
theorem twoIdentity_smallestGramEigenvalue :
    sourceFactorSmallestGramEigenvalue (1 : Matrix (Fin 2) (Fin 2) ℝ) (by decide) = 1 := by
  apply le_antisymm
  · exact twoIdentity_gramLowerBound_le_one
      ((sourceFactorGramLowerBound_iff_le_smallestEigenvalue _ (by decide) _).mpr le_rfl)
  · exact (sourceFactorGramLowerBound_iff_le_smallestEigenvalue _ (by decide) _).mp
      twoIdentity_gramLowerBound

/-- The actual last singular value is the square root of the actual least Gram eigenvalue. -/
theorem twoMatrix_lastSingularValue_eq_sqrt_smallestGramEigenvalue
    (U : Matrix (Fin 2) (Fin 2) ℝ) :
    (matrixEuclideanOperatorEquiv U).toLinearMap.singularValues 1 =
      Real.sqrt (sourceFactorSmallestGramEigenvalue U (by decide)) := by
  have hs := (matrixEuclideanOperatorEquiv U).toLinearMap.singularValues_of_lt
    finrank_euclideanSpace_fin (by decide : 1 < 2)
  have he := sourceFactorSmallestGramEigenvalue_eq_operator U (by decide)
  exact hs.trans (congrArg Real.sqrt he.symm)

/-- The last positive singular value of `diag(2,1)` is one. -/
theorem twoDiagonal_two_one_lastSingularValue :
    (matrixEuclideanOperatorEquiv (twoDiagonal 2 1)).toLinearMap.singularValues 1 = 1 := by
  rw [twoMatrix_lastSingularValue_eq_sqrt_smallestGramEigenvalue (twoDiagonal 2 1),
    twoDiagonal_two_one_smallestGramEigenvalue]
  norm_num

/-- The last positive singular value of the two-dimensional identity is one. -/
theorem twoIdentity_lastSingularValue :
    (matrixEuclideanOperatorEquiv (1 : Matrix (Fin 2) (Fin 2) ℝ)).toLinearMap.singularValues 1 = 1 := by
  rw [twoMatrix_lastSingularValue_eq_sqrt_smallestGramEigenvalue (1 : Matrix (Fin 2) (Fin 2) ℝ),
    twoIdentity_smallestGramEigenvalue]
  norm_num

/-- The `diag(2,1)`/identity source representation. -/
def unbalancedDiagonalFit : SourceFactorParameter (Fin 2) (Fin 2) 2 :=
  twoSourceFactors (twoDiagonal 2 1) 1

/-- This representation has exact source heterogeneity one. -/
theorem unbalancedDiagonalFit_heterogeneity :
    sourceHeterogeneity (by decide) unbalancedDiagonalFit = 1 := by
  apply le_antisymm
  · have hV := (sourceHeterogeneity_lowerBounds (by decide) unbalancedDiagonalFit).2
    apply twoIdentity_gramLowerBound_le_one
    simpa only [unbalancedDiagonalFit, twoSourceFactors_model] using hV
  · apply (sourceHeterogeneity_lowerBound_iff (by decide) unbalancedDiagonalFit 1).mpr
    simpa only [unbalancedDiagonalFit, twoSourceFactors_item, twoSourceFactors_model] using
      And.intro twoDiagonal_two_one_gramLowerBound twoIdentity_gramLowerBound

/-- Its two actual covariance matrices are unequal. -/
theorem unbalancedDiagonalFit_not_balanced :
    sourceFactorGramMatrix (fun i k => sourceItemFactor i unbalancedDiagonalFit k) ≠
      sourceFactorGramMatrix (fun j k => sourceModelFactor j unbalancedDiagonalFit k) := by
  intro h
  simp only [unbalancedDiagonalFit, twoSourceFactors_item, twoSourceFactors_model] at h
  have hx := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
  norm_num [sourceFactorGramMatrix_apply, twoDiagonal,
    Fin.sum_univ_two, Matrix.diagonal_apply, Matrix.one_apply] at hx

/-- A genuine unrestricted heterogeneity maximizer can be unbalanced. -/
theorem unbalancedDiagonalFit_is_maximizer :
    sourceBilinearMatrix unbalancedDiagonalFit = twoDiagonal 2 1 ∧
      sourceHeterogeneity (by decide) unbalancedDiagonalFit = 1 ∧
      (∀ z : SourceFactorParameter (Fin 2) (Fin 2) 2,
        sourceBilinearMatrix z = twoDiagonal 2 1 →
          sourceHeterogeneity (by decide) z ≤ sourceHeterogeneity (by decide) unbalancedDiagonalFit) ∧
      sourceFactorGramMatrix (fun i k => sourceItemFactor i unbalancedDiagonalFit k) ≠
        sourceFactorGramMatrix (fun j k => sourceModelFactor j unbalancedDiagonalFit k) := by
  refine ⟨?_, unbalancedDiagonalFit_heterogeneity, ?_, unbalancedDiagonalFit_not_balanced⟩
  · simp [unbalancedDiagonalFit, twoSourceFactors_product]
  · intro z hprod
    have hΘ : 0 < finrank ℝ (matrixEuclideanOperatorEquiv (twoDiagonal 2 1)).toLinearMap.range := by
      have hs := twoDiagonal_two_one_lastSingularValue
      have hp : 0 < (matrixEuclideanOperatorEquiv (twoDiagonal 2 1)).toLinearMap.singularValues 1 := by
        linarith
      exact lt_trans (by decide : 0 < 1)
        ((matrixEuclideanOperatorEquiv (twoDiagonal 2 1)).toLinearMap.singularValues_pos_iff_lt_finrank_range.mp hp)
    obtain ⟨hU, hV⟩ := sourceHeterogeneity_lowerBounds (by decide) z
    have hbound := sourceFactorization_gramLowerBound_le_singularValue
      (twoDiagonal 2 1) z hΘ hprod (sourceHeterogeneity (by decide) z) hU hV
    have hrank : finrank ℝ (matrixEuclideanOperatorEquiv (twoDiagonal 2 1)).toLinearMap.range = 2 := by
      apply le_antisymm
      · exact (matrixEuclideanOperatorEquiv (twoDiagonal 2 1)).toLinearMap.finrank_range_le.trans finrank_euclideanSpace_fin.le
      · have hs := twoDiagonal_two_one_lastSingularValue
        have hp : 0 < (matrixEuclideanOperatorEquiv (twoDiagonal 2 1)).toLinearMap.singularValues 1 := by
          linarith
        exact (matrixEuclideanOperatorEquiv (twoDiagonal 2 1)).toLinearMap.singularValues_pos_iff_lt_finrank_range.mp hp
    simpa only [hrank, Nat.reduceSub, twoDiagonal_two_one_lastSingularValue,
      unbalancedDiagonalFit_heterogeneity] using hbound


/-- The unbalanced maximizing representation has full column rank. -/
theorem unbalancedDiagonalFit_fullRank :
    FullRankOperatorFactors (sourceFactorOperatorEquiv unbalancedDiagonalFit) := by
  obtain ⟨hU, hV⟩ := sourceHeterogeneity_lowerBounds (by decide) unbalancedDiagonalFit
  exact sourceFactorOperator_fullRank_of_gramLowerBounds unbalancedDiagonalFit
    (by rw [unbalancedDiagonalFit_heterogeneity]; norm_num) hU hV

/-- The balanced square-root diagonal representation of the same fitted matrix. -/
def balancedDiagonalFit : SourceFactorParameter (Fin 2) (Fin 2) 2 :=
  twoSourceFactors (twoDiagonal (Real.sqrt 2) 1) (twoDiagonal (Real.sqrt 2) 1)

/-- The square-root diagonal factors reconstruct `diag(2,1)`. -/
theorem balancedDiagonalFit_product : sourceBilinearMatrix balancedDiagonalFit = twoDiagonal 2 1 := by
  rw [balancedDiagonalFit, twoSourceFactors_product]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two,
      twoDiagonal, Matrix.diagonal_apply]

/-- The balanced square-root diagonal factor has a unit Gram lower bound. -/
theorem balancedDiagonalMatrix_gramLowerBound :
    FactorGramLowerBound 1 (twoDiagonal (Real.sqrt 2) 1) := by
  intro x
  have hsq : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  norm_num [finiteSqNorm, finiteDot, Fin.sum_univ_two, twoDiagonal, Matrix.diagonal_apply]
  rw [mul_pow, hsq]
  nlinarith [sq_nonneg (x 0)]

/-- The balanced and unbalanced representations attain the same maximum. -/
theorem balancedDiagonalFit_heterogeneity :
    sourceHeterogeneity (by decide) balancedDiagonalFit = 1 := by
  apply le_antisymm
  · have hmax := unbalancedDiagonalFit_is_maximizer.2.2.1
      balancedDiagonalFit balancedDiagonalFit_product
    simpa only [unbalancedDiagonalFit_heterogeneity] using hmax
  · apply (sourceHeterogeneity_lowerBound_iff (by decide) balancedDiagonalFit 1).mpr
    simpa only [balancedDiagonalFit, twoSourceFactors_item, twoSourceFactors_model] using
      And.intro balancedDiagonalMatrix_gramLowerBound balancedDiagonalMatrix_gramLowerBound

/-- The two actual covariance matrices of the square-root representation are equal. -/
theorem balancedDiagonalFit_balanced :
    sourceFactorGramMatrix (fun i k => sourceItemFactor i balancedDiagonalFit k) =
      sourceFactorGramMatrix (fun j k => sourceModelFactor j balancedDiagonalFit k) := by
  simp only [balancedDiagonalFit, twoSourceFactors_item, twoSourceFactors_model]

/-- For every exact identity factorization with the last model coordinate fixed to one,
any item Gram lower bound is at most `1/2`. -/
theorem fixedLastModelCoordinate_identity_gramLowerBound_le_half
    (z : SourceFactorParameter (Fin 2) (Fin 2) 2)
    (hfixed : ∀ j : Fin 2, sourceModelFactor j z 1 = 1)
    (hprod : sourceBilinearMatrix z = (1 : Matrix (Fin 2) (Fin 2) ℝ))
    {h : ℝ} (hU : FactorGramLowerBound h (fun i k => sourceItemFactor i z k)) :
    h ≤ (1 / 2 : ℝ) := by
  let x : Fin 2 → ℝ := fun k => sourceModelFactor 0 z k + sourceModelFactor 1 z k
  have hdx : ∀ i : Fin 2, finiteDot (fun k => sourceItemFactor i z k) x = 1 := by
    intro i
    calc
      finiteDot (fun k => sourceItemFactor i z k) x =
          sourceBilinearMatrix z i 0 + sourceBilinearMatrix z i 1 := by
        simp only [x, sourceBilinearMatrix_apply, finiteDot, Fin.sum_univ_two]
        ring
      _ = 1 := by
        rw [hprod]
        fin_cases i <;> norm_num [Matrix.one_apply]
  have hx1 : x 1 = 2 := by
    dsimp only [x]
    rw [hfixed 0, hfixed 1]
    norm_num
  have hnorm : 4 ≤ finiteSqNorm x := by
    rw [finiteSqNorm, Fin.sum_univ_two, hx1]
    nlinarith [sq_nonneg (x 0)]
  have hb := hU x
  norm_num only [hdx, Fin.sum_univ_two, one_pow] at hb
  by_cases hh : h ≤ 0
  · linarith
  · have hmul := mul_le_mul_of_nonneg_left hnorm (le_of_lt (lt_of_not_ge hh))
    nlinarith

/-- The fixed last coordinate changes the source heterogeneity's entire feasible maximum. -/
theorem fixedLastModelCoordinate_identity_heterogeneity_le_half
    (z : SourceFactorParameter (Fin 2) (Fin 2) 2)
    (hfixed : ∀ j : Fin 2, sourceModelFactor j z 1 = 1)
    (hprod : sourceBilinearMatrix z = (1 : Matrix (Fin 2) (Fin 2) ℝ)) :
    sourceHeterogeneity (by decide) z ≤ (1 / 2 : ℝ) :=
  fixedLastModelCoordinate_identity_gramLowerBound_le_half z hfixed hprod
    (sourceHeterogeneity_lowerBounds (by decide) z).1

/-- Fixed-coordinate model rows `(1,1)` and `(-1,1)`. -/
def fixedCoordinateIdentityModelMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; -1, 1]

/-- The corresponding item matrix is one half of the model matrix. -/
def fixedCoordinateIdentityItemMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(1 / 2 : ℝ), (1 / 2 : ℝ); (-1 / 2 : ℝ), (1 / 2 : ℝ)]

/-- An exact identity fit attaining the constrained maximum. -/
def fixedCoordinateIdentityFit : SourceFactorParameter (Fin 2) (Fin 2) 2 :=
  twoSourceFactors fixedCoordinateIdentityItemMatrix fixedCoordinateIdentityModelMatrix

/-- The fixed-coordinate witness reconstructs the identity. -/
theorem fixedCoordinateIdentityFit_product :
    sourceBilinearMatrix fixedCoordinateIdentityFit = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [fixedCoordinateIdentityFit, twoSourceFactors_product]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two,
      fixedCoordinateIdentityItemMatrix, fixedCoordinateIdentityModelMatrix, Matrix.one_apply]

/-- Both model rows have last coordinate one. -/
theorem fixedCoordinateIdentityFit_fixed :
    ∀ j : Fin 2, sourceModelFactor j fixedCoordinateIdentityFit 1 = 1 := by
  intro j
  simp only [fixedCoordinateIdentityFit, twoSourceFactors_model]
  fin_cases j <;> norm_num [fixedCoordinateIdentityModelMatrix]

/-- The item witness has Gram matrix `I/2`, hence a half-unit lower bound. -/
theorem fixedCoordinateIdentityItemMatrix_gramLowerBound :
    FactorGramLowerBound (1 / 2 : ℝ) fixedCoordinateIdentityItemMatrix := by
  intro x
  norm_num [finiteSqNorm, finiteDot, Fin.sum_univ_two, fixedCoordinateIdentityItemMatrix]
  nlinarith

/-- The model witness has Gram matrix `2I`, hence also a half-unit lower bound. -/
theorem fixedCoordinateIdentityModelMatrix_gramLowerBound :
    FactorGramLowerBound (1 / 2 : ℝ) fixedCoordinateIdentityModelMatrix := by
  intro x
  norm_num [finiteSqNorm, finiteDot, Fin.sum_univ_two, fixedCoordinateIdentityModelMatrix]
  nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]

/-- The actual source heterogeneity of this constrained fit is `1/2`. -/
theorem fixedCoordinateIdentityFit_heterogeneity :
    sourceHeterogeneity (by decide) fixedCoordinateIdentityFit = (1 / 2 : ℝ) := by
  apply le_antisymm
  · exact fixedLastModelCoordinate_identity_heterogeneity_le_half fixedCoordinateIdentityFit
      fixedCoordinateIdentityFit_fixed fixedCoordinateIdentityFit_product
  · apply (sourceHeterogeneity_lowerBound_iff (by decide) fixedCoordinateIdentityFit _).mpr
    simpa only [fixedCoordinateIdentityFit, twoSourceFactors_item, twoSourceFactors_model] using
      And.intro fixedCoordinateIdentityItemMatrix_gramLowerBound
        fixedCoordinateIdentityModelMatrix_gramLowerBound

/-- The constrained maximum is `1/2` while the fitted matrix's last singular value is `1`. -/
theorem fixedLastModelCoordinate_identity_maximum :
    sourceBilinearMatrix fixedCoordinateIdentityFit = (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
      (∀ j : Fin 2, sourceModelFactor j fixedCoordinateIdentityFit 1 = 1) ∧
      sourceHeterogeneity (by decide) fixedCoordinateIdentityFit = (1 / 2 : ℝ) ∧
      (∀ z : SourceFactorParameter (Fin 2) (Fin 2) 2,
        (∀ j : Fin 2, sourceModelFactor j z 1 = 1) →
        sourceBilinearMatrix z = (1 : Matrix (Fin 2) (Fin 2) ℝ) →
        sourceHeterogeneity (by decide) z ≤ sourceHeterogeneity (by decide) fixedCoordinateIdentityFit) ∧
      (matrixEuclideanOperatorEquiv (1 : Matrix (Fin 2) (Fin 2) ℝ)).toLinearMap.singularValues 1 = 1 := by
  refine ⟨fixedCoordinateIdentityFit_product, fixedCoordinateIdentityFit_fixed,
    fixedCoordinateIdentityFit_heterogeneity, ?_, twoIdentity_lastSingularValue⟩
  intro z hfixed hprod
  rw [fixedCoordinateIdentityFit_heterogeneity]
  exact fixedLastModelCoordinate_identity_heterogeneity_le_half z hfixed hprod

/-- The constrained maximizing identity fit has full column rank. -/
theorem fixedCoordinateIdentityFit_fullRank :
    FullRankOperatorFactors (sourceFactorOperatorEquiv fixedCoordinateIdentityFit) := by
  obtain ⟨hU, hV⟩ := sourceHeterogeneity_lowerBounds (by decide) fixedCoordinateIdentityFit
  exact sourceFactorOperator_fullRank_of_gramLowerBounds fixedCoordinateIdentityFit
    (by rw [fixedCoordinateIdentityFit_heterogeneity]; norm_num) hU hV

end
end JGR26SubjectivityMonoculture
