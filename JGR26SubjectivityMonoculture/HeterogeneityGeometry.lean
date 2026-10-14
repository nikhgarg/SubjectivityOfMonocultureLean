import JGR26SubjectivityMonoculture.MainTheorems

/-!
# Transverse identification for bilinear latent factors

Orthogonality to the infinitesimal reparametrizations
`(B U, -Bᵀ V)` forces equality of two perturbation moment matrices.
Consequently the cross term in the squared prediction derivative is a sum of
squares, and the two factor Gram lower bounds control every transverse
perturbation. This is the linearized bound in the IRT/MIRT lemma.
-/

namespace JGR26SubjectivityMonoculture

open scoped BigOperators

noncomputable section

variable {K : ℕ} {Item Model : Type*} [Fintype Item] [Fintype Model]

/-- Item perturbation moment `Σᵢ ΔUᵢ Uᵢᵀ`. -/
def itemPerturbationMoment (U dU : Item → Fin K → ℝ) (a b : Fin K) : ℝ :=
  ∑ i, dU i a * U i b

/-- Model perturbation moment `Σⱼ Vⱼ ΔVⱼᵀ`. -/
def modelPerturbationMoment (V dV : Model → Fin K → ℝ) (a b : Fin K) : ℝ :=
  ∑ j, V j a * dV j b

/-- Orthogonality to every infinitesimal invertible bilinear reparametrization. -/
def IsOrthogonalToBilinearGauge
    (U : Item → Fin K → ℝ) (V : Model → Fin K → ℝ)
    (dU : Item → Fin K → ℝ) (dV : Model → Fin K → ℝ) : Prop :=
  ∀ B : Fin K → Fin K → ℝ,
    (∑ i, finiteDot (dU i) (fun a => ∑ b, B a b * U i b)) =
      ∑ j, finiteDot (dV j) (fun b => ∑ a, B a b * V j a)

/-- Item component of an infinitesimal bilinear reparametrization. -/
def bilinearGaugeItem (U : Item → Fin K → ℝ) (B : Fin K → Fin K → ℝ)
    (i : Item) (a : Fin K) : ℝ := ∑ b, B a b * U i b

/-- Model component of the same infinitesimal reparametrization. -/
def bilinearGaugeModel (V : Model → Fin K → ℝ) (B : Fin K → Fin K → ℝ)
    (j : Model) (b : Fin K) : ℝ := -(∑ a, B a b * V j a)

omit [Fintype Item] [Fintype Model] in
/-- Every gauge direction lies in the kernel of the actual bilinear derivative. -/
theorem bilinearGauge_predictionDerivative_eq_zero
    (U : Item → Fin K → ℝ) (V : Model → Fin K → ℝ)
    (B : Fin K → Fin K → ℝ) (i : Item) (j : Model) :
    finiteDot (V j) (bilinearGaugeItem U B i) +
      finiteDot (U i) (bilinearGaugeModel V B j) = 0 := by
  have hswap :
      (∑ a, V j a * ∑ b, B a b * U i b) =
        ∑ b, U i b * ∑ a, B a b * V j a := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro a _
    ring
  simpa [finiteDot, bilinearGaugeItem, bilinearGaugeModel,
    Finset.sum_neg_distrib, hswap] using sub_self
    (∑ b, U i b * ∑ a, B a b * V j a)

/-- Euclidean orthogonality to the kernel of the link-weighted prediction derivative. -/
def IsMIRTKernelOrthogonal
    (U : Item → Fin K → ℝ) (V : Model → Fin K → ℝ)
    (weight : Item → Model → ℝ)
    (dU : Item → Fin K → ℝ) (dV : Model → Fin K → ℝ) : Prop :=
  ∀ (eU : Item → Fin K → ℝ) (eV : Model → Fin K → ℝ),
    (∀ i j, weight i j * (finiteDot (V j) (eU i) +
      finiteDot (U i) (eV j)) = 0) →
    (∑ i, finiteDot (dU i) (eU i)) + ∑ j, finiteDot (dV j) (eV j) = 0

/-- Orthogonality to the actual derivative kernel supplies gauge orthogonality. -/
theorem orthogonalToBilinearGauge_of_mirtKernelOrthogonal
    (U : Item → Fin K → ℝ) (V : Model → Fin K → ℝ)
    (weight : Item → Model → ℝ)
    (dU : Item → Fin K → ℝ) (dV : Model → Fin K → ℝ)
    (horth : IsMIRTKernelOrthogonal U V weight dU dV) :
    IsOrthogonalToBilinearGauge U V dU dV := by
  intro B
  have h := horth (bilinearGaugeItem U B) (bilinearGaugeModel V B)
    (fun i j => by rw [bilinearGauge_predictionDerivative_eq_zero, mul_zero])
  simp only [finiteDot, bilinearGaugeItem, bilinearGaugeModel,
    mul_neg, Finset.sum_neg_distrib] at h ⊢
  linarith

/-- Testing each elementary reparametrization identifies the two moment matrices. -/
theorem perturbationMoments_eq_of_orthogonalToBilinearGauge
    (U : Item → Fin K → ℝ) (V : Model → Fin K → ℝ)
    (dU : Item → Fin K → ℝ) (dV : Model → Fin K → ℝ)
    (horth : IsOrthogonalToBilinearGauge U V dU dV) (a b : Fin K) :
    itemPerturbationMoment U dU a b = modelPerturbationMoment V dV a b := by
  classical
  have h := horth (fun x y => if x = a then if y = b then 1 else 0 else 0)
  simpa [finiteDot, itemPerturbationMoment, modelPerturbationMoment,
    mul_ite, mul_comm] using h

/-- The bilinear cross term is the Frobenius inner product of the moments. -/
theorem bilinearLinearizedCrossTerm_eq_moment_inner
    (U : Item → Fin K → ℝ) (V : Model → Fin K → ℝ)
    (dU : Item → Fin K → ℝ) (dV : Model → Fin K → ℝ) :
    bilinearLinearizedCrossTerm U V dU dV =
      ∑ a, ∑ b, itemPerturbationMoment U dU a b *
        modelPerturbationMoment V dV a b := by
  classical
  unfold bilinearLinearizedCrossTerm finiteDot
  calc
    (∑ i, ∑ j, (∑ a, V j a * dU i a) * (∑ b, U i b * dV j b)) =
        ∑ i, ∑ j, ∑ a, ∑ b, (dU i a * U i b) * (V j a * dV j b) := by
      simp only [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = ∑ i, ∑ a, ∑ j, ∑ b, (dU i a * U i b) * (V j a * dV j b) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ j, ∑ b, (dU i a * U i b) * (V j a * dV j b) :=
      Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ b, ∑ j, (dU i a * U i b) * (V j a * dV j b) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ i, ∑ j, (dU i a * U i b) * (V j a * dV j b) := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = ∑ a, ∑ b, itemPerturbationMoment U dU a b *
        modelPerturbationMoment V dV a b := by
      simp only [itemPerturbationMoment, modelPerturbationMoment, Finset.sum_mul_sum]

/-- A transverse perturbation has nonnegative aggregate cross term. -/
theorem bilinearLinearizedCrossTerm_nonneg_of_orthogonalToBilinearGauge
    (U : Item → Fin K → ℝ) (V : Model → Fin K → ℝ)
    (dU : Item → Fin K → ℝ) (dV : Model → Fin K → ℝ)
    (horth : IsOrthogonalToBilinearGauge U V dU dV) :
    0 ≤ bilinearLinearizedCrossTerm U V dU dV := by
  rw [bilinearLinearizedCrossTerm_eq_moment_inner]
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro b _
  rw [perturbationMoments_eq_of_orthogonalToBilinearGauge U V dU dV horth]
  exact mul_self_nonneg _

/-- The Gram heterogeneity controls all perturbations normal to the gauge orbit. -/
theorem bilinearLinearizedSq_lower_bound_of_orthogonalToBilinearGauge
    (U : Item → Fin K → ℝ) (V : Model → Fin K → ℝ)
    (dU : Item → Fin K → ℝ) (dV : Model → Fin K → ℝ) {h : ℝ}
    (hU : FactorGramLowerBound h U) (hV : FactorGramLowerBound h V)
    (horth : IsOrthogonalToBilinearGauge U V dU dV) :
    h * heterogeneityParameterSq dU dV ≤ bilinearLinearizedSq U V dU dV := by
  have hblock := blockLinearSq_lower_bound_of_factorGrams U V dU dV hU hV
  have hcross := bilinearLinearizedCrossTerm_nonneg_of_orthogonalToBilinearGauge
    U V dU dV horth
  rw [bilinearLinearizedSq_eq_blocks_add_cross]
  linarith

/-- A positive lower bound on link weights controls the total weighted square. -/
theorem sum_weighted_sq_ge_of_weight_lower_bound
    (weight signal : Item → Model → ℝ) {m : ℝ} (hm : 0 ≤ m)
    (hweight : ∀ i j, m ≤ weight i j) :
    m ^ 2 * (∑ i, ∑ j, (signal i j) ^ 2) ≤
      ∑ i, ∑ j, (weight i j * signal i j) ^ 2 := by
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have hsquare : m ^ 2 ≤ weight i j ^ 2 := by
    nlinarith [hweight i j]
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right hsquare (sq_nonneg (signal i j))

/-- The link derivative supplies the stated `m² h` transverse identification bound. -/
theorem mirtLinearizedSq_lower_bound_of_orthogonalToBilinearGauge
    (U : Item → Fin K → ℝ) (V : Model → Fin K → ℝ)
    (dU : Item → Fin K → ℝ) (dV : Model → Fin K → ℝ)
    (weight : Item → Model → ℝ) {m h : ℝ} (hm : 0 ≤ m)
    (hweight : ∀ i j, m ≤ weight i j)
    (hU : FactorGramLowerBound h U) (hV : FactorGramLowerBound h V)
    (horth : IsOrthogonalToBilinearGauge U V dU dV) :
    m ^ 2 * h * heterogeneityParameterSq dU dV ≤
      ∑ i, ∑ j, (weight i j *
        (finiteDot (V j) (dU i) + finiteDot (U i) (dV j))) ^ 2 := by
  have hbase := bilinearLinearizedSq_lower_bound_of_orthogonalToBilinearGauge
    U V dU dV hU hV horth
  calc
    m ^ 2 * h * heterogeneityParameterSq dU dV =
        m ^ 2 * (h * heterogeneityParameterSq dU dV) := by ring
    _ ≤ m ^ 2 * bilinearLinearizedSq U V dU dV :=
      mul_le_mul_of_nonneg_left hbase (sq_nonneg m)
    _ ≤ _ := sum_weighted_sq_ge_of_weight_lower_bound weight
      (fun i j => finiteDot (V j) (dU i) + finiteDot (U i) (dV j)) hm hweight

/-- The transverse lower bound from the source's literal kernel-orthogonality premise. -/
theorem mirtLinearizedSq_lower_bound_of_kernelOrthogonal
    (U : Item → Fin K → ℝ) (V : Model → Fin K → ℝ)
    (dU : Item → Fin K → ℝ) (dV : Model → Fin K → ℝ)
    (weight : Item → Model → ℝ) {m h : ℝ} (hm : 0 ≤ m)
    (hweight : ∀ i j, m ≤ weight i j)
    (hU : FactorGramLowerBound h U) (hV : FactorGramLowerBound h V)
    (horth : IsMIRTKernelOrthogonal U V weight dU dV) :
    m ^ 2 * h * heterogeneityParameterSq dU dV ≤
      ∑ i, ∑ j, (weight i j *
        (finiteDot (V j) (dU i) + finiteDot (U i) (dV j))) ^ 2 :=
  mirtLinearizedSq_lower_bound_of_orthogonalToBilinearGauge U V dU dV weight hm
    hweight hU hV (orthogonalToBilinearGauge_of_mirtKernelOrthogonal U V weight dU dV horth)

/-- Admissible model perturbations keep every specified factor coordinate fixed. -/
def HasZeroFixedCoordinates (fixed : Finset (Fin K))
    (dV : Model → Fin K → ℝ) : Prop :=
  ∀ j k, k ∈ fixed → dV j k = 0

/-- Orthogonality to the derivative kernel within the admissible parameter space. -/
def IsMIRTKernelOrthogonalWithin (fixed : Finset (Fin K))
    (U : Item → Fin K → ℝ) (V : Model → Fin K → ℝ)
    (weight : Item → Model → ℝ)
    (dU : Item → Fin K → ℝ) (dV : Model → Fin K → ℝ) : Prop :=
  ∀ (eU : Item → Fin K → ℝ) (eV : Model → Fin K → ℝ),
    HasZeroFixedCoordinates fixed eV →
    (∀ i j, weight i j * (finiteDot (V j) (eU i) +
      finiteDot (U i) (eV j)) = 0) →
    (∑ i, finiteDot (dU i) (eU i)) + ∑ j, finiteDot (dV j) (eV j) = 0

/-- Restricted kernel orthogonality equates moments in all free columns. -/
theorem perturbationMoments_eq_of_kernelOrthogonalWithin
    (fixed : Finset (Fin K))
    (U : Item → Fin K → ℝ) (V : Model → Fin K → ℝ)
    (weight : Item → Model → ℝ)
    (dU : Item → Fin K → ℝ) (dV : Model → Fin K → ℝ)
    (horth : IsMIRTKernelOrthogonalWithin fixed U V weight dU dV)
    (a b : Fin K) (hb : b ∉ fixed) :
    itemPerturbationMoment U dU a b = modelPerturbationMoment V dV a b := by
  classical
  let B : Fin K → Fin K → ℝ :=
    fun x y => if x = a then if y = b then 1 else 0 else 0
  have hadmissible : HasZeroFixedCoordinates fixed (bilinearGaugeModel V B) := by
    intro j k hk
    have hkb : k ≠ b := by
      intro heq
      exact hb (heq ▸ hk)
    simp [bilinearGaugeModel, B, hkb]
  have h := horth (bilinearGaugeItem U B) (bilinearGaugeModel V B) hadmissible
    (fun i j => by rw [bilinearGauge_predictionDerivative_eq_zero, mul_zero])
  have hscalar : itemPerturbationMoment U dU a b -
      modelPerturbationMoment V dV a b = 0 := by
    simpa [finiteDot, bilinearGaugeItem, bilinearGaugeModel, B,
      itemPerturbationMoment, modelPerturbationMoment,
      mul_ite, mul_comm, Finset.sum_neg_distrib] using h
  exact sub_eq_zero.mp hscalar

/-- The cross term remains nonnegative when any set of model coordinates is fixed. -/
theorem bilinearLinearizedCrossTerm_nonneg_of_kernelOrthogonalWithin
    (fixed : Finset (Fin K))
    (U : Item → Fin K → ℝ) (V : Model → Fin K → ℝ)
    (weight : Item → Model → ℝ)
    (dU : Item → Fin K → ℝ) (dV : Model → Fin K → ℝ)
    (hfixed : HasZeroFixedCoordinates fixed dV)
    (horth : IsMIRTKernelOrthogonalWithin fixed U V weight dU dV) :
    0 ≤ bilinearLinearizedCrossTerm U V dU dV := by
  classical
  rw [bilinearLinearizedCrossTerm_eq_moment_inner]
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro b _
  by_cases hb : b ∈ fixed
  · have hzero : modelPerturbationMoment V dV a b = 0 := by
      simp [modelPerturbationMoment, hfixed _ _ hb]
    simp [hzero]
  · rw [perturbationMoments_eq_of_kernelOrthogonalWithin
      fixed U V weight dU dV horth a b hb]
    exact mul_self_nonneg _

/-- The source's transverse Gram bound also holds in a fixed-coordinate affine domain. -/
theorem bilinearLinearizedSq_lower_bound_of_kernelOrthogonalWithin
    (fixed : Finset (Fin K))
    (U : Item → Fin K → ℝ) (V : Model → Fin K → ℝ)
    (weight : Item → Model → ℝ)
    (dU : Item → Fin K → ℝ) (dV : Model → Fin K → ℝ) {h : ℝ}
    (hU : FactorGramLowerBound h U) (hV : FactorGramLowerBound h V)
    (hfixed : HasZeroFixedCoordinates fixed dV)
    (horth : IsMIRTKernelOrthogonalWithin fixed U V weight dU dV) :
    h * heterogeneityParameterSq dU dV ≤ bilinearLinearizedSq U V dU dV := by
  have hblock := blockLinearSq_lower_bound_of_factorGrams U V dU dV hU hV
  have hcross := bilinearLinearizedCrossTerm_nonneg_of_kernelOrthogonalWithin
    fixed U V weight dU dV hfixed horth
  rw [bilinearLinearizedSq_eq_blocks_add_cross]
  linarith

/-- Lemma 8's `m² h` bound also holds with fixed model coordinates. -/
theorem mirtLinearizedSq_lower_bound_of_kernelOrthogonalWithin
    (fixed : Finset (Fin K))
    (U : Item → Fin K → ℝ) (V : Model → Fin K → ℝ)
    (dU : Item → Fin K → ℝ) (dV : Model → Fin K → ℝ)
    (weight : Item → Model → ℝ) {m h : ℝ} (hm : 0 ≤ m)
    (hweight : ∀ i j, m ≤ weight i j)
    (hU : FactorGramLowerBound h U) (hV : FactorGramLowerBound h V)
    (hfixed : HasZeroFixedCoordinates fixed dV)
    (horth : IsMIRTKernelOrthogonalWithin fixed U V weight dU dV) :
    m ^ 2 * h * heterogeneityParameterSq dU dV ≤
      ∑ i, ∑ j, (weight i j *
        (finiteDot (V j) (dU i) + finiteDot (U i) (dV j))) ^ 2 := by
  have hbase := bilinearLinearizedSq_lower_bound_of_kernelOrthogonalWithin
    fixed U V weight dU dV hU hV hfixed horth
  calc
    m ^ 2 * h * heterogeneityParameterSq dU dV =
        m ^ 2 * (h * heterogeneityParameterSq dU dV) := by ring
    _ ≤ m ^ 2 * bilinearLinearizedSq U V dU dV :=
      mul_le_mul_of_nonneg_left hbase (sq_nonneg m)
    _ ≤ _ := sum_weighted_sq_ge_of_weight_lower_bound weight
      (fun i j => finiteDot (V j) (dU i) + finiteDot (U i) (dV j)) hm hweight

end

end JGR26SubjectivityMonoculture
