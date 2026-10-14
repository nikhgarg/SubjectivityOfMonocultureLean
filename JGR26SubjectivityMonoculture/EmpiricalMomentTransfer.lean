import JGR26SubjectivityMonoculture.EmpiricalResiduals
import JGR26SubjectivityMonoculture.ResidualDiscrepancyBridge

/-!
# Conditional empirical residual-moment transfer

Remark 1 transfers population residual moments to fitted empirical covariances
in the sample-size regime in which the moment laws of large numbers and uniform
probability consistency hold. An arbitrary filter represents that regime.
Theorem 3's raw cross-moment limit is combined with residual-mean limits proved
from the same discrepancy hypothesis and the null's actual item-row marginals.

The LLN premises concern oracle first and cross moments. Neither a population
centered-covariance limit nor an empirical covariance limit is assumed.
-/

namespace JGR26SubjectivityMonoculture

open Filter
open scoped BigOperators Topology

noncomputable section

/-- The item-averaged first residual moment, before sample centering. -/
def averageResidualMeanFunctional
    {Item Model : Type*} [Fintype Item] [Nonempty Item]
    (p : Item → Model → ℝ) (j : Model) (response : Item → Model → Bool) : ℝ :=
  ((Fintype.card Item : ℝ)⁻¹) *
    ∑ i : Item, binaryResidual (p i j) (response i j)

/-- A probability table gives a bound-one averaged first residual moment. -/
theorem averageResidualMeanFunctional_abs_le_one
    {Item Model : Type*} [Fintype Item] [Nonempty Item]
    (p : Item → Model → ℝ) (j : Model)
    (hp : ∀ i m, 0 ≤ p i m ∧ p i m ≤ 1)
    (response : Item → Model → Bool) :
    |averageResidualMeanFunctional p j response| ≤ 1 := by
  classical
  have hcard : 0 < (Fintype.card Item : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Item)
  have hinv : 0 ≤ (Fintype.card Item : ℝ)⁻¹ := inv_nonneg.mpr hcard.le
  calc
    |averageResidualMeanFunctional p j response| =
        (Fintype.card Item : ℝ)⁻¹ * |∑ i : Item, binaryResidual (p i j) (response i j)| := by
      simp [averageResidualMeanFunctional, abs_mul, abs_of_nonneg hinv]
    _ ≤ (Fintype.card Item : ℝ)⁻¹ *
        ∑ i : Item, |binaryResidual (p i j) (response i j)| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hinv
    _ ≤ (Fintype.card Item : ℝ)⁻¹ * ∑ _i : Item, (1 : ℝ) := by
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ =>
        abs_binaryResidual_le_one _ _ (hp i j).1 (hp i j).2) hinv
    _ = 1 := by simp [ne_of_gt hcard]

/-- Null marginal success probabilities make each model's residual mean zero. -/
theorem productBernoulliMass_residualMeanExpectation_zero
    {Model : Type*} [Fintype Model] [DecidableEq Model]
    (p : Model → ℝ) (hp : ∀ m, 0 ≤ p m ∧ p m ≤ 1) (j : Model) :
    (∑ r : Model → Bool, productBernoulliMass p r * binaryResidual (p j) (r j)) = 0 := by
  classical
  let μ : Model → PMF Bool := fun m => realBernoulliPMF (p m) (hp m).1 (hp m).2
  have hsum : (∑ r : Model → Bool, productBernoulliMass p r * binaryResidual (p j) (r j)) =
      AppliedModelingLib.pmfExp (AppliedModelingLib.pmfPi μ)
        (fun r => binaryResidual (p j) (r j)) := by
    unfold AppliedModelingLib.pmfExp
    exact Finset.sum_congr rfl (fun r _ => by rw [productBernoulliPMF_toReal_eq_mass p hp r])
  rw [hsum, AppliedModelingLib.pmfExp_pmfPi_eval_eq μ j (binaryResidual (p j))]
  simp [AppliedModelingLib.pmfExp, μ, binaryResidual, boolAsReal]
  ring

/-- Actual null row marginals, rather than an assumed centering identity, give zero first moments. -/
theorem averageResidualMeanExpectation_zero_of_productItemRowMarginals
    {Item Model : Type*} [Fintype Item] [Nonempty Item] [Fintype Model]
    [Fintype (Item → Model → Bool)]
    (null : FiniteLaw (Item → Model → Bool)) (p : Item → Model → ℝ) (j : Model)
    (hp : ∀ i m, 0 ≤ p i m ∧ p i m ≤ 1)
    (hrows : HasProductBernoulliItemRowMarginals null p) :
    finiteLawExpectation null (averageResidualMeanFunctional p j) = 0 := by
  classical
  have hzero : ∀ i : Item,
      finiteLawExpectation null (fun response => binaryResidual (p i j) (response i j)) = 0 := by
    intro i
    rw [finiteLawExpectation_itemRow_eq_of_productBernoulliItemRowMarginals
      null p hrows i (fun r => binaryResidual (p i j) (r j))]
    exact productBernoulliMass_residualMeanExpectation_zero (p i) (hp i) j
  have havg : finiteLawExpectation null (averageResidualMeanFunctional p j) =
      (Fintype.card Item : ℝ)⁻¹ * ∑ i : Item,
        finiteLawExpectation null (fun response => binaryResidual (p i j) (response i j)) := by
    simp only [finiteLawExpectation, averageResidualMeanFunctional, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro response _
    ring
  rw [havg]
  simp only [hzero, Finset.sum_const_zero, mul_zero]

/-- The discrepancy hypothesis of Theorem 3 also makes every population residual mean vanish. -/
theorem averageResidualMean_tendsto_zero_of_productItemRowMarginals_and_qualitative_discrepancy
    {Item Model : Type*} [Fintype Item] [Nonempty Item] [Fintype Model]
    [Fintype (Item → Model → Bool)]
    {D : FiniteLaw (Item → Model → Bool) → FiniteLaw (Item → Model → Bool) → ℝ}
    (hD : ControlsBoundedExpectationsAtZero D)
    (observed : FiniteLaw (Item → Model → Bool))
    (null : ℕ → FiniteLaw (Item → Model → Bool)) (p : ℕ → Item → Model → ℝ) (j : Model)
    (hp : ∀ K i m, 0 ≤ p K i m ∧ p K i m ≤ 1)
    (hrows : ∀ K, HasProductBernoulliItemRowMarginals (null K) (p K))
    (hlim : Tendsto (fun K => D observed (null K)) atTop (𝓝 0)) :
    Tendsto (fun K => finiteLawExpectation observed (averageResidualMeanFunctional (p K) j))
      atTop (𝓝 0) := by
  have hdiff := varyingBoundedExpectations_tendsto_zero_of_controlsBoundedExpectationsAtZero
    hD observed null (fun K => averageResidualMeanFunctional (p K) j)
    (fun K => averageResidualMeanFunctional_abs_le_one (p K) j (hp K)) hlim
  have hzero : ∀ K,
      finiteLawExpectation (null K) (averageResidualMeanFunctional (p K) j) = 0 :=
    fun K => averageResidualMeanExpectation_zero_of_productItemRowMarginals
      (null K) (p K) j (hp K) (hrows K)
  simpa only [hzero, sub_zero] using hdiff

/-- An oracle moment LLN and its population zero limit give the oracle sample zero limit. -/
theorem tendsto_zero_of_moment_lln
    {ι : Type*} {l : Filter ι} {sample population : ι → ℝ}
    (hlln : Tendsto (fun t => sample t - population t) l (𝓝 0))
    (hpopulation : Tendsto population l (𝓝 0)) :
    Tendsto sample l (𝓝 0) := by
  simpa only [sub_add_cancel, add_zero] using hlln.add hpopulation

/--
First- and cross-moment LLNs in any selected regime transfer the raw population
zero limits to fitted centered sample covariance. Uniform probability consistency
is used only through the proved finite perturbation bound `4 * error`.
-/
theorem fittedResidualCovariance_tendsto_zero_of_moment_lln
    {ι Model : Type*} {l : Filter ι}
    (sampleSize : ι → ℕ) (response : ι → ℕ → Model → Bool)
    (oracle fitted : ι → ℕ → Model → ℝ) (error : ι → ℝ) (j ℓ : Model)
    (populationCross populationMeanJ populationMeanL : ι → ℝ)
    (hn : ∀ᶠ t in l, 0 < sampleSize t)
    (hp : ∀ t i, i < sampleSize t → ∀ m, 0 ≤ oracle t i m ∧ oracle t i m ≤ 1)
    (hfitted : ∀ t i, i < sampleSize t → ∀ m, 0 ≤ fitted t i m ∧ fitted t i m ≤ 1)
    (herror : ∀ t i, i < sampleSize t → ∀ m, |fitted t i m - oracle t i m| ≤ error t)
    (hconsistent : Tendsto error l (𝓝 0))
    (hcrossLLN : Tendsto (fun t =>
      empiricalBinaryResidualCrossMoment (oracle t) (response t) j ℓ (sampleSize t) -
        populationCross t) l (𝓝 0))
    (hmeanJLLN : Tendsto (fun t =>
      empiricalBinaryResidualMean (oracle t) (response t) j (sampleSize t) -
        populationMeanJ t) l (𝓝 0))
    (hmeanLLLN : Tendsto (fun t =>
      empiricalBinaryResidualMean (oracle t) (response t) ℓ (sampleSize t) -
        populationMeanL t) l (𝓝 0))
    (hcross : Tendsto populationCross l (𝓝 0))
    (hmeanJ : Tendsto populationMeanJ l (𝓝 0))
    (hmeanL : Tendsto populationMeanL l (𝓝 0)) :
    Tendsto (fun t => empiricalBinaryResidualCovariance
      (fitted t) (response t) j ℓ (sampleSize t)) l (𝓝 0) := by
  have horacle : Tendsto (fun t => empiricalBinaryResidualCovariance
      (oracle t) (response t) j ℓ (sampleSize t)) l (𝓝 0) := by
    simpa only [empiricalBinaryResidualCovariance, mul_zero, sub_zero] using
      (tendsto_zero_of_moment_lln hcrossLLN hcross).sub
        ((tendsto_zero_of_moment_lln hmeanJLLN hmeanJ).mul
          (tendsto_zero_of_moment_lln hmeanLLLN hmeanL))
  have herror2 : Tendsto (fun t => 2 * error t) l (𝓝 0) := by
    simpa only [mul_zero] using hconsistent.const_mul 2
  apply tendsto_of_oracle_limit_and_uniform_perturbation horacle herror2
  filter_upwards [hn] with t ht
  have hbound := abs_empiricalBinaryResidualCovariance_sub_le_four_delta
    (oracle t) (fitted t) (response t) j ℓ ht (error t)
    (hp t) (hfitted t) (herror t)
  convert hbound using 1
  ring

/--
Remark 1, with its conditional LLNs and uniform consistency stated in one
arbitrary filter-indexed regime. The regime's dimension tends to infinity;
its sample size and observations are otherwise governed by the displayed LLNs.
The fixed finite population is the population of Theorem 3. Sample items may
repeat, and fitted probabilities may depend on the complete sample.

The first-moment LLNs supply the centering step. Population first moments and
the raw cross moment are derived from the discrepancy and null marginal
hypotheses. A variance floor is required only for the Pearson clause.
-/
def currentRemark1Spec
    {ι Item Model : Type*} [Fintype Item] [Nonempty Item] [Fintype Model]
    [Fintype (Item → Model → Bool)]
    (l : Filter ι) (dimension sampleSize : ι → ℕ)
    (sampleItem : ι → ℕ → Item) (response : ι → ℕ → Model → Bool)
    (observed : FiniteLaw (Item → Model → Bool))
    (null : ℕ → FiniteLaw (Item → Model → Bool))
    (D : FiniteLaw (Item → Model → Bool) → FiniteLaw (Item → Model → Bool) → ℝ)
    (p : ℕ → Item → Model → ℝ) (fitted : ι → ℕ → Model → ℝ)
    (error : ι → ℝ) (j ℓ : Model) : Prop :=
  j ≠ ℓ → ControlsBoundedExpectationsAtZero D →
    (∀ K i m, 0 ≤ p K i m ∧ p K i m ≤ 1) →
    (∀ K, HasProductBernoulliItemRowMarginals (null K) (p K)) →
    Tendsto (fun K => D observed (null K)) atTop (𝓝 0) →
    Tendsto dimension l atTop → (∀ᶠ t in l, 0 < sampleSize t) →
    (∀ t i, i < sampleSize t → ∀ m, 0 ≤ fitted t i m ∧ fitted t i m ≤ 1) →
    (∀ t i, i < sampleSize t → ∀ m,
      |fitted t i m - p (dimension t) (sampleItem t i) m| ≤ error t) →
    Tendsto error l (𝓝 0) →
    let oracle : ι → ℕ → Model → ℝ := fun t i m => p (dimension t) (sampleItem t i) m
    let populationMean : ℕ → Model → ℝ := fun K m =>
      finiteLawExpectation observed (fun y => (Fintype.card Item : ℝ)⁻¹ *
        ∑ i : Item, (boolAsReal (y i m) - p K i m))
    let populationCross : ℕ → ℝ := fun K =>
      finiteLawExpectation observed (fun y => (Fintype.card Item : ℝ)⁻¹ *
        ∑ i : Item, (boolAsReal (y i j) - p K i j) * (boolAsReal (y i ℓ) - p K i ℓ))
    Tendsto (fun t => empiricalBinaryResidualCrossMoment (oracle t) (response t)
      j ℓ (sampleSize t) - populationCross (dimension t)) l (𝓝 0) →
    Tendsto (fun t => empiricalBinaryResidualMean (oracle t) (response t)
      j (sampleSize t) - populationMean (dimension t) j) l (𝓝 0) →
    Tendsto (fun t => empiricalBinaryResidualMean (oracle t) (response t)
      ℓ (sampleSize t) - populationMean (dimension t) ℓ) l (𝓝 0) →
    let sampleCovariance : ι → Model → Model → ℝ := fun t a b =>
      ((∑ i ∈ Finset.range (sampleSize t),
        (boolAsReal (response t i a) - fitted t i a) *
          (boolAsReal (response t i b) - fitted t i b)) / (sampleSize t : ℝ)) -
      ((∑ i ∈ Finset.range (sampleSize t),
        (boolAsReal (response t i a) - fitted t i a)) / (sampleSize t : ℝ)) *
      ((∑ i ∈ Finset.range (sampleSize t),
        (boolAsReal (response t i b) - fitted t i b)) / (sampleSize t : ℝ))
    Tendsto (fun t => sampleCovariance t j ℓ) l (𝓝 0) ∧
      (∀ v : ℝ, 0 < v →
        (∀ᶠ t in l, v ≤ sampleCovariance t j j ∧ v ≤ sampleCovariance t ℓ ℓ) →
        Tendsto (fun t => sampleCovariance t j ℓ /
          Real.sqrt (sampleCovariance t j j * sampleCovariance t ℓ ℓ)) l (𝓝 0))

/-- The conditional moment-transfer assertion of Remark 1. -/
theorem currentRemark1
    {ι Item Model : Type*} [Fintype Item] [Nonempty Item] [Fintype Model]
    [Fintype (Item → Model → Bool)]
    (l : Filter ι) (dimension sampleSize : ι → ℕ)
    (sampleItem : ι → ℕ → Item) (response : ι → ℕ → Model → Bool)
    (observed : FiniteLaw (Item → Model → Bool))
    (null : ℕ → FiniteLaw (Item → Model → Bool))
    (D : FiniteLaw (Item → Model → Bool) → FiniteLaw (Item → Model → Bool) → ℝ)
    (p : ℕ → Item → Model → ℝ) (fitted : ι → ℕ → Model → ℝ)
    (error : ι → ℝ) (j ℓ : Model) :
    currentRemark1Spec l dimension sampleSize sampleItem response observed null D p fitted error j ℓ := by
  unfold currentRemark1Spec
  intro hjℓ hD hp hrows hlim hdimension hn hfitted herror hconsistent
  dsimp only
  intro hcrossLLN hmeanJLLN hmeanLLLN
  have hcross :=
    (averagePairResidual_tendsto_zero_of_productItemRowMarginals_and_qualitative_discrepancy
      hD observed null p j ℓ hjℓ hp hrows hlim).comp hdimension
  have hmeanJ :=
    (averageResidualMean_tendsto_zero_of_productItemRowMarginals_and_qualitative_discrepancy
      hD observed null p j hp hrows hlim).comp hdimension
  have hmeanL :=
    (averageResidualMean_tendsto_zero_of_productItemRowMarginals_and_qualitative_discrepancy
      hD observed null p ℓ hp hrows hlim).comp hdimension
  have hcov := fittedResidualCovariance_tendsto_zero_of_moment_lln
    sampleSize response (fun t i m => p (dimension t) (sampleItem t i) m) fitted error j ℓ
    (fun t => finiteLawExpectation observed (averagePairResidualFunctional (p (dimension t)) j ℓ))
    (fun t => finiteLawExpectation observed (averageResidualMeanFunctional (p (dimension t)) j))
    (fun t => finiteLawExpectation observed (averageResidualMeanFunctional (p (dimension t)) ℓ))
    hn (fun t i _ m => hp (dimension t) (sampleItem t i) m)
    hfitted herror hconsistent hcrossLLN hmeanJLLN hmeanLLLN hcross hmeanJ hmeanL
  refine ⟨hcov, ?_⟩
  intro v hv hfloor
  exact pearsonFromMoments_tendsto_zero_of_variance_floor hcov hv hfloor

end

end JGR26SubjectivityMonoculture
