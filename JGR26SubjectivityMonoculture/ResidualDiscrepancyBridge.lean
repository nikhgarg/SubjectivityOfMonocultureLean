import JGR26SubjectivityMonoculture.MainTheorems

/-!
# Qualitative discrepancy control of finite-state residual expectations

A discrepancy controls bounded expectations at zero when its convergence to
zero against a fixed observed law implies convergence of each fixed bounded
observable's expectation. On a fixed finite state space, indicators then give
convergence of every probability mass, hence finite L1 convergence and uniform
control of all observables bounded by one. This permits residual observables
that vary with model dimension without imposing a linear modulus on the
discrepancy. Total variation uses the convention `TV = L1 / 2`.
-/

namespace JGR26SubjectivityMonoculture

open Filter
open scoped BigOperators Topology

noncomputable section

/--
Qualitative control of bounded expectations at zero discrepancy. The test
observable is fixed along each sequence; no rate or linear bound in `D` is
required. The bound-one normalization suffices to test all finite-state masses.
-/
def ControlsBoundedExpectationsAtZero {Ω : Type*} [Fintype Ω]
    (D : FiniteLaw Ω → FiniteLaw Ω → ℝ) : Prop :=
  ∀ (observed : FiniteLaw Ω) (fitted : ℕ → FiniteLaw Ω) (f : Ω → ℝ),
    (∀ ω, |f ω| ≤ 1) →
    Tendsto (fun K => D observed (fitted K)) atTop (𝓝 0) →
    Tendsto (fun K => finiteLawExpectation (fitted K) f) atTop
      (𝓝 (finiteLawExpectation observed f))

/-- The expectation of a singleton indicator is its probability mass. -/
theorem finiteLawExpectation_singleton_indicator
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (μ : FiniteLaw Ω) (a : Ω) :
    finiteLawExpectation μ (fun ω => if ω = a then 1 else 0) = μ.1 a := by
  simp [finiteLawExpectation]

/-- Fixed singleton observables give convergence of every finite-state probability mass. -/
theorem finiteLaw_mass_tendsto_of_controlsBoundedExpectationsAtZero
    {Ω : Type*} [Fintype Ω]
    {D : FiniteLaw Ω → FiniteLaw Ω → ℝ} (hD : ControlsBoundedExpectationsAtZero D)
    (observed : FiniteLaw Ω) (fitted : ℕ → FiniteLaw Ω)
    (hlim : Tendsto (fun K => D observed (fitted K)) atTop (𝓝 0)) (a : Ω) :
    Tendsto (fun K => (fitted K).1 a) atTop (𝓝 (observed.1 a)) := by
  classical
  have htest := hD observed fitted (fun ω => if ω = a then 1 else 0)
    (fun ω => by dsimp; split_ifs <;> norm_num) hlim
  simpa only [finiteLawExpectation_singleton_indicator] using htest

/-- Finite summation turns atom convergence into convergence of finite L1 discrepancy. -/
theorem finiteL1Discrepancy_tendsto_zero_of_mass_tendsto
    {Ω : Type*} [Fintype Ω]
    (observed : FiniteLaw Ω) (fitted : ℕ → FiniteLaw Ω)
    (hmass : ∀ a, Tendsto (fun K => (fitted K).1 a) atTop (𝓝 (observed.1 a))) :
    Tendsto (fun K => finiteL1Discrepancy observed (fitted K)) atTop (𝓝 0) := by
  have hcoord : ∀ a, Tendsto (fun K => |observed.1 a - (fitted K).1 a|) atTop (𝓝 0) := by
    intro a
    have hconst : Tendsto (fun _ : ℕ => observed.1 a) atTop (𝓝 (observed.1 a)) := tendsto_const_nhds
    simpa only [sub_self, abs_zero] using (hconst.sub (hmass a)).abs
  simpa only [finiteL1Discrepancy, Finset.sum_const_zero] using
    (tendsto_finset_sum Finset.univ (fun a _ha => hcoord a))

/-- Fixed bounded-observable control entails finite L1 convergence on the fixed state space. -/
theorem finiteL1Discrepancy_tendsto_zero_of_controlsBoundedExpectationsAtZero
    {Ω : Type*} [Fintype Ω]
    {D : FiniteLaw Ω → FiniteLaw Ω → ℝ} (hD : ControlsBoundedExpectationsAtZero D)
    (observed : FiniteLaw Ω) (fitted : ℕ → FiniteLaw Ω)
    (hlim : Tendsto (fun K => D observed (fitted K)) atTop (𝓝 0)) :
    Tendsto (fun K => finiteL1Discrepancy observed (fitted K)) atTop (𝓝 0) := by
  exact finiteL1Discrepancy_tendsto_zero_of_mass_tendsto observed fitted
    (finiteLaw_mass_tendsto_of_controlsBoundedExpectationsAtZero hD observed fitted hlim)

/-- Every fixed real observable converges in expectation once its finite-state masses converge. -/
theorem finiteLawExpectation_tendsto_of_mass_tendsto
    {Ω : Type*} [Fintype Ω]
    (observed : FiniteLaw Ω) (fitted : ℕ → FiniteLaw Ω) (f : Ω → ℝ)
    (hmass : ∀ a, Tendsto (fun K => (fitted K).1 a) atTop (𝓝 (observed.1 a))) :
    Tendsto (fun K => finiteLawExpectation (fitted K) f) atTop
      (𝓝 (finiteLawExpectation observed f)) := by
  exact tendsto_finset_sum Finset.univ (fun a _ha => (hmass a).mul_const (f a))

/-- The normalized qualitative test condition controls every fixed finite-state real observable. -/
theorem finiteLawExpectation_tendsto_of_controlsBoundedExpectationsAtZero
    {Ω : Type*} [Fintype Ω]
    {D : FiniteLaw Ω → FiniteLaw Ω → ℝ} (hD : ControlsBoundedExpectationsAtZero D)
    (observed : FiniteLaw Ω) (fitted : ℕ → FiniteLaw Ω) (f : Ω → ℝ)
    (hlim : Tendsto (fun K => D observed (fitted K)) atTop (𝓝 0)) :
    Tendsto (fun K => finiteLawExpectation (fitted K) f) atTop
      (𝓝 (finiteLawExpectation observed f)) := by
  exact finiteLawExpectation_tendsto_of_mass_tendsto observed fitted f
    (finiteLaw_mass_tendsto_of_controlsBoundedExpectationsAtZero hD observed fitted hlim)

/-- L1 convergence controls expectation differences even when the bounded observable varies. -/
theorem varyingBoundedExpectations_tendsto_zero_of_finiteL1Discrepancy
    {Ω : Type*} [Fintype Ω]
    (observed : FiniteLaw Ω) (fitted : ℕ → FiniteLaw Ω) (f : ℕ → Ω → ℝ)
    (hf : ∀ K ω, |f K ω| ≤ 1)
    (hL1 : Tendsto (fun K => finiteL1Discrepancy observed (fitted K)) atTop (𝓝 0)) :
    Tendsto (fun K => finiteLawExpectation observed (f K) -
      finiteLawExpectation (fitted K) (f K)) atTop (𝓝 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  exact squeeze_zero (fun _ => abs_nonneg _)
    (fun K => finiteL1Discrepancy_controlsBoundedExpectations observed (fitted K) (f K) (hf K)) hL1

/-- Qualitative fixed-observable discrepancy control gives uniform control of varying observables. -/
theorem varyingBoundedExpectations_tendsto_zero_of_controlsBoundedExpectationsAtZero
    {Ω : Type*} [Fintype Ω]
    {D : FiniteLaw Ω → FiniteLaw Ω → ℝ} (hD : ControlsBoundedExpectationsAtZero D)
    (observed : FiniteLaw Ω) (fitted : ℕ → FiniteLaw Ω) (f : ℕ → Ω → ℝ)
    (hf : ∀ K ω, |f K ω| ≤ 1)
    (hlim : Tendsto (fun K => D observed (fitted K)) atTop (𝓝 0)) :
    Tendsto (fun K => finiteLawExpectation observed (f K) -
      finiteLawExpectation (fitted K) (f K)) atTop (𝓝 0) := by
  exact varyingBoundedExpectations_tendsto_zero_of_finiteL1Discrepancy observed fitted f hf
    (finiteL1Discrepancy_tendsto_zero_of_controlsBoundedExpectationsAtZero hD observed fitted hlim)

/-- A single eventual cutoff controls every bound-one observable simultaneously. -/
theorem eventually_uniform_bounded_expectations_of_controlsBoundedExpectationsAtZero
    {Ω : Type*} [Fintype Ω]
    {D : FiniteLaw Ω → FiniteLaw Ω → ℝ} (hD : ControlsBoundedExpectationsAtZero D)
    (observed : FiniteLaw Ω) (fitted : ℕ → FiniteLaw Ω)
    (hlim : Tendsto (fun K => D observed (fitted K)) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ K in atTop, ∀ f : Ω → ℝ,
      (∀ ω, |f ω| ≤ 1) →
      |finiteLawExpectation observed f - finiteLawExpectation (fitted K) f| < ε := by
  have hL1 := finiteL1Discrepancy_tendsto_zero_of_controlsBoundedExpectationsAtZero
    hD observed fitted hlim
  intro ε hε
  have hsmall := hL1.eventually (eventually_lt_nhds hε)
  filter_upwards [hsmall] with K hsmall
  intro f hf
  exact (finiteL1Discrepancy_controlsBoundedExpectations observed (fitted K) f hf).trans_lt hsmall

/-- A coefficient-one finite bound implies qualitative control, without being its definition. -/
theorem controlsBoundedExpectationsAtZero_of_controlsBoundedExpectations
    {Ω : Type*} [Fintype Ω]
    {D : FiniteLaw Ω → FiniteLaw Ω → ℝ} (hD : ControlsBoundedExpectations D) :
    ControlsBoundedExpectationsAtZero D := by
  intro observed fitted f hf hlim
  have hdiff : Tendsto (fun K => finiteLawExpectation (fitted K) f -
      finiteLawExpectation observed f) atTop (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    apply squeeze_zero (fun _ => abs_nonneg _) _ hlim
    intro K
    simpa only [abs_sub_comm] using hD observed (fitted K) f hf
  simpa only [sub_add_cancel, zero_add] using hdiff.add
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => finiteLawExpectation observed f) atTop
      (𝓝 (finiteLawExpectation observed f)))

/-- Finite L1 discrepancy has the qualitative bounded-expectation control property. -/
theorem finiteL1Discrepancy_controlsBoundedExpectationsAtZero
    {Ω : Type*} [Fintype Ω] :
    ControlsBoundedExpectationsAtZero (finiteL1Discrepancy (Ω := Ω)) :=
  controlsBoundedExpectationsAtZero_of_controlsBoundedExpectations
    finiteL1Discrepancy_controlsBoundedExpectations

/--
On a fixed finite state space, qualitative bounded-expectation control is
equivalent to the implication from zero discrepancy to zero finite L1 distance.
-/
theorem controlsBoundedExpectationsAtZero_iff_finiteL1Discrepancy_tendsto_zero
    {Ω : Type*} [Fintype Ω] (D : FiniteLaw Ω → FiniteLaw Ω → ℝ) :
    ControlsBoundedExpectationsAtZero D ↔
      ∀ (observed : FiniteLaw Ω) (fitted : ℕ → FiniteLaw Ω),
        Tendsto (fun K => D observed (fitted K)) atTop (𝓝 0) →
        Tendsto (fun K => finiteL1Discrepancy observed (fitted K)) atTop (𝓝 0) := by
  constructor
  · exact finiteL1Discrepancy_tendsto_zero_of_controlsBoundedExpectationsAtZero
  · intro hL1 observed fitted f hf hlim
    exact finiteL1Discrepancy_controlsBoundedExpectationsAtZero observed fitted f hf
      (hL1 observed fitted hlim)

/-- Total variation on a finite state space, with the convention `TV = L1 / 2`. -/
def finiteTotalVariationDiscrepancy {Ω : Type*} [Fintype Ω]
    (μ ν : FiniteLaw Ω) : ℝ := finiteL1Discrepancy μ ν / 2

/-- The standard total-variation normalization entails finite L1 convergence. -/
theorem finiteL1Discrepancy_tendsto_zero_of_totalVariation_tendsto_zero
    {Ω : Type*} [Fintype Ω]
    (observed : FiniteLaw Ω) (fitted : ℕ → FiniteLaw Ω)
    (hTV : Tendsto (fun K => finiteTotalVariationDiscrepancy observed (fitted K)) atTop (𝓝 0)) :
    Tendsto (fun K => finiteL1Discrepancy observed (fitted K)) atTop (𝓝 0) := by
  have heq : (fun K => 2 * finiteTotalVariationDiscrepancy observed (fitted K)) =
      (fun K => finiteL1Discrepancy observed (fitted K)) := by
    funext K
    unfold finiteTotalVariationDiscrepancy
    ring
  simpa only [heq, mul_zero] using hTV.const_mul 2

/-- Total variation controls bounded expectations at zero with its standard factor of one half. -/
theorem finiteTotalVariationDiscrepancy_controlsBoundedExpectationsAtZero
    {Ω : Type*} [Fintype Ω] :
    ControlsBoundedExpectationsAtZero (finiteTotalVariationDiscrepancy (Ω := Ω)) := by
  intro observed fitted f hf hTV
  exact finiteL1Discrepancy_controlsBoundedExpectationsAtZero observed fitted f hf
    (finiteL1Discrepancy_tendsto_zero_of_totalVariation_tendsto_zero observed fitted hTV)

/-! ## Actual item-row marginals -/

/--
Each actual item-row marginal of the fitted joint law is the product Bernoulli
law generated by that item's probabilities. Dependence between distinct item
rows is unrestricted.
-/
def HasProductBernoulliItemRowMarginals
    {Item Model : Type*} [Fintype Item] [Fintype Model]
    [Fintype (Item → Model → Bool)]
    (fitted : FiniteLaw (Item → Model → Bool)) (p : Item → Model → ℝ) : Prop := by
  classical
  exact ∀ (i : Item) (r : Model → Bool),
    finiteLawExpectation fitted (fun response => if response i = r then 1 else 0) =
      productBernoulliMass (p i) r

/-- A finite marginal specified by indicator events determines every expectation of that marginal. -/
theorem finiteLawExpectation_comp_eq_sum_indicator_marginals
    {Ω Row : Type*} [Fintype Ω] [Fintype Row] [DecidableEq Row]
    (μ : FiniteLaw Ω) (row : Ω → Row) (f : Row → ℝ) :
    finiteLawExpectation μ (fun ω => f (row ω)) =
      ∑ r : Row, finiteLawExpectation μ (fun ω => if row ω = r then 1 else 0) * f r := by
  classical
  calc
    _ = ∑ ω : Ω, μ.1 ω * ∑ r : Row, (if row ω = r then 1 else 0) * f r := by
      simp [finiteLawExpectation]
    _ = _ := by
      simp only [finiteLawExpectation, Finset.mul_sum, Finset.sum_mul, mul_assoc]
      rw [Finset.sum_comm]

/-- The item-row marginal condition gives the exact expectation of every row observable. -/
theorem finiteLawExpectation_itemRow_eq_of_productBernoulliItemRowMarginals
    {Item Model : Type*} [Fintype Item] [Fintype Model] [DecidableEq Model]
    [Fintype (Item → Model → Bool)]
    (fitted : FiniteLaw (Item → Model → Bool)) (p : Item → Model → ℝ)
    (hrows : HasProductBernoulliItemRowMarginals fitted p)
    (i : Item) (f : (Model → Bool) → ℝ) :
    finiteLawExpectation fitted (fun response => f (response i)) =
      ∑ r : Model → Bool, productBernoulliMass (p i) r * f r := by
  classical
  rw [finiteLawExpectation_comp_eq_sum_indicator_marginals fitted (fun response => response i) f]
  exact Finset.sum_congr rfl (fun r _hr => by rw [hrows i r])

/-- The coordinate-product Bernoulli PMF has the source's product Bernoulli mass. -/
theorem productBernoulliPMF_toReal_eq_mass
    {Model : Type*} [Fintype Model] [DecidableEq Model]
    (p : Model → ℝ) (hp : ∀ m, 0 ≤ p m ∧ p m ≤ 1) (r : Model → Bool) :
    (AppliedModelingLib.pmfPi (fun m => realBernoulliPMF (p m) (hp m).1 (hp m).2) r).toReal =
      productBernoulliMass p r := by
  rw [AppliedModelingLib.pmfPi_apply_toReal]
  apply Finset.prod_congr rfl
  intro m _hm
  cases r m <;> simp

/-- Product model-coordinate marginals give zero cross-residual expectation for distinct models. -/
theorem productBernoulliMass_residualCrossExpectation_zero
    {Model : Type*} [Fintype Model] [DecidableEq Model]
    (p : Model → ℝ) (hp : ∀ m, 0 ≤ p m ∧ p m ≤ 1)
    (j ℓ : Model) (hjℓ : j ≠ ℓ) :
    (∑ r : Model → Bool, productBernoulliMass p r *
      (binaryResidual (p j) (r j) * binaryResidual (p ℓ) (r ℓ))) = 0 := by
  classical
  let μ : Model → PMF Bool := fun m => realBernoulliPMF (p m) (hp m).1 (hp m).2
  have hsum : (∑ r : Model → Bool, productBernoulliMass p r *
      (binaryResidual (p j) (r j) * binaryResidual (p ℓ) (r ℓ))) =
      AppliedModelingLib.pmfExp (AppliedModelingLib.pmfPi μ)
        (fun r => binaryResidual (p j) (r j) * binaryResidual (p ℓ) (r ℓ)) := by
    unfold AppliedModelingLib.pmfExp
    exact Finset.sum_congr rfl (fun r _hr => by rw [productBernoulliPMF_toReal_eq_mass p hp r])
  rw [hsum, AppliedModelingLib.pmfExp_pmfPi_twoCoord_eq_pairExp μ hjℓ
    (fun b₁ b₂ => binaryResidual (p j) b₁ * binaryResidual (p ℓ) b₂)]
  simp [AppliedModelingLib.pmfPairExp, AppliedModelingLib.pmfExp, μ, binaryResidual, boolAsReal]
  ring

/--
Actual product item-row marginals imply zero averaged residual expectation.
Only the distribution of each individual row is used.
-/
theorem averagePairResidualExpectation_zero_of_productItemRowMarginals
    {Item Model : Type*} [Fintype Item] [Nonempty Item] [Fintype Model]
    [Fintype (Item → Model → Bool)]
    (fitted : FiniteLaw (Item → Model → Bool)) (p : Item → Model → ℝ)
    (j ℓ : Model) (hjℓ : j ≠ ℓ)
    (hp : ∀ i m, 0 ≤ p i m ∧ p i m ≤ 1)
    (hrows : HasProductBernoulliItemRowMarginals fitted p) :
    finiteLawExpectation fitted (averagePairResidualFunctional p j ℓ) = 0 := by
  classical
  have hzero : ∀ i : Item, finiteLawExpectation fitted (fun response =>
      binaryResidual (p i j) (response i j) * binaryResidual (p i ℓ) (response i ℓ)) = 0 := by
    intro i
    rw [finiteLawExpectation_itemRow_eq_of_productBernoulliItemRowMarginals
      fitted p hrows i (fun r => binaryResidual (p i j) (r j) * binaryResidual (p i ℓ) (r ℓ))]
    exact productBernoulliMass_residualCrossExpectation_zero (p i) (hp i) j ℓ hjℓ
  have havg : finiteLawExpectation fitted (averagePairResidualFunctional p j ℓ) =
      ((Fintype.card Item : ℝ)⁻¹) * ∑ i : Item, finiteLawExpectation fitted (fun response =>
        binaryResidual (p i j) (response i j) * binaryResidual (p i ℓ) (response i ℓ)) := by
    simp only [finiteLawExpectation, averagePairResidualFunctional, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro response _hr
    ring
  rw [havg]
  simp only [hzero, Finset.sum_const_zero, mul_zero]

/--
The source residual-dependence conclusion for arbitrary fitted joint response
laws with product Bernoulli item-row marginals. Conditional independence is
used within each fixed item; no relation between different items is assumed.
-/
theorem averagePairResidual_tendsto_zero_of_productItemRowMarginals_and_qualitative_discrepancy
    {Item Model : Type*} [Fintype Item] [Nonempty Item] [Fintype Model]
    [Fintype (Item → Model → Bool)]
    {D : FiniteLaw (Item → Model → Bool) → FiniteLaw (Item → Model → Bool) → ℝ}
    (hD : ControlsBoundedExpectationsAtZero D)
    (observed : FiniteLaw (Item → Model → Bool))
    (fitted : ℕ → FiniteLaw (Item → Model → Bool))
    (p : ℕ → Item → Model → ℝ) (j ℓ : Model) (hjℓ : j ≠ ℓ)
    (hp : ∀ K i m, 0 ≤ p K i m ∧ p K i m ≤ 1)
    (hrows : ∀ K, HasProductBernoulliItemRowMarginals (fitted K) (p K))
    (hlim : Tendsto (fun K => D observed (fitted K)) atTop (𝓝 0)) :
    Tendsto (fun K => finiteLawExpectation observed (averagePairResidualFunctional (p K) j ℓ))
      atTop (𝓝 0) := by
  have hdiff := varyingBoundedExpectations_tendsto_zero_of_controlsBoundedExpectationsAtZero
    hD observed fitted (fun K => averagePairResidualFunctional (p K) j ℓ)
    (fun K => averagePairResidualFunctional_abs_le_one (p K) j ℓ (hp K)) hlim
  have hzero : ∀ K, finiteLawExpectation (fitted K) (averagePairResidualFunctional (p K) j ℓ) = 0 :=
    fun K => averagePairResidualExpectation_zero_of_productItemRowMarginals
      (fitted K) (p K) j ℓ hjℓ (hp K) (hrows K)
  simpa only [hzero, sub_zero] using hdiff

/-- The full cell-product response PMF is also a product of its item-row PMFs. -/
theorem fixedDesignResponsePMF_eq_productItemRows
    {Item Model : Type*} [Fintype Item] [Fintype Model]
    [DecidableEq Item] [DecidableEq Model]
    (p : Item → Model → ℝ) (hp : ∀ i m, 0 ≤ p i m ∧ p i m ≤ 1) :
    fixedDesignResponsePMF p hp =
      AppliedModelingLib.pmfPi (fun i => AppliedModelingLib.pmfPi
        (fun m => realBernoulliPMF (p i m) (hp i m).1 (hp i m).2)) := by
  classical
  apply PMF.ext
  intro response
  rw [fixedDesignResponsePMF, PMF.map_apply, tsum_fintype]
  rw [Finset.sum_eq_single ((responseCurryEquiv Item Model).symm response)]
  · simp only [Equiv.apply_symm_apply, if_true]
    rw [AppliedModelingLib.pmfPi_apply, AppliedModelingLib.pmfPi_apply]
    simp_rw [AppliedModelingLib.pmfPi_apply]
    rw [Fintype.prod_prod_type]
    rfl
  · intro other _hother hne
    rw [if_neg]
    intro heq
    apply hne
    simpa only [Equiv.symm_apply_apply] using (congrArg (responseCurryEquiv Item Model).symm heq).symm
  · simp

/-- The concrete full product response law satisfies the actual item-row marginal condition. -/
theorem fixedDesignResponseLaw_hasProductBernoulliItemRowMarginals
    {Item Model : Type*} [Fintype Item] [Fintype Model]
    [DecidableEq Item] [DecidableEq Model]
    [fState : Fintype (Item → Model → Bool)] [DecidableEq (Item → Model → Bool)]
    (p : Item → Model → ℝ) (hp : ∀ i m, 0 ≤ p i m ∧ p i m ≤ 1) :
    HasProductBernoulliItemRowMarginals (fixedDesignResponseLaw p hp) p := by
  classical
  have henum : fState = (Pi.instFintype : Fintype (Item → Model → Bool)) := Subsingleton.elim _ _
  cases henum
  intro i r
  change AppliedModelingLib.pmfExp (fixedDesignResponsePMF p hp)
    (fun response => if response i = r then 1 else 0) = productBernoulliMass (p i) r
  rw [fixedDesignResponsePMF_eq_productItemRows]
  rw [AppliedModelingLib.pmfExp_pmfPi_eval_eq
    (fun i => AppliedModelingLib.pmfPi
      (fun m => realBernoulliPMF (p i m) (hp i m).1 (hp i m).2)) i
    (fun row => if row = r then 1 else 0)]
  change finiteLawExpectation (finiteLawOfPMF (AppliedModelingLib.pmfPi
    (fun m => realBernoulliPMF (p i m) (hp i m).1 (hp i m).2)))
    (fun row => if row = r then 1 else 0) = productBernoulliMass (p i) r
  rw [finiteLawExpectation_singleton_indicator]
  exact productBernoulliPMF_toReal_eq_mass (p i) (hp i) r

/--
Theorem 3 for the concrete fitted fixed-design product laws and any discrepancy
that qualitatively controls bounded expectations. The varying residual
functional is uniformly bounded, and its null expectation is proved from the
product response law for two distinct model coordinates.
-/
theorem averagePairResidual_tendsto_zero_of_fixedDesignProductNulls_and_qualitative_discrepancy
    {Item Model : Type*} [Fintype Item] [Nonempty Item] [Fintype Model]
    [DecidableEq Item] [DecidableEq Model]
    [Fintype (Item → Model → Bool)] [DecidableEq (Item → Model → Bool)]
    {D : FiniteLaw (Item → Model → Bool) → FiniteLaw (Item → Model → Bool) → ℝ}
    (hD : ControlsBoundedExpectationsAtZero D)
    (observed : FiniteLaw (Item → Model → Bool))
    (p : ℕ → Item → Model → ℝ) (j ℓ : Model) (hjℓ : j ≠ ℓ)
    (hp : ∀ K i m, 0 ≤ p K i m ∧ p K i m ≤ 1)
    (hlim : Tendsto (fun K => D observed (fixedDesignResponseLaw (p K) (hp K))) atTop (𝓝 0)) :
    Tendsto (fun K => finiteLawExpectation observed (averagePairResidualFunctional (p K) j ℓ))
      atTop (𝓝 0) := by
  have hdiff := varyingBoundedExpectations_tendsto_zero_of_controlsBoundedExpectationsAtZero
    hD observed (fun K => fixedDesignResponseLaw (p K) (hp K))
    (fun K => averagePairResidualFunctional (p K) j ℓ)
    (fun K => averagePairResidualFunctional_abs_le_one (p K) j ℓ (hp K)) hlim
  have hzero : ∀ K, finiteLawExpectation (fixedDesignResponseLaw (p K) (hp K))
      (averagePairResidualFunctional (p K) j ℓ) = 0 := by
    intro K
    exact (fixedDesignResponseLaw_matchesProductPairNull (p K) (hp K) hjℓ).trans
      (averagePairResidual_productPairNullExpectation_zero (p K) j ℓ)
  simpa only [hzero, sub_zero] using hdiff

/-- The paper's elementary sequence predicate agrees with the standard real-sequence limit. -/
theorem sequenceConvergesTo_iff_tendsto (x : ℕ → ℝ) (limit : ℝ) :
    SequenceConvergesTo x limit ↔ Tendsto x atTop (𝓝 limit) := by
  constructor
  · intro hseq
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := hseq (ε / 2) (half_pos hε)
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq]
    exact (hN n hn).trans_lt (by linarith)
  · intro hlim ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim ε hε
    refine ⟨N, fun n hn => ?_⟩
    simpa only [Real.dist_eq] using (hN n hn).le

/-- The general item-row marginal conclusion in the source's elementary sequence interface. -/
theorem averagePairResidual_converges_to_zero_of_productItemRowMarginals_and_qualitative_discrepancy
    {Item Model : Type*} [Fintype Item] [Nonempty Item] [Fintype Model]
    [Fintype (Item → Model → Bool)]
    {D : FiniteLaw (Item → Model → Bool) → FiniteLaw (Item → Model → Bool) → ℝ}
    (hD : ControlsBoundedExpectationsAtZero D)
    (observed : FiniteLaw (Item → Model → Bool))
    (fitted : ℕ → FiniteLaw (Item → Model → Bool))
    (p : ℕ → Item → Model → ℝ) (j ℓ : Model) (hjℓ : j ≠ ℓ)
    (hp : ∀ K i m, 0 ≤ p K i m ∧ p K i m ≤ 1)
    (hrows : ∀ K, HasProductBernoulliItemRowMarginals (fitted K) (p K))
    (hlim : SequenceConvergesTo (fun K => D observed (fitted K)) 0) :
    SequenceConvergesTo
      (fun K => finiteLawExpectation observed (averagePairResidualFunctional (p K) j ℓ)) 0 := by
  apply (sequenceConvergesTo_iff_tendsto _ _).mpr
  exact averagePairResidual_tendsto_zero_of_productItemRowMarginals_and_qualitative_discrepancy
    hD observed fitted p j ℓ hjℓ hp hrows ((sequenceConvergesTo_iff_tendsto _ _).mp hlim)

/-- Theorem 3 in the existing source-facing sequence interface, with qualitative discrepancy control. -/
theorem averagePairResidual_converges_to_zero_of_fixedDesignProductNulls_and_qualitative_discrepancy
    {Item Model : Type*} [Fintype Item] [Nonempty Item] [Fintype Model]
    [DecidableEq Item] [DecidableEq Model]
    [Fintype (Item → Model → Bool)] [DecidableEq (Item → Model → Bool)]
    {D : FiniteLaw (Item → Model → Bool) → FiniteLaw (Item → Model → Bool) → ℝ}
    (hD : ControlsBoundedExpectationsAtZero D)
    (observed : FiniteLaw (Item → Model → Bool))
    (p : ℕ → Item → Model → ℝ) (j ℓ : Model) (hjℓ : j ≠ ℓ)
    (hp : ∀ K i m, 0 ≤ p K i m ∧ p K i m ≤ 1)
    (hlim : SequenceConvergesTo
      (fun K => D observed (fixedDesignResponseLaw (p K) (hp K))) 0) :
    SequenceConvergesTo
      (fun K => finiteLawExpectation observed (averagePairResidualFunctional (p K) j ℓ)) 0 := by
  apply (sequenceConvergesTo_iff_tendsto _ _).mpr
  exact averagePairResidual_tendsto_zero_of_fixedDesignProductNulls_and_qualitative_discrepancy
    hD observed p j ℓ hjℓ hp ((sequenceConvergesTo_iff_tendsto _ _).mp hlim)

end

end JGR26SubjectivityMonoculture
