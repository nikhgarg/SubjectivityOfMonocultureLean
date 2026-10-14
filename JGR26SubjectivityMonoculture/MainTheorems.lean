import AppliedModelingLib.Foundations.Math.FiniteOptimization
import AppliedModelingLib.Foundations.Probability.IndependentProduct
import Mathlib.Tactic

/-!
# Finite probability and local stability lemmas

Finite response laws, vertex mixtures, nested null families, discrepancy
control, centered residuals, and quantitative local identification supply the
algebraic and probabilistic helpers for the paper interfaces. The factor
lemmas also describe prediction invariances and cancellation directions.
-/

open scoped BigOperators

namespace JGR26SubjectivityMonoculture

noncomputable section

/-! ## Finite laws and vertex mixtures -/

/-- A finite probability law represented as a nonnegative mass function summing to one. -/
abbrev FiniteLaw (Ω : Type*) [Fintype Ω] :=
  { mass : Ω → ℝ // AppliedModelingLib.FiniteProbabilitySimplex mass }

/-- Expectation of a real function under a finite law. -/
def finiteLawExpectation {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (f : Ω → ℝ) : ℝ :=
  ∑ ω : Ω, μ.1 ω * f ω

/-- Convert a finite PMF into the paper-local finite-law representation. -/
def finiteLawOfPMF {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μ : PMF Ω) : FiniteLaw Ω :=
  ⟨fun ω : Ω => (μ ω).toReal, by
    constructor
    · intro ω
      exact ENNReal.toReal_nonneg
    · exact AppliedModelingLib.pmfToRealSum μ⟩

@[simp]
theorem finiteLawExpectation_finiteLawOfPMF
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μ : PMF Ω) (f : Ω → ℝ) :
    finiteLawExpectation (finiteLawOfPMF μ) f = AppliedModelingLib.pmfExp μ f := rfl

/-! ## Product Bernoulli and MIRT null semantics -/

/-- Finite dot product for the latent vectors used in MIRT-style nulls. -/
def finiteDot {K : ℕ} (a θ : Fin K → ℝ) : ℝ :=
  ∑ k : Fin K, a k * θ k

@[simp]
theorem finiteDot_comm {K : ℕ} (x y : Fin K → ℝ) :
    finiteDot x y = finiteDot y x := by
  unfold finiteDot
  refine Finset.sum_congr rfl ?_
  intro k _hk
  ring

@[simp]
theorem finiteDot_neg_right {K : ℕ} (x y : Fin K → ℝ) :
    finiteDot x (fun k : Fin K => - y k) = - finiteDot x y := by
  unfold finiteDot
  simp [mul_neg, Finset.sum_neg_distrib]

theorem finiteDot_smul_left {K : ℕ} (a : ℝ) (x y : Fin K → ℝ) :
    finiteDot (fun k : Fin K => a * x k) y = a * finiteDot x y := by
  unfold finiteDot
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k _hk
  ring

theorem finiteDot_smul_right {K : ℕ} (a : ℝ) (x y : Fin K → ℝ) :
    finiteDot x (fun k : Fin K => a * y k) = a * finiteDot x y := by
  unfold finiteDot
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k _hk
  ring

theorem finiteDot_smul_smul {K : ℕ} (a b : ℝ) (x y : Fin K → ℝ) :
    finiteDot (fun k : Fin K => a * x k) (fun k : Fin K => b * y k) =
      (a * b) * finiteDot x y := by
  rw [finiteDot_smul_left, finiteDot_smul_right]
  ring

/--
Source-facing MIRT success probability for item `i` and model `j`.

The link function is left abstract because the draft allows standard choices
such as logit or probit.
-/
def MIRTSuccessProbability {K : ℕ} {Item Model : Type*}
    (link : ℝ → ℝ)
    (itemSlope : Item → Fin K → ℝ)
    (itemDifficulty : Item → ℝ)
    (modelAbility : Model → Fin K → ℝ)
    (i : Item) (j : Model) : ℝ :=
  link (finiteDot (itemSlope i) (modelAbility j) + itemDifficulty i)

/--
Product-Bernoulli mass for a finite vector of binary model responses.

This is the fixed-design conditional-independence object used by the draft:
after the fitted item/model parameters are fixed, model coordinates multiply.
-/
def productBernoulliMass {Model : Type*} [Fintype Model]
    (p : Model → ℝ) (response : Model → Bool) : ℝ :=
  ∏ j : Model, if response j then p j else 1 - p j

/-- Bernoulli PMF with real success probability in `[0,1]`. -/
def realBernoulliPMF (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : PMF Bool :=
  PMF.bernoulli ⟨p, hp0⟩ (by
    change p ≤ (1 : ℝ)
    exact hp1)

@[simp]
theorem realBernoulliPMF_apply_true_toReal
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (realBernoulliPMF p hp0 hp1 true).toReal = p := by
  rw [realBernoulliPMF, PMF.bernoulli_apply]
  change ((⟨p, hp0⟩ : NNReal) : ℝ) = p
  rfl

@[simp]
theorem realBernoulliPMF_apply_false_toReal
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (realBernoulliPMF p hp0 hp1 false).toReal = 1 - p := by
  rw [realBernoulliPMF, PMF.bernoulli_apply]
  change ((1 - ⟨p, hp0⟩ : NNReal) : ℝ) = 1 - p
  rw [NNReal.coe_sub]
  · rfl
  · change p ≤ (1 : ℝ)
    exact hp1

/-- A finite law is a product-Bernoulli law if it has some coordinate probabilities. -/
def IsProductBernoulliLaw {Model : Type*} [Fintype Model]
    (Q : (Model → Bool) → ℝ) : Prop :=
  ∃ p : Model → ℝ, Q = productBernoulliMass p

/-- Convert a binary response to its real-valued indicator. -/
def boolAsReal (b : Bool) : ℝ :=
  if b then 1 else 0

/-- Binary residual for a fitted success probability. -/
def binaryResidual (p : ℝ) (response : Bool) : ℝ :=
  boolAsReal response - p

/-- Binary residuals are bounded by one when the fitted probability lies in `[0,1]`. -/
theorem abs_binaryResidual_le_one
    (p : ℝ) (response : Bool) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    |binaryResidual p response| ≤ 1 := by
  cases response
  · dsimp [binaryResidual, boolAsReal]
    simpa [abs_neg, abs_of_nonneg hp0] using hp1
  · dsimp [binaryResidual, boolAsReal]
    have hnonneg : 0 ≤ 1 - p := by linarith
    have hle : 1 - p ≤ 1 := by linarith
    simpa [abs_of_nonneg hnonneg] using hle

/-- Changing the fitted probability changes a binary residual by the same amount. -/
theorem abs_binaryResidual_sub_le_of_abs_prob_sub_le
    (p q : ℝ) (response : Bool) {δ : ℝ}
    (hδ : |q - p| ≤ δ) :
    |binaryResidual q response - binaryResidual p response| ≤ δ := by
  have hsame :
      binaryResidual q response - binaryResidual p response = p - q := by
    cases response
    · simp [binaryResidual, boolAsReal]
      ring
    · simp [binaryResidual, boolAsReal]
  calc
    |binaryResidual q response - binaryResidual p response| = |p - q| := by
      rw [hsame]
    _ = |q - p| := abs_sub_comm p q
    _ ≤ δ := hδ

/--
The source's averaged pairwise residual functional for a fixed pair of models.

This is the `g_K` used in the proof of Theorem 3, with the fitted
probability table left as an explicit input.
-/
def averagePairResidualFunctional
    {Item Model : Type*} [Fintype Item] [Nonempty Item]
    (p : Item → Model → ℝ) (j ℓ : Model)
    (response : Item → Model → Bool) : ℝ :=
  ((Fintype.card Item : ℝ)⁻¹) *
    ∑ i : Item,
      binaryResidual (p i j) (response i j) *
        binaryResidual (p i ℓ) (response i ℓ)

/--
The averaged binary pair-residual functional is bounded by one in absolute
value whenever all fitted probabilities lie in `[0,1]`.
-/
theorem averagePairResidualFunctional_abs_le_one
    {Item Model : Type*} [Fintype Item] [Nonempty Item]
    (p : Item → Model → ℝ) (j ℓ : Model)
    (hp : ∀ i : Item, ∀ m : Model, 0 ≤ p i m ∧ p i m ≤ 1)
    (response : Item → Model → Bool) :
    |averagePairResidualFunctional p j ℓ response| ≤ 1 := by
  classical
  have hcard_pos : 0 < (Fintype.card Item : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Item)
  have hinv_nonneg : 0 ≤ ((Fintype.card Item : ℝ)⁻¹) :=
    inv_nonneg.mpr (le_of_lt hcard_pos)
  have hterm :
      ∀ i : Item,
        |binaryResidual (p i j) (response i j) *
            binaryResidual (p i ℓ) (response i ℓ)| ≤ 1 := by
    intro i
    have hj := abs_binaryResidual_le_one
      (p i j) (response i j) (hp i j).1 (hp i j).2
    have hℓ := abs_binaryResidual_le_one
      (p i ℓ) (response i ℓ) (hp i ℓ).1 (hp i ℓ).2
    rw [abs_mul]
    exact mul_le_one₀ hj (abs_nonneg _) hℓ
  calc
    |averagePairResidualFunctional p j ℓ response|
        = ((Fintype.card Item : ℝ)⁻¹) *
            |∑ i : Item,
              binaryResidual (p i j) (response i j) *
                binaryResidual (p i ℓ) (response i ℓ)| := by
          simp [averagePairResidualFunctional, abs_mul, abs_of_nonneg hinv_nonneg]
    _ ≤ ((Fintype.card Item : ℝ)⁻¹) *
        ∑ i : Item,
          |binaryResidual (p i j) (response i j) *
            binaryResidual (p i ℓ) (response i ℓ)| := by
          exact mul_le_mul_of_nonneg_left
            (by
              simpa using
                (Finset.abs_sum_le_sum_abs
                  (fun i : Item =>
                    binaryResidual (p i j) (response i j) *
                      binaryResidual (p i ℓ) (response i ℓ))
                  Finset.univ))
            hinv_nonneg
    _ ≤ ((Fintype.card Item : ℝ)⁻¹) * ∑ _i : Item, (1 : ℝ) := by
          exact mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum (fun i _hi => hterm i))
            hinv_nonneg
    _ = 1 := by
          simp [Finset.sum_const, nsmul_eq_mul]

/--
A product of two bounded residuals is stable under a uniform residual
perturbation.
-/
theorem abs_mul_sub_mul_le_two_delta_of_abs_le_one
    {a b a' b' δ : ℝ}
    (ha : |a| ≤ 1) (hb' : |b'| ≤ 1)
    (ha_diff : |a' - a| ≤ δ) (hb_diff : |b' - b| ≤ δ) :
    |a' * b' - a * b| ≤ 2 * δ := by
  have hδ_nonneg : 0 ≤ δ := le_trans (abs_nonneg _) ha_diff
  have hsplit : a' * b' - a * b = (a' - a) * b' + a * (b' - b) := by
    ring
  calc
    |a' * b' - a * b|
        = |(a' - a) * b' + a * (b' - b)| := by rw [hsplit]
    _ ≤ |(a' - a) * b'| + |a * (b' - b)| := abs_add_le _ _
    _ = |a' - a| * |b'| + |a| * |b' - b| := by
          rw [abs_mul, abs_mul]
    _ ≤ δ * 1 + 1 * δ := by
          have hleft : |a' - a| * |b'| ≤ δ * 1 :=
            mul_le_mul ha_diff hb' (abs_nonneg b') hδ_nonneg
          have hright : |a| * |b' - b| ≤ 1 * δ :=
            mul_le_mul ha hb_diff (abs_nonneg (b' - b)) zero_le_one
          exact add_le_add hleft hright
    _ = 2 * δ := by ring

/--
The averaged pair-residual functional is Lipschitz in the fitted probability
table under a uniform sup-norm error bound.
-/
theorem abs_averagePairResidualFunctional_sub_le_two_delta
    {Item Model : Type*} [Fintype Item] [Nonempty Item]
    (p phat : Item → Model → ℝ) (j ℓ : Model)
    (hp : ∀ i : Item, ∀ m : Model, 0 ≤ p i m ∧ p i m ≤ 1)
    (hphat : ∀ i : Item, ∀ m : Model, 0 ≤ phat i m ∧ phat i m ≤ 1)
    (δ : ℝ)
    (hδ : ∀ i : Item, ∀ m : Model, |phat i m - p i m| ≤ δ)
    (response : Item → Model → Bool) :
    |averagePairResidualFunctional phat j ℓ response -
      averagePairResidualFunctional p j ℓ response| ≤ 2 * δ := by
  classical
  let invCard : ℝ := ((Fintype.card Item : ℝ)⁻¹)
  let term (prob : Item → Model → ℝ) (i : Item) : ℝ :=
    binaryResidual (prob i j) (response i j) *
      binaryResidual (prob i ℓ) (response i ℓ)
  have hcard_pos : 0 < (Fintype.card Item : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Item)
  have hinv_nonneg : 0 ≤ invCard :=
    inv_nonneg.mpr (le_of_lt hcard_pos)
  have hdiff :
      averagePairResidualFunctional phat j ℓ response -
        averagePairResidualFunctional p j ℓ response =
          invCard * ∑ i : Item, (term phat i - term p i) := by
    simp [averagePairResidualFunctional, invCard, term, Finset.mul_sum,
      Finset.sum_sub_distrib, mul_sub]
  have hterm :
      ∀ i : Item, |term phat i - term p i| ≤ 2 * δ := by
    intro i
    exact abs_mul_sub_mul_le_two_delta_of_abs_le_one
      (abs_binaryResidual_le_one
        (p i j) (response i j) (hp i j).1 (hp i j).2)
      (abs_binaryResidual_le_one
        (phat i ℓ) (response i ℓ) (hphat i ℓ).1 (hphat i ℓ).2)
      (abs_binaryResidual_sub_le_of_abs_prob_sub_le
        (p i j) (phat i j) (response i j) (hδ i j))
      (abs_binaryResidual_sub_le_of_abs_prob_sub_le
        (p i ℓ) (phat i ℓ) (response i ℓ) (hδ i ℓ))
  calc
    |averagePairResidualFunctional phat j ℓ response -
        averagePairResidualFunctional p j ℓ response|
        = invCard * |∑ i : Item, (term phat i - term p i)| := by
          rw [hdiff, abs_mul, abs_of_nonneg hinv_nonneg]
    _ ≤ invCard * ∑ i : Item, |term phat i - term p i| := by
          exact mul_le_mul_of_nonneg_left
            (by
              simpa using
                (Finset.abs_sum_le_sum_abs
                  (fun i : Item => term phat i - term p i)
                  Finset.univ))
            hinv_nonneg
    _ ≤ invCard * ∑ _i : Item, (2 * δ) := by
          exact mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum (fun i _hi => hterm i))
            hinv_nonneg
    _ = 2 * δ := by
          simp [invCard, Finset.sum_const, nsmul_eq_mul, hcard_pos.ne']

/-- Product-Bernoulli mass for two distinguished model coordinates. -/
def twoModelProductBernoulliMass (p q : ℝ) (response : Bool × Bool) : ℝ :=
  (if response.1 then p else 1 - p) *
    (if response.2 then q else 1 - q)

/--
Fixed-design product-null covariance-zero step for two model coordinates.

Under independent Bernoulli coordinates with probabilities `p` and `q`, the
expectation of `(Y₁-p)(Y₂-q)` is exactly zero.
-/
theorem twoModelProductBernoulli_residualCrossExpectation_zero
    (p q : ℝ) :
    (∑ b₁ : Bool, ∑ b₂ : Bool,
      twoModelProductBernoulliMass p q (b₁, b₂) *
        ((boolAsReal b₁ - p) * (boolAsReal b₂ - q))) = 0 := by
  simp [twoModelProductBernoulliMass, boolAsReal]
  ring

/--
A two-coordinate latent-mixture law with perfect positive dependence.

This law puts probability `1/2` on `(false,false)` and `1/2` on
`(true,true)`.  Both unconditional marginals are `1/2`, but the residual cross
expectation after subtracting those unconditional marginals is positive.
-/
def perfectlyCorrelatedTwoModelMixtureMass (response : Bool × Bool) : ℝ :=
  if response.1 = response.2 then (1 / 2 : ℝ) else 0

/-- The perfectly correlated two-model mixture is a finite probability law. -/
def perfectlyCorrelatedTwoModelMixtureLaw : FiniteLaw (Bool × Bool) :=
  ⟨perfectlyCorrelatedTwoModelMixtureMass, by
    constructor
    · intro response
      cases response with
      | mk b₁ b₂ =>
          cases b₁ <;> cases b₂ <;>
            norm_num [perfectlyCorrelatedTwoModelMixtureMass]
    · rw [Fintype.sum_prod_type]
      norm_num [perfectlyCorrelatedTwoModelMixtureMass]⟩

/-- Each coordinate has unconditional success probability one half. -/
theorem perfectlyCorrelatedTwoModelMixture_firstMarginal_half
    (b₁ : Bool) :
    (∑ b₂ : Bool, perfectlyCorrelatedTwoModelMixtureMass (b₁, b₂)) =
      1 / 2 := by
  cases b₁ <;> norm_num [perfectlyCorrelatedTwoModelMixtureMass]

/-- Each coordinate has unconditional success probability one half. -/
theorem perfectlyCorrelatedTwoModelMixture_secondMarginal_half
    (b₂ : Bool) :
    (∑ b₁ : Bool, perfectlyCorrelatedTwoModelMixtureMass (b₁, b₂)) =
      1 / 2 := by
  cases b₂ <;> norm_num [perfectlyCorrelatedTwoModelMixtureMass]

/--
Unconditional marginals alone do not imply zero residual covariance.

For the perfectly correlated half-half mixture, subtracting the unconditional
marginal `1/2` from each coordinate leaves residual cross expectation `1/4`.
This is the formal counterexample behind the Theorem 3 source clarification:
the zero-under-null step needs fixed-design/product-pair residuals or
conditional residuals, not just unconditional latent-mixture marginals.
-/
theorem perfectlyCorrelatedTwoModelMixture_residualCrossExpectation_quarter :
    finiteLawExpectation perfectlyCorrelatedTwoModelMixtureLaw
      (fun response : Bool × Bool =>
        (boolAsReal response.1 - 1 / 2) *
          (boolAsReal response.2 - 1 / 2)) = 1 / 4 := by
  rw [finiteLawExpectation, Fintype.sum_prod_type]
  norm_num [perfectlyCorrelatedTwoModelMixtureLaw,
    perfectlyCorrelatedTwoModelMixtureMass, boolAsReal]

/--
The fixed-design product-null covariance-zero step remains zero after
averaging over a finite item population.
-/
theorem average_twoModelProductBernoulli_residualCrossExpectation_zero
    {Item : Type*} [Fintype Item] [Nonempty Item]
    (p q : Item → ℝ) :
    ((Fintype.card Item : ℝ)⁻¹) *
      ∑ i : Item, (∑ b₁ : Bool, ∑ b₂ : Bool,
        twoModelProductBernoulliMass (p i) (q i) (b₁, b₂) *
          ((boolAsReal b₁ - p i) * (boolAsReal b₂ - q i))) = 0 := by
  have hzero :
      ∀ i : Item,
        (∑ b₁ : Bool, ∑ b₂ : Bool,
          twoModelProductBernoulliMass (p i) (q i) (b₁, b₂) *
            ((boolAsReal b₁ - p i) * (boolAsReal b₂ - q i))) = 0 := by
    intro i
    exact twoModelProductBernoulli_residualCrossExpectation_zero (p i) (q i)
  have hsum :
      (∑ i : Item, (∑ b₁ : Bool, ∑ b₂ : Bool,
        twoModelProductBernoulliMass (p i) (q i) (b₁, b₂) *
          ((boolAsReal b₁ - p i) * (boolAsReal b₂ - q i)))) = 0 :=
    Finset.sum_eq_zero (fun i _hi => hzero i)
  rw [hsum, mul_zero]

/--
Theorem 3 support lemma: for the source's averaged pair-residual functional,
the corresponding averaged fixed-design product-pair null has expectation zero.
-/
theorem averagePairResidual_productPairNullExpectation_zero
    {Item Model : Type*} [Fintype Item] [Nonempty Item]
    (p : Item → Model → ℝ) (j ℓ : Model) :
    ((Fintype.card Item : ℝ)⁻¹) *
      ∑ i : Item, (∑ b₁ : Bool, ∑ b₂ : Bool,
        twoModelProductBernoulliMass (p i j) (p i ℓ) (b₁, b₂) *
          (binaryResidual (p i j) b₁ * binaryResidual (p i ℓ) b₂)) = 0 := by
  simpa [binaryResidual] using
    average_twoModelProductBernoulli_residualCrossExpectation_zero
      (fun i : Item => p i j) (fun i : Item => p i ℓ)

/--
The source-facing product-pair marginal condition for Theorem 3.

For the averaged residual functional, this says that the fitted null has the
same two-coordinate residual expectation as the fixed-design product Bernoulli
law at each item.  It is weaker and more local than specifying a full product
law on all item/model cells, but stronger and more semantic than assuming the
expectation is simply zero.
-/
def AveragePairResidualMatchesProductPairNull
    {Item Model : Type*} [Fintype Item] [Nonempty Item] [Fintype Model]
    [Fintype (Item → Model → Bool)]
    (fittedNull : FiniteLaw (Item → Model → Bool))
    (p : Item → Model → ℝ) (j ℓ : Model) : Prop :=
  finiteLawExpectation fittedNull (averagePairResidualFunctional p j ℓ) =
    ((Fintype.card Item : ℝ)⁻¹) *
      ∑ i : Item, (∑ b₁ : Bool, ∑ b₂ : Bool,
        twoModelProductBernoulliMass (p i j) (p i ℓ) (b₁, b₂) *
          (binaryResidual (p i j) b₁ * binaryResidual (p i ℓ) b₂))

/-- Curry binary response functions from `(Item × Model)` to `Item → Model`. -/
def responseCurryEquiv (Item Model : Type*) :
    (((Item × Model) → Bool) ≃ (Item → Model → Bool)) where
  toFun response i m := response (i, m)
  invFun response coord := response coord.1 coord.2
  left_inv response := by
    funext coord
    cases coord
    rfl
  right_inv response := by
    funext i m
    rfl

/-- Full fixed-design product PMF over all item/model response cells. -/
def fixedDesignResponsePMF
    {Item Model : Type*} [Fintype Item] [Fintype Model]
    [DecidableEq Item] [DecidableEq Model]
    (p : Item → Model → ℝ)
    (hp : ∀ i : Item, ∀ m : Model, 0 ≤ p i m ∧ p i m ≤ 1) :
    PMF (Item → Model → Bool) :=
  (AppliedModelingLib.pmfPi
    (fun coord : Item × Model =>
      realBernoulliPMF (p coord.1 coord.2)
        (hp coord.1 coord.2).1 (hp coord.1 coord.2).2)).map
    (responseCurryEquiv Item Model)

/-- Full fixed-design product finite law over all item/model response cells. -/
def fixedDesignResponseLaw
    {Item Model : Type*} [Fintype Item] [Fintype Model]
    [DecidableEq Item] [DecidableEq Model]
    [Fintype (Item → Model → Bool)] [DecidableEq (Item → Model → Bool)]
    (p : Item → Model → ℝ)
    (hp : ∀ i : Item, ∀ m : Model, 0 ≤ p i m ∧ p i m ≤ 1) :
    FiniteLaw (Item → Model → Bool) :=
  finiteLawOfPMF (fixedDesignResponsePMF p hp)

/-- Full fixed-design response law generated by finite MIRT primitives. -/
def fixedDesignMIRTResponseLaw
    {K : ℕ} {Item Model : Type*} [Fintype Item] [Fintype Model]
    [DecidableEq Item] [DecidableEq Model]
    [Fintype (Item → Model → Bool)] [DecidableEq (Item → Model → Bool)]
    (link : ℝ → ℝ)
    (itemSlope : Item → Fin K → ℝ)
    (itemDifficulty : Item → ℝ)
    (modelAbility : Model → Fin K → ℝ)
    (hlink : ∀ x : ℝ, 0 ≤ link x ∧ link x ≤ 1) :
    FiniteLaw (Item → Model → Bool) :=
  fixedDesignResponseLaw
    (fun i m => MIRTSuccessProbability link itemSlope itemDifficulty modelAbility i m)
    (fun i m => hlink _)

/--
A full fixed-design independent response law implies the source's product-pair
residual marginal for every distinct model pair.
-/
theorem fixedDesignResponseLaw_matchesProductPairNull
    {Item Model : Type*} [Fintype Item] [Nonempty Item] [Fintype Model]
    [DecidableEq Item] [DecidableEq Model]
    [Fintype (Item → Model → Bool)] [DecidableEq (Item → Model → Bool)]
    (p : Item → Model → ℝ)
    (hp : ∀ i : Item, ∀ m : Model, 0 ≤ p i m ∧ p i m ≤ 1)
    {j ℓ : Model} (hjℓ : j ≠ ℓ) :
    AveragePairResidualMatchesProductPairNull
      (fixedDesignResponseLaw p hp) p j ℓ := by
  classical
  unfold AveragePairResidualMatchesProductPairNull
  change
    AppliedModelingLib.pmfExp (fixedDesignResponsePMF p hp)
      (averagePairResidualFunctional p j ℓ) =
      ((Fintype.card Item : ℝ)⁻¹) *
        ∑ i : Item, (∑ b₁ : Bool, ∑ b₂ : Bool,
          twoModelProductBernoulliMass (p i j) (p i ℓ) (b₁, b₂) *
            (binaryResidual (p i j) b₁ * binaryResidual (p i ℓ) b₂))
  unfold averagePairResidualFunctional
  rw [AppliedModelingLib.pmfExp_const_mul, AppliedModelingLib.pmfExp_univ_sum]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i _hi
  let μcoord : Item × Model → PMF Bool := fun coord =>
    realBernoulliPMF (p coord.1 coord.2)
      (hp coord.1 coord.2).1 (hp coord.1 coord.2).2
  have hcoord_ne : (i, j) ≠ (i, ℓ) := by
    intro h
    exact hjℓ (Prod.mk.inj h).2
  change
    AppliedModelingLib.pmfExp (fixedDesignResponsePMF p hp)
      (fun response : Item → Model → Bool =>
        binaryResidual (p i j) (response i j) *
          binaryResidual (p i ℓ) (response i ℓ)) =
      ∑ b₁ : Bool, ∑ b₂ : Bool,
        twoModelProductBernoulliMass (p i j) (p i ℓ) (b₁, b₂) *
          (binaryResidual (p i j) b₁ * binaryResidual (p i ℓ) b₂)
  rw [fixedDesignResponsePMF, AppliedModelingLib.pmfExp_map]
  change
    AppliedModelingLib.pmfExp (AppliedModelingLib.pmfPi μcoord)
      (fun response : Item × Model → Bool =>
        binaryResidual (p i j) (response (i, j)) *
          binaryResidual (p i ℓ) (response (i, ℓ))) =
      ∑ b₁ : Bool, ∑ b₂ : Bool,
        twoModelProductBernoulliMass (p i j) (p i ℓ) (b₁, b₂) *
          (binaryResidual (p i j) b₁ * binaryResidual (p i ℓ) b₂)
  rw [AppliedModelingLib.pmfExp_pmfPi_twoCoord_eq_pairExp
    (μ := μcoord) (i := (i, j)) (j := (i, ℓ)) hcoord_ne
    (F := fun b₁ b₂ =>
      binaryResidual (p i j) b₁ * binaryResidual (p i ℓ) b₂)]
  unfold AppliedModelingLib.pmfPairExp AppliedModelingLib.pmfExp
  refine Finset.sum_congr rfl ?_
  intro b₁ _hb₁
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro b₂ _hb₂
  cases b₁ <;> cases b₂ <;>
    simp [μcoord, twoModelProductBernoulliMass, binaryResidual, boolAsReal] <;>
    ring

/-- Item-row law generated by a finite MIRT null. -/
def MIRTItemLaw {K : ℕ} {Item Model : Type*} [Fintype Model]
    (link : ℝ → ℝ)
    (itemSlope : Item → Fin K → ℝ)
    (itemDifficulty : Item → ℝ)
    (modelAbility : Model → Fin K → ℝ)
    (i : Item) (response : Model → Bool) : ℝ :=
  productBernoulliMass
    (fun j : Model =>
      MIRTSuccessProbability link itemSlope itemDifficulty modelAbility i j)
    response

/--
Definition 2.1 / finite fixed-design MIRT null family.

The law maps each item to a product-Bernoulli law over model responses, with
coordinate probabilities generated by latent item/model vectors and a link.
-/
def IsMIRTNullLaw {K : ℕ} {Item Model : Type*} [Fintype Model]
    (Q : Item → (Model → Bool) → ℝ) : Prop :=
  ∃ link : ℝ → ℝ,
  ∃ itemSlope : Item → Fin K → ℝ,
  ∃ itemDifficulty : Item → ℝ,
  ∃ modelAbility : Model → Fin K → ℝ,
    Q = MIRTItemLaw link itemSlope itemDifficulty modelAbility

/-- Each item row of a MIRT law is product Bernoulli after conditioning. -/
theorem MIRTItemLaw_isProductBernoulli {K : ℕ} {Item Model : Type*}
    [Fintype Model]
    (link : ℝ → ℝ)
    (itemSlope : Item → Fin K → ℝ)
    (itemDifficulty : Item → ℝ)
    (modelAbility : Model → Fin K → ℝ)
    (i : Item) :
    IsProductBernoulliLaw
      (MIRTItemLaw link itemSlope itemDifficulty modelAbility i) := by
  exact ⟨fun j : Model =>
    MIRTSuccessProbability link itemSlope itemDifficulty modelAbility i j, rfl⟩

/-- Extend a finite latent vector by appending a zero coordinate. -/
def extendFinVectorZero {K : ℕ} (x : Fin K → ℝ) : Fin (K + 1) → ℝ :=
  Fin.snoc x 0

/-- Appending a zero coordinate preserves finite dot products. -/
theorem finiteDot_extendFinVectorZero_eq {K : ℕ}
    (a θ : Fin K → ℝ) :
    finiteDot (extendFinVectorZero a) (extendFinVectorZero θ) =
      finiteDot a θ := by
  unfold finiteDot extendFinVectorZero
  rw [Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

/-- Every `K`-dimensional MIRT null law is also `(K+1)`-dimensional. -/
theorem IsMIRTNullLaw_succ_of_IsMIRTNullLaw
    {K : ℕ} {Item Model : Type*} [Fintype Model]
    {Q : Item → (Model → Bool) → ℝ}
    (hQ : IsMIRTNullLaw (K := K) Q) :
    IsMIRTNullLaw (K := K + 1) Q := by
  rcases hQ with ⟨link, itemSlope, itemDifficulty, modelAbility, rfl⟩
  refine ⟨link, fun i => extendFinVectorZero (itemSlope i),
    itemDifficulty, fun j => extendFinVectorZero (modelAbility j), ?_⟩
  funext i response
  simp [MIRTItemLaw, MIRTSuccessProbability, finiteDot_extendFinVectorZero_eq]

/--
The deterministic vertex law concentrated at `ω₀`.

This is the finite-law analogue of the point `p = y` used in the source proof
of the mixture theorem.
-/
def vertexLaw {Ω : Type*} [DecidableEq Ω] (ω₀ ω : Ω) : ℝ :=
  if ω = ω₀ then 1 else 0

/--
The vertex-mixture law obtained by putting mass `P ω₀` on the deterministic
vertex law concentrated at `ω₀`.
-/
def vertexMixtureLaw {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ ω₀ : Ω, P ω₀ * vertexLaw ω₀ ω

/--
Theorem 3.1 / mixture representation, finite vertex form:
placing mass `P y` on each deterministic vertex `y` recovers `P`.

This is the closed algebraic core of the source theorem's claim that any law on
`{0,1}^m` is a finite mixture of conditionally independent Bernoulli vertices.
-/
theorem vertexMixtureLaw_eq {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : Ω → ℝ) (ω : Ω) :
    vertexMixtureLaw P ω = P ω := by
  classical
  simp [vertexMixtureLaw, vertexLaw]

/-- The set of deterministic vertices used with nonzero mixture weight. -/
def vertexMixtureSupport {Ω : Type*} [Fintype Ω]
    (P : Ω → ℝ) : Finset Ω :=
  Finset.univ.filter (fun ω : Ω => P ω ≠ 0)

/-- The vertex-mixture support has no more points than the underlying space. -/
theorem vertexMixtureSupport_card_le {Ω : Type*} [Fintype Ω]
    (P : Ω → ℝ) :
    (vertexMixtureSupport P).card ≤ Fintype.card Ω := by
  classical
  unfold vertexMixtureSupport
  simpa using Finset.card_filter_le Finset.univ (fun ω : Ω => P ω ≠ 0)

/-- Boolean response vectors over `m` models have cardinality `2^m`. -/
theorem boolVector_card (m : ℕ) :
    Fintype.card (Fin m → Bool) = 2 ^ m := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]

/--
Theorem 3.1 support-size clause for binary response vectors:
the finite vertex representation uses at most `2^m` nonzero vertices.
-/
theorem vertexMixtureSupport_bool_card_le (m : ℕ)
    (P : (Fin m → Bool) → ℝ) :
    (vertexMixtureSupport P).card ≤ 2 ^ m := by
  simpa [boolVector_card] using vertexMixtureSupport_card_le P

/-! ## Nested null families and attained excess -/

/-- A null ladder is a nested sequence of source null families. -/
def NullLadder {Law : Type*} (N : ℕ → Set Law) : Prop :=
  ∀ K : ℕ, N K ⊆ N (K + 1)

/-- The `K`-dimensional MIRT null families. -/
def MIRTNullFamily (Item Model : Type*) [Fintype Model]
    (K : ℕ) : Set (Item → (Model → Bool) → ℝ) :=
  { Q | IsMIRTNullLaw (K := K) Q }

/-- Lemma 6 / nestedness of ability nulls, concrete MIRT form. -/
theorem MIRTNullFamily_nested (Item Model : Type*) [Fintype Model] :
    NullLadder (fun K : ℕ => MIRTNullFamily Item Model K) := by
  intro K Q hQ
  exact IsMIRTNullLaw_succ_of_IsMIRTNullLaw hQ

/-- Discrepancy values obtained by comparing a fixed law `P` to laws in `S`. -/
def discrepancyValues {Law : Type*}
    (D : Law → Law → ℝ) (P : Law) (S : Set Law) : Set ℝ :=
  { x : ℝ | ∃ Q : Law, Q ∈ S ∧ x = D P Q }

/-- `x` is an attained minimal value of a set of real discrepancies. -/
def IsAttainedMinimum (S : Set ℝ) (x : ℝ) : Prop :=
  x ∈ S ∧ ∀ y : ℝ, y ∈ S → x ≤ y

/--
`x` is the infimum value of a set of real discrepancies, stated through the
lower-bound and approximating-sequence properties used in the source draft.
-/
def IsInfimumValue (S : Set ℝ) (x : ℝ) : Prop :=
  (∀ y : ℝ, y ∈ S → x ≤ y) ∧
    ∀ ε : ℝ, 0 < ε → ∃ y : ℝ, y ∈ S ∧ y ≤ x + ε

/--
Proposition 3.2 / monotone absorption, attained-minimum form.

If the `K`th null family is contained in the `(K+1)`st family and both
minima are attained, then the minimal discrepancy at level `K+1` is no larger
than the minimal discrepancy at level `K`.
-/
theorem attainedMinimalExcess_nonincreasing {Law : Type*}
    (D : Law → Law → ℝ) (P : Law) (N : ℕ → Set Law) (K : ℕ)
    (hNested : NullLadder N)
    {excessK excessSucc : ℝ}
    (hK :
      IsAttainedMinimum (discrepancyValues D P (N K)) excessK)
    (hSucc :
      IsAttainedMinimum (discrepancyValues D P (N (K + 1))) excessSucc) :
    excessSucc ≤ excessK := by
  rcases hK.1 with ⟨Q, hQ, hQeq⟩
  exact hSucc.2 excessK ⟨Q, hNested K hQ, hQeq⟩

/--
Proposition 3.2 / monotone absorption, infimum form.

If the `K`th null family is contained in the `(K+1)`st family and both excess
values are infima in the lower-bound/approximating-sequence sense, then the
level `K+1` excess is no larger than the level `K` excess.
-/
theorem infimumMinimalExcess_nonincreasing {Law : Type*}
    (D : Law → Law → ℝ) (P : Law) (N : ℕ → Set Law) (K : ℕ)
    (hNested : NullLadder N)
    {excessK excessSucc : ℝ}
    (hK :
      IsInfimumValue (discrepancyValues D P (N K)) excessK)
    (hSucc :
      IsInfimumValue (discrepancyValues D P (N (K + 1))) excessSucc) :
    excessSucc ≤ excessK := by
  by_contra hnot
  have hlt : excessK < excessSucc := lt_of_not_ge hnot
  let ε : ℝ := (excessSucc - excessK) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    nlinarith
  rcases hK.2 ε hε with ⟨y, hy, hyle⟩
  rcases hy with ⟨Q, hQ, hQeq⟩
  have hySucc : y ∈ discrepancyValues D P (N (K + 1)) :=
    ⟨Q, hNested K hQ, hQeq⟩
  have hle : excessSucc ≤ y := hSucc.1 y hySucc
  have hupper : excessSucc ≤ excessK + ε := le_trans hle hyle
  dsimp [ε] at hupper
  nlinarith

/-! ## Residual dependence under a fitted null -/

/--
A discrepancy controls bounded expectations when it upper-bounds the difference
in expectation of every function bounded by one in absolute value.
-/
def ControlsBoundedExpectations {Ω : Type*} [Fintype Ω]
    (D : FiniteLaw Ω → FiniteLaw Ω → ℝ) : Prop :=
  ∀ μ ν : FiniteLaw Ω, ∀ f : Ω → ℝ,
    (∀ ω : Ω, |f ω| ≤ 1) →
      |finiteLawExpectation μ f - finiteLawExpectation ν f| ≤ D μ ν

/--
Finite L1 discrepancy between two finite laws.

This is twice total variation under the common `TV = 1/2 * L1` convention, and
therefore is a source-valid example of a discrepancy controlling bounded
expectations.
-/
def finiteL1Discrepancy {Ω : Type*} [Fintype Ω]
    (μ ν : FiniteLaw Ω) : ℝ :=
  ∑ ω : Ω, |μ.1 ω - ν.1 ω|

/-- Finite L1 discrepancy controls expectations of functions bounded by one. -/
theorem finiteL1Discrepancy_controlsBoundedExpectations
    {Ω : Type*} [Fintype Ω] :
    ControlsBoundedExpectations (finiteL1Discrepancy (Ω := Ω)) := by
  intro μ ν f hf
  have hdiff :
      finiteLawExpectation μ f - finiteLawExpectation ν f =
        ∑ ω : Ω, (μ.1 ω - ν.1 ω) * f ω := by
    simp [finiteLawExpectation, Finset.sum_sub_distrib, sub_mul]
  calc
    |finiteLawExpectation μ f - finiteLawExpectation ν f|
        = |∑ ω : Ω, (μ.1 ω - ν.1 ω) * f ω| := by rw [hdiff]
    _ ≤ ∑ ω : Ω, |(μ.1 ω - ν.1 ω) * f ω| := by
          simpa using
            (Finset.abs_sum_le_sum_abs
              (fun ω : Ω => (μ.1 ω - ν.1 ω) * f ω)
              Finset.univ)
    _ ≤ ∑ ω : Ω, |μ.1 ω - ν.1 ω| := by
          exact Finset.sum_le_sum (fun ω _hω => by
            rw [abs_mul]
            exact mul_le_of_le_one_right (abs_nonneg _) (hf ω))

/--
Theorem 3 / residual-dependence control, fixed-design form.

Once the fitted null has zero expectation for the centered residual cross-term,
any discrepancy that controls bounded expectations bounds the residual
dependence under the observed law.
-/
theorem expectation_abs_le_of_controlsBoundedExpectations
    {Ω : Type*} [Fintype Ω]
    {D : FiniteLaw Ω → FiniteLaw Ω → ℝ}
    (hD : ControlsBoundedExpectations D)
    (observed fittedNull : FiniteLaw Ω) (residualCrossTerm : Ω → ℝ)
    (hBounded : ∀ ω : Ω, |residualCrossTerm ω| ≤ 1)
    (hNullZero : finiteLawExpectation fittedNull residualCrossTerm = 0) :
    |finiteLawExpectation observed residualCrossTerm| ≤ D observed fittedNull := by
  have hcontrol :=
    hD observed fittedNull residualCrossTerm hBounded
  simpa [hNullZero] using hcontrol

/-! ## Empirical residual convergence abstraction -/

/-- Elementary real-sequence convergence predicate used for source-facing remarks. -/
def SequenceConvergesTo (x : ℕ → ℝ) (limit : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |x n - limit| ≤ ε

/-- Multiplying by a fixed real constant preserves convergence to zero. -/
theorem sequence_converges_to_zero_const_mul
    (x : ℕ → ℝ) (c : ℝ)
    (hx : SequenceConvergesTo x 0) :
    SequenceConvergesTo (fun n : ℕ => c * x n) 0 := by
  intro ε hε
  by_cases hc : c = 0
  · refine ⟨0, ?_⟩
    intro n _hn
    simpa [hc] using le_of_lt hε
  · have hscale_pos : 0 < ε / |c| :=
      div_pos hε (abs_pos.mpr hc)
    rcases hx (ε / |c|) hscale_pos with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    have hxn := hN n hn
    calc
      |c * x n - 0| = |c| * |x n - 0| := by
        simp [abs_mul]
      _ ≤ |c| * (ε / |c|) :=
        mul_le_mul_of_nonneg_left hxn (abs_nonneg c)
      _ = ε := by
        field_simp [abs_ne_zero.mpr hc]

/--
If empirical residual correlations are bounded in absolute value by an error
term that converges to zero, then the residual correlations converge to zero.
-/
theorem sequence_converges_to_zero_of_abs_le
    (corr bound : ℕ → ℝ)
    (hbound : ∀ n : ℕ, |corr n| ≤ bound n)
    (hlim : SequenceConvergesTo bound 0) :
    SequenceConvergesTo corr 0 := by
  intro ε hε
  rcases hlim ε hε with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  calc
    |corr n - 0| = |corr n| := by simp
    _ ≤ bound n := hbound n
    _ ≤ |bound n| := le_abs_self (bound n)
    _ = |bound n - 0| := by simp
    _ ≤ ε := hN n hn

/--
If a sequence differs from a zero-convergent sequence by a zero-convergent
error term, then it also converges to zero.
-/
theorem sequence_converges_to_zero_of_abs_sub_le
    (x y err : ℕ → ℝ)
    (hbound : ∀ n : ℕ, |x n - y n| ≤ err n)
    (hy : SequenceConvergesTo y 0)
    (herr : SequenceConvergesTo err 0) :
    SequenceConvergesTo x 0 := by
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  rcases hy (ε / 2) hhalf with ⟨Ny, hNy⟩
  rcases herr (ε / 2) hhalf with ⟨Ne, hNe⟩
  refine ⟨max Ny Ne, ?_⟩
  intro n hn
  have hy_n : |y n - 0| ≤ ε / 2 :=
    hNy n (le_trans (Nat.le_max_left Ny Ne) hn)
  have herr_n : |err n - 0| ≤ ε / 2 :=
    hNe n (le_trans (Nat.le_max_right Ny Ne) hn)
  have htriangle : |x n| ≤ |x n - y n| + |y n| := by
    have hdecomp : (x n - y n) + y n = x n := by ring
    simpa [hdecomp] using abs_add_le (x n - y n) (y n)
  calc
    |x n - 0| = |x n| := by simp
    _ ≤ |x n - y n| + |y n| := htriangle
    _ ≤ err n + |y n| := by
          linarith [hbound n]
    _ ≤ |err n| + |y n| := by
          linarith [le_abs_self (err n)]
    _ = |err n - 0| + |y n - 0| := by simp
    _ ≤ ε / 2 + ε / 2 := add_le_add herr_n hy_n
    _ = ε := by ring

/--
A finite-law expectation changes by at most a pointwise uniform bound on the
integrand difference.
-/
theorem finiteLawExpectation_abs_sub_le_of_pointwise
    {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (f g : Ω → ℝ) (δ : ℝ)
    (hδ_nonneg : 0 ≤ δ)
    (hpoint : ∀ ω : Ω, |f ω - g ω| ≤ δ) :
    |finiteLawExpectation μ f - finiteLawExpectation μ g| ≤ δ := by
  have hdiff :
      finiteLawExpectation μ f - finiteLawExpectation μ g =
        ∑ ω : Ω, μ.1 ω * (f ω - g ω) := by
    simp [finiteLawExpectation, Finset.sum_sub_distrib, mul_sub]
  calc
    |finiteLawExpectation μ f - finiteLawExpectation μ g|
        = |∑ ω : Ω, μ.1 ω * (f ω - g ω)| := by rw [hdiff]
    _ ≤ ∑ ω : Ω, |μ.1 ω * (f ω - g ω)| := by
          simpa using
            (Finset.abs_sum_le_sum_abs
              (fun ω : Ω => μ.1 ω * (f ω - g ω))
              Finset.univ)
    _ = ∑ ω : Ω, μ.1 ω * |f ω - g ω| := by
          apply Finset.sum_congr rfl
          intro ω _hω
          rw [abs_mul, abs_of_nonneg (μ.2.1 ω)]
    _ ≤ ∑ ω : Ω, μ.1 ω * δ := by
          exact Finset.sum_le_sum (fun ω _hω =>
            mul_le_mul_of_nonneg_left (hpoint ω) (μ.2.1 ω))
    _ = δ := by
          calc
            (∑ ω : Ω, μ.1 ω * δ) = (∑ ω : Ω, μ.1 ω) * δ := by
              rw [← Finset.sum_mul]
            _ = δ := by
              rw [μ.2.2]
              ring

/--
Theorem 3 / residual dependence vanishes along a null ladder.

If the fitted nulls approach the observed law in a discrepancy controlling
bounded expectations, and each fitted null has zero expectation for the
bounded residual functional `g_K`, then the observed residual functional
converges to zero.
-/
theorem residualDependence_converges_to_zero_of_controlsBoundedExpectations
    {Ω : Type*} [Fintype Ω]
    {D : FiniteLaw Ω → FiniteLaw Ω → ℝ}
    (hD : ControlsBoundedExpectations D)
    (observed : FiniteLaw Ω)
    (fittedNull : ℕ → FiniteLaw Ω)
    (residualFunctional : ℕ → Ω → ℝ)
    (hBounded : ∀ K : ℕ, ∀ ω : Ω, |residualFunctional K ω| ≤ 1)
    (hNullZero :
      ∀ K : ℕ,
        finiteLawExpectation (fittedNull K) (residualFunctional K) = 0)
    (hlim :
      SequenceConvergesTo (fun K : ℕ => D observed (fittedNull K)) 0) :
    SequenceConvergesTo
      (fun K : ℕ => finiteLawExpectation observed (residualFunctional K)) 0 :=
  sequence_converges_to_zero_of_abs_le
    (fun K : ℕ => finiteLawExpectation observed (residualFunctional K))
    (fun K : ℕ => D observed (fittedNull K))
    (fun K : ℕ =>
      expectation_abs_le_of_controlsBoundedExpectations
        hD observed (fittedNull K) (residualFunctional K)
        (hBounded K) (hNullZero K))
    hlim

/--
Theorem 3 specialized to the source's averaged pairwise binary residual.

For a fixed pair of models, if the fitted nulls have zero expectation for the
averaged residual functional and converge to the observed law in a discrepancy
controlling bounded expectations, then the observed averaged residual
functional converges to zero.
-/
theorem averagePairResidual_converges_to_zero_of_controlsBoundedExpectations
    {Item Model : Type*} [Fintype Item] [Nonempty Item] [Fintype Model]
    [Fintype (Item → Model → Bool)]
    {D :
      FiniteLaw (Item → Model → Bool) →
        FiniteLaw (Item → Model → Bool) → ℝ}
    (hD : ControlsBoundedExpectations D)
    (observed : FiniteLaw (Item → Model → Bool))
    (fittedNull : ℕ → FiniteLaw (Item → Model → Bool))
    (p : ℕ → Item → Model → ℝ) (j ℓ : Model)
    (hp : ∀ K : ℕ, ∀ i : Item, ∀ m : Model, 0 ≤ p K i m ∧ p K i m ≤ 1)
    (hNullZero :
      ∀ K : ℕ,
        finiteLawExpectation (fittedNull K)
          (averagePairResidualFunctional (p K) j ℓ) = 0)
    (hlim :
      SequenceConvergesTo (fun K : ℕ => D observed (fittedNull K)) 0) :
    SequenceConvergesTo
      (fun K : ℕ =>
        finiteLawExpectation observed
          (averagePairResidualFunctional (p K) j ℓ)) 0 :=
  residualDependence_converges_to_zero_of_controlsBoundedExpectations
    hD observed fittedNull
    (fun K : ℕ => averagePairResidualFunctional (p K) j ℓ)
    (fun K : ℕ =>
      averagePairResidualFunctional_abs_le_one (p K) j ℓ (hp K))
    hNullZero hlim

/--
Theorem 3 with a source-natural product-pair marginal premise.

Instead of assuming that each fitted null has zero averaged pair-residual
expectation, this version assumes the fitted null agrees with the
fixed-design product Bernoulli pair marginal.  The zero expectation is then
derived from the product-null support lemma above.
-/
theorem averagePairResidual_converges_to_zero_of_productPairNullMarginals
    {Item Model : Type*} [Fintype Item] [Nonempty Item] [Fintype Model]
    [Fintype (Item → Model → Bool)]
    {D :
      FiniteLaw (Item → Model → Bool) →
        FiniteLaw (Item → Model → Bool) → ℝ}
    (hD : ControlsBoundedExpectations D)
    (observed : FiniteLaw (Item → Model → Bool))
    (fittedNull : ℕ → FiniteLaw (Item → Model → Bool))
    (p : ℕ → Item → Model → ℝ) (j ℓ : Model)
    (hp : ∀ K : ℕ, ∀ i : Item, ∀ m : Model, 0 ≤ p K i m ∧ p K i m ≤ 1)
    (hProductPair :
      ∀ K : ℕ,
        AveragePairResidualMatchesProductPairNull (fittedNull K) (p K) j ℓ)
    (hlim :
      SequenceConvergesTo (fun K : ℕ => D observed (fittedNull K)) 0) :
    SequenceConvergesTo
      (fun K : ℕ =>
        finiteLawExpectation observed
          (averagePairResidualFunctional (p K) j ℓ)) 0 :=
  averagePairResidual_converges_to_zero_of_controlsBoundedExpectations
    hD observed fittedNull p j ℓ hp
    (fun K : ℕ => by
      exact (hProductPair K).trans
        (averagePairResidual_productPairNullExpectation_zero (p K) j ℓ))
    hlim

/--
Theorem 3 for concrete fixed-design product response laws.

This version constructs the fitted null at each `K` as the full independent
product law over all item/model cells.  For distinct models, the required
product-pair residual marginal is derived from that full law.
-/
theorem averagePairResidual_converges_to_zero_of_fixedDesignProductNulls
    {Item Model : Type*} [Fintype Item] [Nonempty Item] [Fintype Model]
    [DecidableEq Item] [DecidableEq Model]
    [Fintype (Item → Model → Bool)] [DecidableEq (Item → Model → Bool)]
    {D :
      FiniteLaw (Item → Model → Bool) →
        FiniteLaw (Item → Model → Bool) → ℝ}
    (hD : ControlsBoundedExpectations D)
    (observed : FiniteLaw (Item → Model → Bool))
    (p : ℕ → Item → Model → ℝ) (j ℓ : Model)
    (hjℓ : j ≠ ℓ)
    (hp : ∀ K : ℕ, ∀ i : Item, ∀ m : Model, 0 ≤ p K i m ∧ p K i m ≤ 1)
    (hlim :
      SequenceConvergesTo
        (fun K : ℕ =>
          D observed (fixedDesignResponseLaw (p K) (hp K)))
        0) :
    SequenceConvergesTo
      (fun K : ℕ =>
        finiteLawExpectation observed
          (averagePairResidualFunctional (p K) j ℓ)) 0 :=
  averagePairResidual_converges_to_zero_of_productPairNullMarginals
    hD observed
    (fun K : ℕ => fixedDesignResponseLaw (p K) (hp K))
    p j ℓ hp
    (fun K : ℕ =>
      fixedDesignResponseLaw_matchesProductPairNull (p K) (hp K) hjℓ)
    hlim

/--
Theorem 3 for fitted fixed-design MIRT nulls.

This instantiates the full fixed-design product response law with the MIRT
success probabilities from Definition 2.1.
-/
theorem averagePairResidual_converges_to_zero_of_fixedDesignMIRTNulls
    {Item Model : Type*} [Fintype Item] [Nonempty Item] [Fintype Model]
    [DecidableEq Item] [DecidableEq Model]
    [Fintype (Item → Model → Bool)] [DecidableEq (Item → Model → Bool)]
    {D :
      FiniteLaw (Item → Model → Bool) →
        FiniteLaw (Item → Model → Bool) → ℝ}
    (hD : ControlsBoundedExpectations D)
    (observed : FiniteLaw (Item → Model → Bool))
    (dim : ℕ → ℕ)
    (link : (K : ℕ) → ℝ → ℝ)
    (itemSlope : (K : ℕ) → Item → Fin (dim K) → ℝ)
    (itemDifficulty : (K : ℕ) → Item → ℝ)
    (modelAbility : (K : ℕ) → Model → Fin (dim K) → ℝ)
    (j ℓ : Model)
    (hjℓ : j ≠ ℓ)
    (hlink : ∀ K : ℕ, ∀ x : ℝ, 0 ≤ link K x ∧ link K x ≤ 1)
    (hlim :
      SequenceConvergesTo
        (fun K : ℕ =>
          D observed
            (fixedDesignMIRTResponseLaw (link K) (itemSlope K)
              (itemDifficulty K) (modelAbility K) (hlink K)))
        0) :
    SequenceConvergesTo
      (fun K : ℕ =>
        finiteLawExpectation observed
          (averagePairResidualFunctional
            (fun i m =>
              MIRTSuccessProbability (link K) (itemSlope K)
                (itemDifficulty K) (modelAbility K) i m)
            j ℓ))
        0 :=
  averagePairResidual_converges_to_zero_of_fixedDesignProductNulls
    hD observed
    (fun K i m =>
      MIRTSuccessProbability (link K) (itemSlope K)
        (itemDifficulty K) (modelAbility K) i m)
    j ℓ hjℓ
    (fun K i m => hlink K _)
    hlim

/--
Appendix Remark B.3 deterministic fitted-probability stability.

If the model-implied pair-residual expectation converges to zero and the fitted
probability table is uniformly consistent for the model-implied table, then
the pair-residual expectation computed using fitted probabilities also
converges to zero.
-/
theorem fittedPairResidualExpectation_converges_to_zero_of_uniform_probability_error
    {Item Model : Type*} [Fintype Item] [Nonempty Item] [Fintype Model]
    [Fintype (Item → Model → Bool)]
    (observed : FiniteLaw (Item → Model → Bool))
    (p phat : ℕ → Item → Model → ℝ) (j ℓ : Model)
    (hp : ∀ K : ℕ, ∀ i : Item, ∀ m : Model, 0 ≤ p K i m ∧ p K i m ≤ 1)
    (hphat : ∀ K : ℕ, ∀ i : Item, ∀ m : Model, 0 ≤ phat K i m ∧ phat K i m ≤ 1)
    (uniformError : ℕ → ℝ)
    (herror_nonneg : ∀ K : ℕ, 0 ≤ uniformError K)
    (herror :
      ∀ K : ℕ, ∀ i : Item, ∀ m : Model,
        |phat K i m - p K i m| ≤ uniformError K)
    (hsource :
      SequenceConvergesTo
        (fun K : ℕ =>
          finiteLawExpectation observed
            (averagePairResidualFunctional (p K) j ℓ))
        0)
    (herror_lim : SequenceConvergesTo uniformError 0) :
    SequenceConvergesTo
      (fun K : ℕ =>
        finiteLawExpectation observed
          (averagePairResidualFunctional (phat K) j ℓ))
      0 := by
  refine sequence_converges_to_zero_of_abs_sub_le
    (fun K : ℕ =>
      finiteLawExpectation observed
        (averagePairResidualFunctional (phat K) j ℓ))
    (fun K : ℕ =>
      finiteLawExpectation observed
        (averagePairResidualFunctional (p K) j ℓ))
    (fun K : ℕ => 2 * uniformError K)
    ?_ hsource
    (sequence_converges_to_zero_const_mul uniformError 2 herror_lim)
  intro K
  exact finiteLawExpectation_abs_sub_le_of_pointwise observed
    (averagePairResidualFunctional (phat K) j ℓ)
    (averagePairResidualFunctional (p K) j ℓ)
    (2 * uniformError K)
    (mul_nonneg (by norm_num) (herror_nonneg K))
    (fun response =>
      abs_averagePairResidualFunctional_sub_le_two_delta
        (p K) (phat K) j ℓ (hp K) (hphat K)
        (uniformError K) (herror K) response)

/-! ## Debiased residuals -/

/-- The model-specific average residual across the finite item population. -/
def meanResidual {Item Model : Type*} [Fintype Item]
    (e : Item → Model → ℝ) (j : Model) : ℝ :=
  ((Fintype.card Item : ℝ)⁻¹) * ∑ i : Item, e i j

/-- Residual after subtracting the model-specific sample mean across items. -/
def debiasedResidual {Item Model : Type*} [Fintype Item]
    (e : Item → Model → ℝ) (i : Item) (j : Model) : ℝ :=
  e i j - meanResidual e j

/--
Proposition B.1 / residual debiasing, finite-sample identity:
demeaned residuals have zero item-sum for every model.
-/
theorem debiasedResidual_sum_eq_zero
    {Item Model : Type*} [Fintype Item] [Nonempty Item]
    (e : Item → Model → ℝ) (j : Model) :
    (∑ i : Item, debiasedResidual e i j) = 0 := by
  classical
  have hcard_pos : 0 < (Fintype.card Item : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Item)
  have hcard_ne : (Fintype.card Item : ℝ) ≠ 0 := ne_of_gt hcard_pos
  simp [debiasedResidual, meanResidual, Finset.sum_sub_distrib, Finset.sum_const,
    nsmul_eq_mul, hcard_ne]

/-! ## Population-relative null fits -/

/-- `Q` is a population-specific best-fitting null for the discrepancy `D`. -/
def IsPopulationSpecificTarget {Fit : Type*} (D : Fit → ℝ) (Q : Fit) : Prop :=
  ∀ R : Fit, D Q ≤ D R

/-- The two cells in the full finite witness for population relativity. -/
inductive LargePopulationCell
  | focal
  | context
  deriving DecidableEq, Fintype

/-- The single focal cell retained in the restricted population. -/
inductive SmallPopulationCell
  | focal
  deriving DecidableEq, Fintype

/-- Sum over the two cells in the full finite witness. -/
theorem sum_largePopulationCell (f : LargePopulationCell → ℝ) :
    (∑ c : LargePopulationCell, f c) =
      f LargePopulationCell.focal + f LargePopulationCell.context := by
  classical
  have huniv :
      (Finset.univ : Finset LargePopulationCell) =
        {LargePopulationCell.focal, LargePopulationCell.context} := by
    ext c
    cases c <;> simp
  simp [huniv]

/-- Sum over the single cell in the restricted finite witness. -/
theorem sum_smallPopulationCell (f : SmallPopulationCell → ℝ) :
    (∑ c : SmallPopulationCell, f c) = f SmallPopulationCell.focal := by
  classical
  have huniv :
      (Finset.univ : Finset SmallPopulationCell) =
        {SmallPopulationCell.focal} := by
    ext c
    cases c
    simp
  simp [huniv]

/--
Two candidate null fits on the larger population.

`contextFit` fits the context cell well but misses the focal cell; `focalFit`
fits the focal cell well but badly misses the context cell.
-/
inductive LargePopulationNullFit
  | contextFit
  | focalFit
  deriving DecidableEq, Fintype

/-- Two candidate null fits available when fitting only the restricted population. -/
inductive SmallPopulationNullFit
  | low
  | high
  deriving DecidableEq, Fintype

/-- The observed response-probability vector on the larger population. -/
def largePopulationObserved : LargePopulationCell → ℝ
  | LargePopulationCell.focal => 0
  | LargePopulationCell.context => 0

/-- The observed response-probability vector on the restricted population. -/
def smallPopulationObserved : SmallPopulationCell → ℝ
  | SmallPopulationCell.focal => 0

/-- Candidate null predictions on the larger population. -/
def largePopulationPrediction :
    LargePopulationNullFit → LargePopulationCell → ℝ
  | LargePopulationNullFit.contextFit, LargePopulationCell.focal => 1
  | LargePopulationNullFit.contextFit, LargePopulationCell.context => 0
  | LargePopulationNullFit.focalFit, LargePopulationCell.focal => 0
  | LargePopulationNullFit.focalFit, LargePopulationCell.context => 10

/-- Candidate null predictions on the restricted population. -/
def smallPopulationPrediction :
    SmallPopulationNullFit → SmallPopulationCell → ℝ
  | SmallPopulationNullFit.low, SmallPopulationCell.focal => 0
  | SmallPopulationNullFit.high, SmallPopulationCell.focal => 1

/-- Restrict a full-population fit to the focal restricted population. -/
def restrictLargePopulationFit :
    LargePopulationNullFit → SmallPopulationNullFit
  | LargePopulationNullFit.contextFit => SmallPopulationNullFit.high
  | LargePopulationNullFit.focalFit => SmallPopulationNullFit.low

/-- Squared-error discrepancy for the larger population witness. -/
def largePopulationSquaredDiscrepancy
    (Q : LargePopulationNullFit) : ℝ :=
  ∑ c : LargePopulationCell,
    (largePopulationPrediction Q c - largePopulationObserved c) ^ 2

/-- Squared-error discrepancy for the restricted population witness. -/
def smallPopulationSquaredDiscrepancy
    (Q : SmallPopulationNullFit) : ℝ :=
  ∑ c : SmallPopulationCell,
    (smallPopulationPrediction Q c - smallPopulationObserved c) ^ 2

/-- In the full population, the context-fitting null has lower squared error. -/
theorem largePopulation_contextFit_isTarget :
    IsPopulationSpecificTarget largePopulationSquaredDiscrepancy
      LargePopulationNullFit.contextFit := by
  intro Q
  cases Q <;>
    norm_num [sum_largePopulationCell, largePopulationSquaredDiscrepancy,
      largePopulationPrediction, largePopulationObserved]

/-- In the restricted population, the low focal prediction is the best fit. -/
theorem smallPopulation_low_isTarget :
    IsPopulationSpecificTarget smallPopulationSquaredDiscrepancy
      SmallPopulationNullFit.low := by
  intro Q
  cases Q <;>
    norm_num [sum_smallPopulationCell, smallPopulationSquaredDiscrepancy,
      smallPopulationPrediction, smallPopulationObserved]

/--
Proposition 4.1 / population relativity, concrete finite witness.

The full-population best fit restricts to `high`, while the best fit obtained
by fitting only the restricted population is `low`.
-/
theorem populationRelativity_concreteWitness :
    IsPopulationSpecificTarget largePopulationSquaredDiscrepancy
        LargePopulationNullFit.contextFit ∧
      IsPopulationSpecificTarget smallPopulationSquaredDiscrepancy
        SmallPopulationNullFit.low ∧
      restrictLargePopulationFit LargePopulationNullFit.contextFit ≠
        SmallPopulationNullFit.low := by
  refine ⟨largePopulation_contextFit_isTarget,
    smallPopulation_low_isTarget, ?_⟩
  simp [restrictLargePopulationFit]

/-! ## Heterogeneity stability abstraction -/

/--
The squared prediction-distance form of the epsilon-equivalence set.

The source theorem states the set in terms of prediction error at most
`epsilon`; this squared form avoids unnecessary square roots in the Lean
statement.
-/
def IsEpsilonEquivalent
    {State : Type*} (predictionSq : State → ℝ) (ε : ℝ) (z : State) : Prop :=
  predictionSq z ≤ ε ^ 2

/--
The source theorem's "for all sufficiently small `ε`" condition, expressed at
one fixed value of `ε`: every `ε`-equivalent representation lies in the local
quotient chart where the Taylor and identifiability conditions apply.
-/
def EpsilonEquivalentInsideChart
    {State : Type*} (inChart : State → Prop)
    (predictionSq : State → ℝ) (ε : ℝ) : Prop :=
  ∀ z : State, IsEpsilonEquivalent predictionSq ε z → inChart z

/--
Restricted strong identification at heterogeneity scale `h`.

After quotienting by model invariances, local squared prediction error
lower-bounds squared parameter distance by `c * h`.
-/
def RestrictedStrongIdentification
    {State : Type*} (predictionSq parameterSq : State → ℝ) (c h : ℝ) : Prop :=
  0 < c ∧ 0 < h ∧
    ∀ z : State, c * h * parameterSq z ≤ predictionSq z

/--
Local restricted strong identification at heterogeneity scale `h`.

This is the source-faithful form of the local stability bound's "sufficiently small
epsilon" language: the lower bound is only required in the neighborhood where
the Taylor expansion and quotient chart are valid.  The function `parameterSq`
should be read as the squared quotient distance to the fitted representation.
-/
def LocalRestrictedStrongIdentification
    {State : Type*} (inChart : State → Prop)
    (predictionSq parameterSq : State → ℝ) (c h : ℝ) : Prop :=
  0 < c ∧ 0 < h ∧
    ∀ z : State, inChart z → c * h * parameterSq z ≤ predictionSq z

/--
The source proof's Step 2 condition: the squared linearized prediction change
lower-bounds quotient squared-parameter distance at heterogeneity scale `h`.
-/
def LinearizedRestrictedStrongIdentification
    {State : Type*} (linearSq parameterSq : State → ℝ) (c h : ℝ) : Prop :=
  0 < c ∧ 0 < h ∧
    ∀ z : State, c * h * parameterSq z ≤ linearSq z

/--
Local version of the source proof's Step 2 condition.

It is enough for the linearized quotient lower bound to hold on the local
neighborhood where the theorem is asserted.
-/
def LocalLinearizedRestrictedStrongIdentification
    {State : Type*} (inChart : State → Prop)
    (linearSq parameterSq : State → ℝ) (c h : ℝ) : Prop :=
  0 < c ∧ 0 < h ∧
    ∀ z : State, inChart z → c * h * parameterSq z ≤ linearSq z

/--
The source proof's Step 1 condition: after restricting to a small enough
neighborhood, nonlinear squared prediction error dominates a fixed fraction of
the squared linearized prediction change.
-/
def PredictionDominatesLinearization
    {State : Type*} (predictionSq linearSq : State → ℝ) (κ : ℝ) : Prop :=
  0 < κ ∧ ∀ z : State, κ * linearSq z ≤ predictionSq z

/--
Local version of Taylor domination.  This captures the paper proof's use of a
neighborhood of the fitted representation rather than a global nonlinear
inequality.
-/
def LocalPredictionDominatesLinearization
    {State : Type*} (inChart : State → Prop)
    (predictionSq linearSq : State → ℝ) (κ : ℝ) : Prop :=
  0 < κ ∧ ∀ z : State, inChart z → κ * linearSq z ≤ predictionSq z

/-! ### Source-shaped heterogeneity lower-bound primitives -/

/-- Squared Euclidean norm for a finite latent vector. -/
def finiteSqNorm {K : ℕ} (x : Fin K → ℝ) : ℝ :=
  ∑ k : Fin K, x k ^ 2

/-- Squared Euclidean norms are nonnegative. -/
theorem finiteSqNorm_nonneg {K : ℕ} (x : Fin K → ℝ) :
    0 ≤ finiteSqNorm x := by
  unfold finiteSqNorm
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- Squared norm of an arbitrary finite real vector. -/
def finiteFunctionSqNorm {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  ∑ i : ι, x i ^ 2

/-- Finite squared norm of a difference is bounded by twice the two norms. -/
theorem finiteFunctionSqNorm_sub_le_two_mul_add
    {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    finiteFunctionSqNorm (fun i : ι => x i - y i) ≤
      2 * finiteFunctionSqNorm x + 2 * finiteFunctionSqNorm y := by
  unfold finiteFunctionSqNorm
  calc
    (∑ i : ι, (x i - y i) ^ 2)
        ≤ ∑ i : ι, (2 * x i ^ 2 + 2 * y i ^ 2) := by
          refine Finset.sum_le_sum ?_
          intro i _hi
          nlinarith [sq_nonneg (x i + y i)]
    _ = 2 * (∑ i : ι, x i ^ 2) + 2 * (∑ i : ι, y i ^ 2) := by
          simp [Finset.mul_sum, Finset.sum_add_distrib]

/--
Source proof Step 1 in finite-vector form.

If the Taylor remainder squared norm is at most one quarter of the linearized
squared norm, then the nonlinear prediction squared norm dominates one quarter
of the linearized squared norm.
-/
theorem localPredictionDominatesLinearization_of_remainder_bound
    {State Coord : Type*} [Fintype Coord]
    (inChart : State → Prop)
    (actual linear : State → Coord → ℝ)
    (hremainder :
      ∀ z : State, inChart z →
        4 * finiteFunctionSqNorm (fun c : Coord => actual z c - linear z c) ≤
          finiteFunctionSqNorm (linear z)) :
    LocalPredictionDominatesLinearization inChart
      (fun z : State => finiteFunctionSqNorm (actual z))
      (fun z : State => finiteFunctionSqNorm (linear z))
      (1 / 4 : ℝ) := by
  refine ⟨by norm_num, ?_⟩
  intro z hz
  let remainder : Coord → ℝ := fun c => actual z c - linear z c
  have hlin_eq :
      finiteFunctionSqNorm (linear z) =
        finiteFunctionSqNorm (fun c : Coord => actual z c - remainder c) := by
    unfold finiteFunctionSqNorm remainder
    congr
    ext c
    ring
  have hupper :
      finiteFunctionSqNorm (linear z) ≤
        2 * finiteFunctionSqNorm (actual z) +
          2 * finiteFunctionSqNorm remainder := by
    rw [hlin_eq]
    exact finiteFunctionSqNorm_sub_le_two_mul_add (actual z) remainder
  have hrem :
      4 * finiteFunctionSqNorm remainder ≤ finiteFunctionSqNorm (linear z) :=
    hremainder z hz
  nlinarith

/--
Heterogeneity lower bound for a fitted factor cloud.

This is the quadratic-form version of
`lambda_min (sum_a base_a base_a^T) >= h`, stated without introducing a matrix
API into the paper-local proof.
-/
def FactorGramLowerBound {K : ℕ} {α : Type*} [Fintype α]
    (h : ℝ) (base : α → Fin K → ℝ) : Prop :=
  ∀ x : Fin K → ℝ, h * finiteSqNorm x ≤
    ∑ a : α, (finiteDot (base a) x) ^ 2

/-- A stronger Gram lower-bound scale implies any smaller scale. -/
theorem FactorGramLowerBound.mono
    {K : ℕ} {α : Type*} [Fintype α]
    {h h' : ℝ} {base : α → Fin K → ℝ}
    (hle : h ≤ h')
    (hbase : FactorGramLowerBound h' base) :
    FactorGramLowerBound h base := by
  intro x
  have hscale : h * finiteSqNorm x ≤ h' * finiteSqNorm x :=
    mul_le_mul_of_nonneg_right hle (finiteSqNorm_nonneg x)
  exact hscale.trans (hbase x)

/-- The scalar heterogeneity Gram value for one-dimensional factors. -/
def oneDimFactorHeterogeneity {α : Type*} [Fintype α]
    (base : α → Fin 1 → ℝ) : ℝ :=
  ∑ a : α, (base a 0) ^ 2

/-- In one dimension, the factor Gram lower bound is exactly the squared-factor sum. -/
theorem FactorGramLowerBound_oneDim
    {α : Type*} [Fintype α]
    (base : α → Fin 1 → ℝ) :
    FactorGramLowerBound (oneDimFactorHeterogeneity base) base := by
  intro x
  unfold oneDimFactorHeterogeneity finiteSqNorm finiteDot
  calc
    (∑ a : α, (base a 0) ^ 2) * (∑ k : Fin 1, x k ^ 2)
        = (∑ a : α, (base a 0) ^ 2) * x 0 ^ 2 := by
          simp
    _ = ∑ a : α, (base a 0) ^ 2 * x 0 ^ 2 := by
          rw [Finset.sum_mul]
    _ = ∑ a : α, (∑ k : Fin 1, base a k * x k) ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro a _ha
          simp
          ring
    _ ≤ ∑ a : α, (∑ k : Fin 1, base a k * x k) ^ 2 := le_rfl

/-- One-dimensional version of the source heterogeneity index. -/
def oneDimHeterogeneityIndex
    {Item Model : Type*} [Fintype Item] [Fintype Model]
    (Ustar : Item → Fin 1 → ℝ)
    (Vstar : Model → Fin 1 → ℝ) : ℝ :=
  min (oneDimFactorHeterogeneity Ustar) (oneDimFactorHeterogeneity Vstar)

/--
The one-dimensional source heterogeneity index supplies both factor Gram lower
bounds needed by the local stability bound route.
-/
theorem oneDimHeterogeneityIndex_factorGramLowerBounds
    {Item Model : Type*} [Fintype Item] [Fintype Model]
    (Ustar : Item → Fin 1 → ℝ)
    (Vstar : Model → Fin 1 → ℝ) :
    FactorGramLowerBound (oneDimHeterogeneityIndex Ustar Vstar) Ustar ∧
      FactorGramLowerBound (oneDimHeterogeneityIndex Ustar Vstar) Vstar := by
  constructor
  · exact FactorGramLowerBound.mono
      (min_le_left _ _) (FactorGramLowerBound_oneDim Ustar)
  · exact FactorGramLowerBound.mono
      (min_le_right _ _) (FactorGramLowerBound_oneDim Vstar)

/-- Squared size of item/model perturbations in the source Frobenius norm. -/
def heterogeneityParameterSq
    {K : ℕ} {Item Model : Type*} [Fintype Item] [Fintype Model]
    (dU : Item → Fin K → ℝ) (dV : Model → Fin K → ℝ) : ℝ :=
  (∑ i : Item, finiteSqNorm (dU i)) +
    ∑ j : Model, finiteSqNorm (dV j)

/-- Item-block contribution to the linearized prediction norm. -/
def itemBlockLinearSq
    {K : ℕ} {Item Model : Type*} [Fintype Item] [Fintype Model]
    (Vstar : Model → Fin K → ℝ)
    (dU : Item → Fin K → ℝ) : ℝ :=
  ∑ i : Item, ∑ j : Model, (finiteDot (Vstar j) (dU i)) ^ 2

/-- Model-block contribution to the linearized prediction norm. -/
def modelBlockLinearSq
    {K : ℕ} {Item Model : Type*} [Fintype Item] [Fintype Model]
    (Ustar : Item → Fin K → ℝ)
    (dV : Model → Fin K → ℝ) : ℝ :=
  ∑ j : Model, ∑ i : Item, (finiteDot (Ustar i) (dV j)) ^ 2

/-- Raw bilinear linearized prediction norm for the source MIRT proof route. -/
def bilinearLinearizedSq
    {K : ℕ} {Item Model : Type*} [Fintype Item] [Fintype Model]
    (Ustar : Item → Fin K → ℝ)
    (Vstar : Model → Fin K → ℝ)
    (dU : Item → Fin K → ℝ) (dV : Model → Fin K → ℝ) : ℝ :=
  ∑ i : Item, ∑ j : Model,
    (finiteDot (Vstar j) (dU i) + finiteDot (Ustar i) (dV j)) ^ 2

/-- Squared prediction distance for the raw bilinear factor model. -/
def bilinearPredictionSq
    {K : ℕ} {Item Model : Type*} [Fintype Item] [Fintype Model]
    (Ustar : Item → Fin K → ℝ)
    (Vstar : Model → Fin K → ℝ)
    (U : Item → Fin K → ℝ) (V : Model → Fin K → ℝ) : ℝ :=
  ∑ i : Item, ∑ j : Model,
    (finiteDot (U i) (V j) - finiteDot (Ustar i) (Vstar j)) ^ 2

/-- Raw squared factor movement before quotienting model invariances. -/
def bilinearRawParameterSq
    {K : ℕ} {Item Model : Type*} [Fintype Item] [Fintype Model]
    (Ustar : Item → Fin K → ℝ)
    (Vstar : Model → Fin K → ℝ)
    (U : Item → Fin K → ℝ) (V : Model → Fin K → ℝ) : ℝ :=
  heterogeneityParameterSq
    (fun i : Item => fun k : Fin K => U i k - Ustar i k)
    (fun j : Model => fun k : Fin K => V j k - Vstar j k)

/-- Aggregate cross term between item and model perturbation blocks. -/
def bilinearLinearizedCrossTerm
    {K : ℕ} {Item Model : Type*} [Fintype Item] [Fintype Model]
    (Ustar : Item → Fin K → ℝ)
    (Vstar : Model → Fin K → ℝ)
    (dU : Item → Fin K → ℝ) (dV : Model → Fin K → ℝ) : ℝ :=
  ∑ i : Item, ∑ j : Model,
    finiteDot (Vstar j) (dU i) * finiteDot (Ustar i) (dV j)

/-- Expands the combined linearized norm into block norms and the cross term. -/
theorem bilinearLinearizedSq_eq_blocks_add_cross
    {K : ℕ} {Item Model : Type*} [Fintype Item] [Fintype Model]
    (Ustar : Item → Fin K → ℝ)
    (Vstar : Model → Fin K → ℝ)
    (dU : Item → Fin K → ℝ) (dV : Model → Fin K → ℝ) :
    bilinearLinearizedSq Ustar Vstar dU dV =
      itemBlockLinearSq Vstar dU + modelBlockLinearSq Ustar dV +
        2 * bilinearLinearizedCrossTerm Ustar Vstar dU dV := by
  classical
  unfold bilinearLinearizedSq itemBlockLinearSq modelBlockLinearSq
    bilinearLinearizedCrossTerm
  have hmodel :
      (∑ j : Model, ∑ i : Item,
          (finiteDot (Ustar i) (dV j)) ^ 2) =
        ∑ i : Item, ∑ j : Model,
          (finiteDot (Ustar i) (dV j)) ^ 2 := by
    rw [Finset.sum_comm]
  rw [hmodel]
  calc
    (∑ i : Item, ∑ j : Model,
        (finiteDot (Vstar j) (dU i) + finiteDot (Ustar i) (dV j)) ^ 2)
        =
        ∑ i : Item, ∑ j : Model,
          ((finiteDot (Vstar j) (dU i)) ^ 2 +
            (finiteDot (Ustar i) (dV j)) ^ 2 +
            2 * (finiteDot (Vstar j) (dU i) *
              finiteDot (Ustar i) (dV j))) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          refine Finset.sum_congr rfl ?_
          intro j _hj
          ring
    _ = (∑ i : Item, ∑ j : Model,
          (finiteDot (Vstar j) (dU i)) ^ 2) +
        (∑ i : Item, ∑ j : Model,
          (finiteDot (Ustar i) (dV j)) ^ 2) +
        2 * (∑ i : Item, ∑ j : Model,
            finiteDot (Vstar j) (dU i) *
              finiteDot (Ustar i) (dV j)) := by
          simp [Finset.sum_add_distrib, Finset.mul_sum]

/--
The raw bilinear factor parameterization has an exact scaling-gauge
cancellation direction.

At first order, moving item factors by `Ustar` and model factors by `-Vstar`
does not change any bilinear prediction.  Thus the local stability bound must either
quotient this direction out or assume an identification condition that rules it
out locally.
-/
theorem bilinearLinearizedSq_scalingGauge_zero
    {K : ℕ} {Item Model : Type*} [Fintype Item] [Fintype Model]
    (Ustar : Item → Fin K → ℝ)
    (Vstar : Model → Fin K → ℝ) :
    bilinearLinearizedSq Ustar Vstar
      (fun i : Item => Ustar i)
      (fun j : Model => fun k : Fin K => - Vstar j k) = 0 := by
  classical
  unfold bilinearLinearizedSq
  refine Finset.sum_eq_zero ?_
  intro i _hi
  refine Finset.sum_eq_zero ?_
  intro j _hj
  have hcancel :
      finiteDot (Vstar j) (Ustar i) +
        finiteDot (Ustar i) (fun k : Fin K => - Vstar j k) = 0 := by
    rw [finiteDot_neg_right, finiteDot_comm (Vstar j) (Ustar i)]
    ring
  rw [hcancel]
  norm_num

/-- In one dimension, the scaling-gauge perturbation has squared size equal to
the two factor heterogeneity sums. -/
theorem heterogeneityParameterSq_scalingGauge_oneDim_eq
    {Item Model : Type*} [Fintype Item] [Fintype Model]
    (Ustar : Item → Fin 1 → ℝ)
    (Vstar : Model → Fin 1 → ℝ) :
    heterogeneityParameterSq
      (fun i : Item => Ustar i)
      (fun j : Model => fun k : Fin 1 => - Vstar j k) =
        oneDimFactorHeterogeneity Ustar + oneDimFactorHeterogeneity Vstar := by
  unfold heterogeneityParameterSq oneDimFactorHeterogeneity finiteSqNorm
  congr 1
  · exact Finset.sum_congr rfl (fun _i _hi => by simp)
  · exact Finset.sum_congr rfl (fun _j _hj => by
      simp)

/--
With positive one-dimensional heterogeneity on both sides, the raw scaling
gauge is a nonzero parameter-space movement.
-/
theorem heterogeneityParameterSq_scalingGauge_pos_of_oneDimHeterogeneity
    {Item Model : Type*} [Fintype Item] [Fintype Model]
    (Ustar : Item → Fin 1 → ℝ)
    (Vstar : Model → Fin 1 → ℝ)
    (hh : 0 < oneDimHeterogeneityIndex Ustar Vstar) :
    0 <
      heterogeneityParameterSq
        (fun i : Item => Ustar i)
        (fun j : Model => fun k : Fin 1 => - Vstar j k) := by
  have hU : 0 < oneDimFactorHeterogeneity Ustar :=
    lt_of_lt_of_le hh (min_le_left _ _)
  have hV : 0 < oneDimFactorHeterogeneity Vstar :=
    lt_of_lt_of_le hh (min_le_right _ _)
  rw [heterogeneityParameterSq_scalingGauge_oneDim_eq]
  linarith

/--
Exact nonlinear scaling of bilinear factors leaves all fitted predictions
unchanged.

This is the raw, non-infinitesimal version of the scaling-gauge issue: replacing
`Ustar` by `s • Ustar` and `Vstar` by `s⁻¹ • Vstar` preserves every bilinear
inner product when `s ≠ 0`.
-/
theorem bilinearPredictionSq_scalingGauge_zero
    {K : ℕ} {Item Model : Type*} [Fintype Item] [Fintype Model]
    (Ustar : Item → Fin K → ℝ)
    (Vstar : Model → Fin K → ℝ)
    {s : ℝ} (hs : s ≠ 0) :
    bilinearPredictionSq Ustar Vstar
      (fun i : Item => fun k : Fin K => s * Ustar i k)
      (fun j : Model => fun k : Fin K => s⁻¹ * Vstar j k) = 0 := by
  classical
  unfold bilinearPredictionSq
  refine Finset.sum_eq_zero ?_
  intro i _hi
  refine Finset.sum_eq_zero ?_
  intro j _hj
  have hscale : s * s⁻¹ = 1 := by
    field_simp [hs]
  have hdot :
      finiteDot
          (fun k : Fin K => s * Ustar i k)
          (fun k : Fin K => s⁻¹ * Vstar j k) =
        finiteDot (Ustar i) (Vstar j) := by
    rw [finiteDot_smul_smul, hscale]
    ring
  rw [hdot]
  norm_num

/-- Raw one-dimensional factor movement under exact scaling. -/
theorem bilinearRawParameterSq_scalingGauge_oneDim_eq
    {Item Model : Type*} [Fintype Item] [Fintype Model]
    (Ustar : Item → Fin 1 → ℝ)
    (Vstar : Model → Fin 1 → ℝ)
    (s : ℝ) :
    bilinearRawParameterSq Ustar Vstar
      (fun i : Item => fun k : Fin 1 => s * Ustar i k)
      (fun j : Model => fun k : Fin 1 => s⁻¹ * Vstar j k) =
        (s - 1) ^ 2 * oneDimFactorHeterogeneity Ustar +
          (s⁻¹ - 1) ^ 2 * oneDimFactorHeterogeneity Vstar := by
  have hU :
      (∑ i : Item,
          finiteSqNorm
            (fun k : Fin 1 => s * Ustar i k - Ustar i k)) =
        (s - 1) ^ 2 * oneDimFactorHeterogeneity Ustar := by
    unfold finiteSqNorm oneDimFactorHeterogeneity
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    simp
    ring
  have hV :
      (∑ j : Model,
          finiteSqNorm
            (fun k : Fin 1 => s⁻¹ * Vstar j k - Vstar j k)) =
        (s⁻¹ - 1) ^ 2 * oneDimFactorHeterogeneity Vstar := by
    unfold finiteSqNorm oneDimFactorHeterogeneity
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _hj
    simp
    ring
  unfold bilinearRawParameterSq heterogeneityParameterSq
  rw [hU, hV]

/--
In one dimension, any nontrivial exact scaling changes the raw factor
coordinates by a positive amount whenever the source heterogeneity index is
positive.
-/
theorem bilinearRawParameterSq_scalingGauge_pos_oneDim
    {Item Model : Type*} [Fintype Item] [Fintype Model]
    (Ustar : Item → Fin 1 → ℝ)
    (Vstar : Model → Fin 1 → ℝ)
    {s : ℝ}
    (hs : s ≠ 1)
    (hh : 0 < oneDimHeterogeneityIndex Ustar Vstar) :
    0 <
      bilinearRawParameterSq Ustar Vstar
        (fun i : Item => fun k : Fin 1 => s * Ustar i k)
        (fun j : Model => fun k : Fin 1 => s⁻¹ * Vstar j k) := by
  have hU : 0 < oneDimFactorHeterogeneity Ustar :=
    lt_of_lt_of_le hh (min_le_left _ _)
  have hV_nonneg : 0 ≤ oneDimFactorHeterogeneity Vstar := by
    unfold oneDimFactorHeterogeneity
    exact Finset.sum_nonneg (fun _j _hj => sq_nonneg _)
  have hcoefU : 0 < (s - 1) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hs)
  have hcoefV : 0 ≤ (s⁻¹ - 1) ^ 2 := sq_nonneg _
  rw [bilinearRawParameterSq_scalingGauge_oneDim_eq]
  nlinarith [mul_pos hcoefU hU, mul_nonneg hcoefV hV_nonneg]

/--
Aggregate no-cancellation condition for the combined linearized map.

The paper proof sketch currently uses the false pointwise inequality
`(a+b)^2 >= a^2/4 + b^2/4`.  The theorem below needs exactly the source
condition that remains after quotienting/gauge-fixing the null-model
invariances: the combined linearized norm controls the sum of the two block
norms.
-/
def LinearizedSplitLowerBound
    {K : ℕ} {Item Model : Type*} [Fintype Item] [Fintype Model]
    (γ : ℝ)
    (Ustar : Item → Fin K → ℝ)
    (Vstar : Model → Fin K → ℝ)
    (dU : Item → Fin K → ℝ) (dV : Model → Fin K → ℝ) : Prop :=
  γ * (itemBlockLinearSq Vstar dU + modelBlockLinearSq Ustar dV) ≤
    bilinearLinearizedSq Ustar Vstar dU dV

/--
A nonnegative aggregate cross term is a concrete sufficient condition for the
corrected split lower bound with coefficient one.
-/
theorem linearizedSplitLowerBound_one_of_cross_nonnegative
    {K : ℕ} {Item Model : Type*} [Fintype Item] [Fintype Model]
    (Ustar : Item → Fin K → ℝ)
    (Vstar : Model → Fin K → ℝ)
    (dU : Item → Fin K → ℝ) (dV : Model → Fin K → ℝ)
    (hcross : 0 ≤ bilinearLinearizedCrossTerm Ustar Vstar dU dV) :
    LinearizedSplitLowerBound 1 Ustar Vstar dU dV := by
  unfold LinearizedSplitLowerBound
  rw [bilinearLinearizedSq_eq_blocks_add_cross]
  nlinarith

/--
Exact first-order cancellation is a local non-identification witness.

If a nonzero tangent perturbation changes the linearized predictions by zero,
then no positive restricted-identification lower bound can hold for that local
linearized map.  This is the converse intuition behind the corrected Theorem
4.2 route: cancellation is not harmless proof slack; it is precisely an
ill-conditioned quotient direction unless removed by the quotient/gauge
condition.
-/
theorem not_linearizedRestrictedStrongIdentification_of_exact_cancellation
    {K : ℕ} {Item Model : Type*} [Fintype Item] [Fintype Model]
    (Ustar : Item → Fin K → ℝ)
    (Vstar : Model → Fin K → ℝ)
    (dU : Item → Fin K → ℝ) (dV : Model → Fin K → ℝ)
    {c h : ℝ}
    (hc : 0 < c) (hh : 0 < h)
    (hparam : 0 < heterogeneityParameterSq dU dV)
    (hcancel : bilinearLinearizedSq Ustar Vstar dU dV = 0) :
    ¬ LinearizedRestrictedStrongIdentification
      (fun _z : Unit => bilinearLinearizedSq Ustar Vstar dU dV)
      (fun _z : Unit => heterogeneityParameterSq dU dV)
      c h := by
  intro hident
  have hbound := hident.2.2 ()
  rw [hcancel] at hbound
  have hpositive : 0 < c * h * heterogeneityParameterSq dU dV := by
    nlinarith [mul_pos hc hh]
  nlinarith

/--
Positive one-dimensional factor heterogeneity does not by itself imply raw
linearized identification, because the scaling gauge is an exact cancellation
direction.

This is the formal reason the source theorem must use quotient distance or an
explicit no-cancellation/restricted-identification condition, rather than only
positive factor-Gram heterogeneity.
-/
theorem not_linearizedRestrictedStrongIdentification_of_oneDim_scalingGauge
    {Item Model : Type*} [Fintype Item] [Fintype Model]
    (Ustar : Item → Fin 1 → ℝ)
    (Vstar : Model → Fin 1 → ℝ)
    {c : ℝ}
    (hc : 0 < c)
    (hh : 0 < oneDimHeterogeneityIndex Ustar Vstar) :
    ¬ LinearizedRestrictedStrongIdentification
      (fun _z : Unit =>
        bilinearLinearizedSq Ustar Vstar
          (fun i : Item => Ustar i)
          (fun j : Model => fun k : Fin 1 => - Vstar j k))
      (fun _z : Unit =>
        heterogeneityParameterSq
          (fun i : Item => Ustar i)
          (fun j : Model => fun k : Fin 1 => - Vstar j k))
      c (oneDimHeterogeneityIndex Ustar Vstar) := by
  exact
    not_linearizedRestrictedStrongIdentification_of_exact_cancellation
      Ustar Vstar
      (fun i : Item => Ustar i)
      (fun j : Model => fun k : Fin 1 => - Vstar j k)
      hc hh
      (heterogeneityParameterSq_scalingGauge_pos_of_oneDimHeterogeneity
        Ustar Vstar hh)
      (bilinearLinearizedSq_scalingGauge_zero Ustar Vstar)

/--
Small first-order movement is an approximate non-identification witness at the
specified constant.
-/
theorem not_linearizedRestrictedStrongIdentification_of_small_linearizedSq
    {K : ℕ} {Item Model : Type*} [Fintype Item] [Fintype Model]
    (Ustar : Item → Fin K → ℝ)
    (Vstar : Model → Fin K → ℝ)
    (dU : Item → Fin K → ℝ) (dV : Model → Fin K → ℝ)
    {c h : ℝ}
    (hsmall :
      bilinearLinearizedSq Ustar Vstar dU dV <
        c * h * heterogeneityParameterSq dU dV) :
    ¬ LinearizedRestrictedStrongIdentification
      (fun _z : Unit => bilinearLinearizedSq Ustar Vstar dU dV)
      (fun _z : Unit => heterogeneityParameterSq dU dV)
      c h := by
  intro hident
  have hbound := hident.2.2 ()
  nlinarith

/--
An exactly prediction-equivalent but parameter-distinct representation rules
out any fixed linear stability rate.

This is the nonlinear version of the cancellation intuition: if the fitted
predictions do not move but the quotient parameter distance is positive, then
for every advertised constant `C` one can take `ε` small enough that the
representation lies in the `ε`-equivalence set while violating the
`C * ε / sqrt(h)` bound.
-/
theorem exact_prediction_equivalent_nonzero_violates_fixed_linear_rate
    {State : Type*}
    (predictionSq parameterDistance : State → ℝ)
    {h C : ℝ}
    (hh : 0 < h)
    (hC : 0 ≤ C)
    {z : State}
    (hpred : predictionSq z = 0)
    (hdist : 0 < parameterDistance z) :
    ∃ ε : ℝ, 0 < ε ∧ IsEpsilonEquivalent predictionSq ε z ∧
      ¬ parameterDistance z ≤ (C / Real.sqrt h) * ε := by
  let ε : ℝ := parameterDistance z * Real.sqrt h / (2 * (C + 1))
  have hsqrth_pos : 0 < Real.sqrt h := Real.sqrt_pos.mpr hh
  have hden_pos : 0 < 2 * (C + 1) := by nlinarith
  have hε_pos : 0 < ε := by
    dsimp [ε]
    positivity
  refine ⟨ε, hε_pos, ?_, ?_⟩
  · dsimp [IsEpsilonEquivalent]
    rw [hpred]
    exact sq_nonneg ε
  · intro hrate
    have hrate' :
        parameterDistance z ≤
          parameterDistance z * (C / (2 * (C + 1))) := by
      calc
        parameterDistance z ≤ (C / Real.sqrt h) * ε := hrate
        _ = parameterDistance z * (C / (2 * (C + 1))) := by
          dsimp [ε]
          field_simp [hsqrth_pos.ne', hden_pos.ne']
    have hfactor_lt_one : C / (2 * (C + 1)) < 1 := by
      rw [div_lt_one hden_pos]
      nlinarith
    have hstrict :
        parameterDistance z * (C / (2 * (C + 1))) <
          parameterDistance z := by
      nlinarith [mul_lt_mul_of_pos_left hfactor_lt_one hdist]
    nlinarith

/--
Positive one-dimensional factor heterogeneity still cannot make a raw
unquotiented bilinear factorization stable under the paper's advertised
linear rate.

For every nontrivial scaling of the fitted factors, predictions are exactly
unchanged while raw factor distance is positive.  Therefore the theorem's
distance must be a quotient distance, or the theorem must add a gauge-fixing /
restricted-identification condition.
-/
theorem exact_scalingGauge_violates_raw_linear_rate_oneDim
    {Item Model : Type*} [Fintype Item] [Fintype Model]
    (Ustar : Item → Fin 1 → ℝ)
    (Vstar : Model → Fin 1 → ℝ)
    {C s : ℝ}
    (hC : 0 ≤ C)
    (hs0 : s ≠ 0)
    (hs1 : s ≠ 1)
    (hh : 0 < oneDimHeterogeneityIndex Ustar Vstar) :
    ∃ ε : ℝ, 0 < ε ∧
      IsEpsilonEquivalent
        (fun _z : Unit =>
          bilinearPredictionSq Ustar Vstar
            (fun i : Item => fun k : Fin 1 => s * Ustar i k)
            (fun j : Model => fun k : Fin 1 => s⁻¹ * Vstar j k))
        ε () ∧
      ¬ Real.sqrt
          (bilinearRawParameterSq Ustar Vstar
            (fun i : Item => fun k : Fin 1 => s * Ustar i k)
            (fun j : Model => fun k : Fin 1 => s⁻¹ * Vstar j k)) ≤
          (C / Real.sqrt (oneDimHeterogeneityIndex Ustar Vstar)) * ε := by
  exact
    exact_prediction_equivalent_nonzero_violates_fixed_linear_rate
      (fun _z : Unit =>
        bilinearPredictionSq Ustar Vstar
          (fun i : Item => fun k : Fin 1 => s * Ustar i k)
          (fun j : Model => fun k : Fin 1 => s⁻¹ * Vstar j k))
      (fun _z : Unit =>
        Real.sqrt
          (bilinearRawParameterSq Ustar Vstar
            (fun i : Item => fun k : Fin 1 => s * Ustar i k)
            (fun j : Model => fun k : Fin 1 => s⁻¹ * Vstar j k)))
      hh hC
      (by
        rw [bilinearPredictionSq_scalingGauge_zero Ustar Vstar hs0])
      (Real.sqrt_pos.mpr
        (bilinearRawParameterSq_scalingGauge_pos_oneDim Ustar Vstar hs1 hh))

/-- Item-factor heterogeneity controls all item perturbations. -/
theorem itemBlockLinearSq_lower_bound_of_factorGram
    {K : ℕ} {Item Model : Type*} [Fintype Item] [Fintype Model]
    {h : ℝ}
    (Vstar : Model → Fin K → ℝ)
    (dU : Item → Fin K → ℝ)
    (hV : FactorGramLowerBound h Vstar) :
    h * (∑ i : Item, finiteSqNorm (dU i)) ≤
      itemBlockLinearSq Vstar dU := by
  calc
    h * (∑ i : Item, finiteSqNorm (dU i))
        = ∑ i : Item, h * finiteSqNorm (dU i) := by
          rw [Finset.mul_sum]
    _ ≤ ∑ i : Item, ∑ j : Model,
          (finiteDot (Vstar j) (dU i)) ^ 2 := by
          exact Finset.sum_le_sum (fun i _hi => hV (dU i))
    _ = itemBlockLinearSq Vstar dU := rfl

/-- Model-factor heterogeneity controls all model perturbations. -/
theorem modelBlockLinearSq_lower_bound_of_factorGram
    {K : ℕ} {Item Model : Type*} [Fintype Item] [Fintype Model]
    {h : ℝ}
    (Ustar : Item → Fin K → ℝ)
    (dV : Model → Fin K → ℝ)
    (hU : FactorGramLowerBound h Ustar) :
    h * (∑ j : Model, finiteSqNorm (dV j)) ≤
      modelBlockLinearSq Ustar dV := by
  calc
    h * (∑ j : Model, finiteSqNorm (dV j))
        = ∑ j : Model, h * finiteSqNorm (dV j) := by
          rw [Finset.mul_sum]
    _ ≤ ∑ j : Model, ∑ i : Item,
          (finiteDot (Ustar i) (dV j)) ^ 2 := by
          exact Finset.sum_le_sum (fun j _hj => hU (dV j))
    _ = modelBlockLinearSq Ustar dV := rfl

/--
The heterogeneity index controls the sum of the item and model block
linearized norms.
-/
theorem blockLinearSq_lower_bound_of_factorGrams
    {K : ℕ} {Item Model : Type*} [Fintype Item] [Fintype Model]
    {h : ℝ}
    (Ustar : Item → Fin K → ℝ)
    (Vstar : Model → Fin K → ℝ)
    (dU : Item → Fin K → ℝ) (dV : Model → Fin K → ℝ)
    (hU : FactorGramLowerBound h Ustar)
    (hV : FactorGramLowerBound h Vstar) :
    h * heterogeneityParameterSq dU dV ≤
      itemBlockLinearSq Vstar dU + modelBlockLinearSq Ustar dV := by
  have hitem :
      h * (∑ i : Item, finiteSqNorm (dU i)) ≤
        itemBlockLinearSq Vstar dU :=
    itemBlockLinearSq_lower_bound_of_factorGram Vstar dU hV
  have hmodel :
      h * (∑ j : Model, finiteSqNorm (dV j)) ≤
        modelBlockLinearSq Ustar dV :=
    modelBlockLinearSq_lower_bound_of_factorGram Ustar dV hU
  calc
    h * heterogeneityParameterSq dU dV
        = h * (∑ i : Item, finiteSqNorm (dU i)) +
            h * (∑ j : Model, finiteSqNorm (dV j)) := by
          simp [heterogeneityParameterSq]
          ring
    _ ≤ itemBlockLinearSq Vstar dU + modelBlockLinearSq Ustar dV :=
      add_le_add hitem hmodel

/--
Source proof Step 2, corrected: factor heterogeneity plus an aggregate
no-cancellation/gauge condition gives the linearized restricted-identification
lower bound.
-/
theorem bilinearLinearizedSq_lower_bound_of_factorGrams_and_split
    {K : ℕ} {Item Model : Type*} [Fintype Item] [Fintype Model]
    {γ h : ℝ}
    (Ustar : Item → Fin K → ℝ)
    (Vstar : Model → Fin K → ℝ)
    (dU : Item → Fin K → ℝ) (dV : Model → Fin K → ℝ)
    (hγ : 0 ≤ γ)
    (hU : FactorGramLowerBound h Ustar)
    (hV : FactorGramLowerBound h Vstar)
    (hsplit : LinearizedSplitLowerBound γ Ustar Vstar dU dV) :
    γ * h * heterogeneityParameterSq dU dV ≤
      bilinearLinearizedSq Ustar Vstar dU dV := by
  have hblock :
      h * heterogeneityParameterSq dU dV ≤
        itemBlockLinearSq Vstar dU + modelBlockLinearSq Ustar dV :=
    blockLinearSq_lower_bound_of_factorGrams Ustar Vstar dU dV hU hV
  have hscaled :
      γ * (h * heterogeneityParameterSq dU dV) ≤
        γ * (itemBlockLinearSq Vstar dU + modelBlockLinearSq Ustar dV) :=
    mul_le_mul_of_nonneg_left hblock hγ
  calc
    γ * h * heterogeneityParameterSq dU dV
        = γ * (h * heterogeneityParameterSq dU dV) := by ring
    _ ≤ γ * (itemBlockLinearSq Vstar dU + modelBlockLinearSq Ustar dV) :=
      hscaled
    _ ≤ bilinearLinearizedSq Ustar Vstar dU dV := hsplit

/--
The source-shaped Step 2 lower bound as a local restricted-identification
predicate usable by the existing the local stability bound route.
-/
theorem localLinearizedRestrictedStrongIdentification_of_factorGrams_and_split
    {K : ℕ} {State Item Model : Type*}
    [Fintype Item] [Fintype Model]
    (inChart : State → Prop)
    (Ustar : Item → Fin K → ℝ)
    (Vstar : Model → Fin K → ℝ)
    (dU : State → Item → Fin K → ℝ)
    (dV : State → Model → Fin K → ℝ)
    {γ h : ℝ}
    (hγ : 0 < γ)
    (hh : 0 < h)
    (hU : FactorGramLowerBound h Ustar)
    (hV : FactorGramLowerBound h Vstar)
    (hsplit :
      ∀ z : State, inChart z →
        LinearizedSplitLowerBound γ Ustar Vstar (dU z) (dV z)) :
    LocalLinearizedRestrictedStrongIdentification inChart
      (fun z : State => bilinearLinearizedSq Ustar Vstar (dU z) (dV z))
      (fun z : State => heterogeneityParameterSq (dU z) (dV z))
      γ h := by
  refine ⟨hγ, hh, ?_⟩
  intro z hz
  exact bilinearLinearizedSq_lower_bound_of_factorGrams_and_split
    Ustar Vstar (dU z) (dV z) (le_of_lt hγ) hU hV (hsplit z hz)

/--
Nonnegative aggregate cross terms give the local linearized
restricted-identification condition directly.
-/
theorem localLinearizedRestrictedStrongIdentification_of_factorGrams_cross_nonnegative
    {K : ℕ} {State Item Model : Type*}
    [Fintype Item] [Fintype Model]
    (inChart : State → Prop)
    (Ustar : Item → Fin K → ℝ)
    (Vstar : Model → Fin K → ℝ)
    (dU : State → Item → Fin K → ℝ)
    (dV : State → Model → Fin K → ℝ)
    {h : ℝ}
    (hh : 0 < h)
    (hU : FactorGramLowerBound h Ustar)
    (hV : FactorGramLowerBound h Vstar)
    (hcross :
      ∀ z : State, inChart z →
        0 ≤ bilinearLinearizedCrossTerm Ustar Vstar (dU z) (dV z)) :
    LocalLinearizedRestrictedStrongIdentification inChart
      (fun z : State => bilinearLinearizedSq Ustar Vstar (dU z) (dV z))
      (fun z : State => heterogeneityParameterSq (dU z) (dV z))
      1 h :=
  localLinearizedRestrictedStrongIdentification_of_factorGrams_and_split
    inChart Ustar Vstar dU dV zero_lt_one hh hU hV
    (fun z hz =>
      linearizedSplitLowerBound_one_of_cross_nonnegative
        Ustar Vstar (dU z) (dV z) (hcross z hz))

/--
Cancellation prevents a lower bound from the two summands alone.

The pointwise inequality `(a+b)^2 >= (1/4)*a^2 + (1/4)*b^2` is false without
an alignment or cross-term condition; `a = 1`, `b = -1` is the minimal
cancellation witness. A valid combined bound needs a direct lower bound for
the linearized quotient map.
-/
theorem square_add_lower_bound_quarter_terms_false :
    ¬ (∀ a b : ℝ, (1 / 4 : ℝ) * a ^ 2 + (1 / 4 : ℝ) * b ^ 2 ≤ (a + b) ^ 2) := by
  intro h
  have hbad := h 1 (-1)
  norm_num at hbad

/--
the local stability bound proof route: Taylor domination plus the linearized quotient
lower bound imply restricted strong identification for the nonlinear prediction
map, with constant `κ * c`.
-/
theorem restrictedStrongIdentification_of_linearized_and_taylor
    {State : Type*}
    (predictionSq linearSq parameterSq : State → ℝ)
    {κ c h : ℝ}
    (htaylor : PredictionDominatesLinearization predictionSq linearSq κ)
    (hlin :
      LinearizedRestrictedStrongIdentification linearSq parameterSq c h) :
    RestrictedStrongIdentification predictionSq parameterSq (κ * c) h := by
  refine ⟨mul_pos htaylor.1 hlin.1, hlin.2.1, ?_⟩
  intro z
  have hlin_z := hlin.2.2 z
  have htaylor_z := htaylor.2 z
  have hscaled :
      κ * (c * h * parameterSq z) ≤ κ * linearSq z :=
    mul_le_mul_of_nonneg_left hlin_z (le_of_lt htaylor.1)
  calc
    (κ * c) * h * parameterSq z = κ * (c * h * parameterSq z) := by ring
    _ ≤ κ * linearSq z := hscaled
    _ ≤ predictionSq z := htaylor_z

/--
Local the local stability bound proof route: local Taylor domination plus a local linearized
quotient lower bound imply local restricted strong identification for the
nonlinear prediction map.
-/
theorem localRestrictedStrongIdentification_of_linearized_and_taylor
    {State : Type*}
    (inChart : State → Prop)
    (predictionSq linearSq parameterSq : State → ℝ)
    {κ c h : ℝ}
    (htaylor :
      LocalPredictionDominatesLinearization inChart predictionSq linearSq κ)
    (hlin :
      LocalLinearizedRestrictedStrongIdentification
        inChart linearSq parameterSq c h) :
    LocalRestrictedStrongIdentification
      inChart predictionSq parameterSq (κ * c) h := by
  refine ⟨mul_pos htaylor.1 hlin.1, hlin.2.1, ?_⟩
  intro z hz
  have hlin_z := hlin.2.2 z hz
  have htaylor_z := htaylor.2 z hz
  have hscaled :
      κ * (c * h * parameterSq z) ≤ κ * linearSq z :=
    mul_le_mul_of_nonneg_left hlin_z (le_of_lt htaylor.1)
  calc
    (κ * c) * h * parameterSq z = κ * (c * h * parameterSq z) := by ring
    _ ≤ κ * linearSq z := hscaled
    _ ≤ predictionSq z := htaylor_z

/--
The conditional algebraic core of the local stability bound.

If the local prediction-distance map lower-bounds parameter distance by
`c * sqrtH`, then every representation with prediction distance at most
`ε` has parameter distance at most `ε / (c * sqrtH)`.  In the source theorem,
`sqrtH` corresponds to the square-root heterogeneity scale and the missing
source condition is precisely the local lower bound supplied as `hstable`.
-/
theorem heterogeneity_stability_of_linear_lower_bound
    {State : Type*}
    (predictionDistance parameterDistance : State → ℝ)
    {c sqrtH ε : ℝ}
    (hc : 0 < c) (hsqrtH : 0 < sqrtH)
    (hstable :
      ∀ z : State,
        c * sqrtH * parameterDistance z ≤ predictionDistance z)
    {z : State}
    (hpred : predictionDistance z ≤ ε) :
    parameterDistance z ≤ ε / (c * sqrtH) := by
  have hden : 0 < c * sqrtH := mul_pos hc hsqrtH
  have hmul : (c * sqrtH) * parameterDistance z ≤ ε := by
    have hstable_z := hstable z
    nlinarith
  have hmul' : parameterDistance z * (c * sqrtH) ≤ ε := by
    nlinarith
  rw [le_div_iff₀ hden]
  exact hmul'

/--
the local stability bound's natural squared-distance form.

If the local quotient-space prediction error has a quadratic lower bound
`c * h * parameterSq`, then membership in the `ε` prediction-error ball gives
the squared parameter-distance bound `ε^2 / (c * h)`.
-/
theorem heterogeneity_stability_of_quadratic_lower_bound
    {State : Type*}
    (predictionSq parameterSq : State → ℝ)
    {c h ε : ℝ}
    (hc : 0 < c) (hh : 0 < h)
    (hstable :
      ∀ z : State,
        c * h * parameterSq z ≤ predictionSq z)
    {z : State}
    (hpred : predictionSq z ≤ ε ^ 2) :
    parameterSq z ≤ ε ^ 2 / (c * h) := by
  have hden : 0 < c * h := mul_pos hc hh
  have hmul : (c * h) * parameterSq z ≤ ε ^ 2 := by
    have hstable_z := hstable z
    nlinarith
  have hmul' : parameterSq z * (c * h) ≤ ε ^ 2 := by
    nlinarith
  rw [le_div_iff₀ hden]
  exact hmul'

/--
The local squared-distance core of the local stability bound.

The quotient-space prediction-error lower bound only needs to hold for the
local neighborhood in which the theorem is applied.
-/
theorem heterogeneity_stability_of_local_quadratic_lower_bound
    {State : Type*}
    (inChart : State → Prop)
    (predictionSq parameterSq : State → ℝ)
    {c h ε : ℝ}
    (hc : 0 < c) (hh : 0 < h)
    (hstable :
      ∀ z : State,
        inChart z → c * h * parameterSq z ≤ predictionSq z)
    {z : State}
    (hz : inChart z)
    (hpred : predictionSq z ≤ ε ^ 2) :
    parameterSq z ≤ ε ^ 2 / (c * h) := by
  have hden : 0 < c * h := mul_pos hc hh
  have hmul : (c * h) * parameterSq z ≤ ε ^ 2 := by
    have hstable_z := hstable z hz
    nlinarith
  have hmul' : parameterSq z * (c * h) ≤ ε ^ 2 := by
    nlinarith
  rw [le_div_iff₀ hden]
  exact hmul'

/--
the local stability bound strengthened to a named assumption.

Under restricted strong identification at scale `h`, every epsilon-equivalent
representation has quotient squared-parameter distance at most `ε^2 / (c*h)`.
-/
theorem parameterSq_le_of_epsilonEquivalent_of_restrictedStrongIdentification
    {State : Type*}
    (predictionSq parameterSq : State → ℝ)
    {c h ε : ℝ}
    (hident :
      RestrictedStrongIdentification predictionSq parameterSq c h)
    {z : State}
    (heq : IsEpsilonEquivalent predictionSq ε z) :
    parameterSq z ≤ ε ^ 2 / (c * h) :=
  heterogeneity_stability_of_quadratic_lower_bound
    predictionSq parameterSq hident.1 hident.2.1 hident.2.2 heq

/--
the local stability bound in its natural local named-assumption form.

Inside the local neighborhood where the quotient chart and Taylor estimates
hold, epsilon-equivalent representations have squared quotient-parameter
distance at most `ε^2 / (c*h)`.
-/
theorem parameterSq_le_of_epsilonEquivalent_of_localRestrictedStrongIdentification
    {State : Type*}
    (inChart : State → Prop)
    (predictionSq parameterSq : State → ℝ)
    {c h ε : ℝ}
    (hident :
      LocalRestrictedStrongIdentification inChart predictionSq parameterSq c h)
    {z : State}
    (hz : inChart z)
    (heq : IsEpsilonEquivalent predictionSq ε z) :
    parameterSq z ≤ ε ^ 2 / (c * h) :=
  heterogeneity_stability_of_local_quadratic_lower_bound
    inChart predictionSq parameterSq hident.1 hident.2.1 hident.2.2 hz heq

/--
Distance-form consequence of the squared the local stability bound bound.

If `parameterSq` is the square of a nonnegative quotient distance, then local
restricted strong identification yields the source-scale bound
`ε / sqrt (c*h)`, i.e. `C * ε / sqrt h` for `C = 1 / sqrt c`.
-/
theorem parameterDistance_le_of_epsilonEquivalent_of_localRestrictedStrongIdentification
    {State : Type*}
    (inChart : State → Prop)
    (predictionSq parameterSq parameterDistance : State → ℝ)
    {c h ε : ℝ}
    (hident :
      LocalRestrictedStrongIdentification inChart predictionSq parameterSq c h)
    (hdistance_nonneg : ∀ z : State, 0 ≤ parameterDistance z)
    (hsq : ∀ z : State, parameterSq z = parameterDistance z ^ 2)
    (hε : 0 ≤ ε)
    {z : State}
    (hz : inChart z)
    (heq : IsEpsilonEquivalent predictionSq ε z) :
    parameterDistance z ≤ ε / Real.sqrt (c * h) := by
  have hden_pos : 0 < c * h := mul_pos hident.1 hident.2.1
  have hsq_bound :
      parameterSq z ≤ ε ^ 2 / (c * h) :=
    parameterSq_le_of_epsilonEquivalent_of_localRestrictedStrongIdentification
      inChart predictionSq parameterSq hident hz heq
  have htarget_nonneg : 0 ≤ ε / Real.sqrt (c * h) :=
    div_nonneg hε (Real.sqrt_nonneg _)
  have htarget_sq :
      (ε / Real.sqrt (c * h)) ^ 2 = ε ^ 2 / (c * h) := by
    rw [div_pow, Real.sq_sqrt (le_of_lt hden_pos)]
  have hsq_bound' :
      parameterDistance z ^ 2 ≤ (ε / Real.sqrt (c * h)) ^ 2 := by
    simpa [hsq z, htarget_sq] using hsq_bound
  exact (sq_le_sq₀ (hdistance_nonneg z) htarget_nonneg).mp hsq_bound'

/--
the local stability bound in the source's "sufficiently small `ε`" form.

Rather than requiring chart membership pointwise, this version assumes the
whole `ε`-equivalence set is contained in the local chart.  That is the natural
formal version of choosing `ε` small enough in the paper statement.
-/
theorem parameterDistance_le_of_epsilonEquivalent_of_small_epsilon_localRestrictedStrongIdentification
    {State : Type*}
    (inChart : State → Prop)
    (predictionSq parameterSq parameterDistance : State → ℝ)
    {c h ε : ℝ}
    (hsmall : EpsilonEquivalentInsideChart inChart predictionSq ε)
    (hident :
      LocalRestrictedStrongIdentification inChart predictionSq parameterSq c h)
    (hdistance_nonneg : ∀ z : State, 0 ≤ parameterDistance z)
    (hsq : ∀ z : State, parameterSq z = parameterDistance z ^ 2)
    (hε : 0 ≤ ε)
    {z : State}
    (heq : IsEpsilonEquivalent predictionSq ε z) :
    parameterDistance z ≤ ε / Real.sqrt (c * h) :=
  parameterDistance_le_of_epsilonEquivalent_of_localRestrictedStrongIdentification
    inChart predictionSq parameterSq parameterDistance hident
    hdistance_nonneg hsq hε (hsmall z heq) heq

/--
Source-shaped constant form of the local stability bound.

The paper states the distance rate as `C * ε / sqrt h` for some constant `C`.
The local restricted-identification theorem gives this with
`C = 1 / sqrt c`.
-/
theorem parameterDistance_le_of_epsilonEquivalent_of_small_epsilon_localRestrictedStrongIdentification_exists_constant
    {State : Type*}
    (inChart : State → Prop)
    (predictionSq parameterSq parameterDistance : State → ℝ)
    {c h ε : ℝ}
    (hsmall : EpsilonEquivalentInsideChart inChart predictionSq ε)
    (hident :
      LocalRestrictedStrongIdentification inChart predictionSq parameterSq c h)
    (hdistance_nonneg : ∀ z : State, 0 ≤ parameterDistance z)
    (hsq : ∀ z : State, parameterSq z = parameterDistance z ^ 2)
    (hε : 0 ≤ ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {z : State}, IsEpsilonEquivalent predictionSq ε z →
        parameterDistance z ≤ (C / Real.sqrt h) * ε := by
  refine ⟨(Real.sqrt c)⁻¹, ?_, ?_⟩
  · exact inv_pos.mpr (Real.sqrt_pos.mpr hident.1)
  · intro z heq
    have hbase :
        parameterDistance z ≤ ε / Real.sqrt (c * h) :=
      parameterDistance_le_of_epsilonEquivalent_of_small_epsilon_localRestrictedStrongIdentification
        inChart predictionSq parameterSq parameterDistance hsmall hident
        hdistance_nonneg hsq hε heq
    have hc_nonneg : 0 ≤ c := le_of_lt hident.1
    have hsqrtc_pos : 0 < Real.sqrt c := Real.sqrt_pos.mpr hident.1
    have hsqrth_pos : 0 < Real.sqrt h := Real.sqrt_pos.mpr hident.2.1
    have hrewrite :
        ε / Real.sqrt (c * h) =
          (((Real.sqrt c)⁻¹) / Real.sqrt h) * ε := by
      rw [Real.sqrt_mul hc_nonneg h]
      field_simp [hsqrtc_pos.ne', hsqrth_pos.ne']
    exact hbase.trans_eq hrewrite

/--
the local stability bound stated in the source proof's two-step form.

If the nonlinear prediction error dominates the linearized error and the
linearized map satisfies restricted strong identification, then every
epsilon-equivalent representation has squared parameter distance bounded by
`ε^2 / ((κ*c) * h)`.
-/
theorem parameterSq_le_of_epsilonEquivalent_of_linearized_taylor
    {State : Type*}
    (predictionSq linearSq parameterSq : State → ℝ)
    {κ c h ε : ℝ}
    (htaylor : PredictionDominatesLinearization predictionSq linearSq κ)
    (hlin :
      LinearizedRestrictedStrongIdentification linearSq parameterSq c h)
    {z : State}
    (heq : IsEpsilonEquivalent predictionSq ε z) :
    parameterSq z ≤ ε ^ 2 / ((κ * c) * h) :=
  parameterSq_le_of_epsilonEquivalent_of_restrictedStrongIdentification
    predictionSq parameterSq
    (restrictedStrongIdentification_of_linearized_and_taylor
      predictionSq linearSq parameterSq htaylor hlin)
    heq

/--
the local stability bound in the source proof's natural local two-step form.

After restricting to a neighborhood of the fitted representation, Taylor
domination and a linearized
quotient-space lower bound imply the `ε^2 / ((κ*c)*h)` stability bound.
-/
theorem parameterSq_le_of_epsilonEquivalent_of_local_linearized_taylor
    {State : Type*}
    (inChart : State → Prop)
    (predictionSq linearSq parameterSq : State → ℝ)
    {κ c h ε : ℝ}
    (htaylor :
      LocalPredictionDominatesLinearization inChart predictionSq linearSq κ)
    (hlin :
      LocalLinearizedRestrictedStrongIdentification
        inChart linearSq parameterSq c h)
    {z : State}
    (hz : inChart z)
    (heq : IsEpsilonEquivalent predictionSq ε z) :
    parameterSq z ≤ ε ^ 2 / ((κ * c) * h) :=
  parameterSq_le_of_epsilonEquivalent_of_localRestrictedStrongIdentification
    inChart predictionSq parameterSq
    (localRestrictedStrongIdentification_of_linearized_and_taylor
      inChart predictionSq linearSq parameterSq htaylor hlin)
    hz heq

/--
Small-epsilon version of the local source-proof decomposition.

This packages the source's "for sufficiently small `ε`" clause with the
Taylor-plus-linearized-identification route, so users of the theorem do not
have to provide chart membership separately for each epsilon-equivalent
representation.
-/
theorem parameterSq_le_of_epsilonEquivalent_of_small_epsilon_local_linearized_taylor
    {State : Type*}
    (inChart : State → Prop)
    (predictionSq linearSq parameterSq : State → ℝ)
    {κ c h ε : ℝ}
    (hsmall : EpsilonEquivalentInsideChart inChart predictionSq ε)
    (htaylor :
      LocalPredictionDominatesLinearization inChart predictionSq linearSq κ)
    (hlin :
      LocalLinearizedRestrictedStrongIdentification
        inChart linearSq parameterSq c h)
    {z : State}
    (heq : IsEpsilonEquivalent predictionSq ε z) :
    parameterSq z ≤ ε ^ 2 / ((κ * c) * h) :=
  parameterSq_le_of_epsilonEquivalent_of_local_linearized_taylor
    inChart predictionSq linearSq parameterSq htaylor hlin (hsmall z heq) heq

/--
Distance-form local source-proof decomposition for the local stability bound.

This combines local Taylor domination, the local linearized quotient lower
bound, and the identification of `parameterSq` with squared quotient distance.
-/
theorem parameterDistance_le_of_epsilonEquivalent_of_local_linearized_taylor
    {State : Type*}
    (inChart : State → Prop)
    (predictionSq linearSq parameterSq parameterDistance : State → ℝ)
    {κ c h ε : ℝ}
    (htaylor :
      LocalPredictionDominatesLinearization inChart predictionSq linearSq κ)
    (hlin :
      LocalLinearizedRestrictedStrongIdentification
        inChart linearSq parameterSq c h)
    (hdistance_nonneg : ∀ z : State, 0 ≤ parameterDistance z)
    (hsq : ∀ z : State, parameterSq z = parameterDistance z ^ 2)
    (hε : 0 ≤ ε)
    {z : State}
    (hz : inChart z)
    (heq : IsEpsilonEquivalent predictionSq ε z) :
    parameterDistance z ≤ ε / Real.sqrt ((κ * c) * h) :=
  parameterDistance_le_of_epsilonEquivalent_of_localRestrictedStrongIdentification
    inChart predictionSq parameterSq parameterDistance
    (localRestrictedStrongIdentification_of_linearized_and_taylor
      inChart predictionSq linearSq parameterSq htaylor hlin)
    hdistance_nonneg hsq hε hz heq

/--
Small-epsilon distance-form source-proof decomposition for the local stability bound.

This is the paper-facing local theorem in distance scale: once the
epsilon-equivalence set lies in the quotient chart, Taylor domination and the
local linearized lower bound imply the `ε / sqrt(h)` rate.
-/
theorem parameterDistance_le_of_epsilonEquivalent_of_small_epsilon_local_linearized_taylor
    {State : Type*}
    (inChart : State → Prop)
    (predictionSq linearSq parameterSq parameterDistance : State → ℝ)
    {κ c h ε : ℝ}
    (hsmall : EpsilonEquivalentInsideChart inChart predictionSq ε)
    (htaylor :
      LocalPredictionDominatesLinearization inChart predictionSq linearSq κ)
    (hlin :
      LocalLinearizedRestrictedStrongIdentification
        inChart linearSq parameterSq c h)
    (hdistance_nonneg : ∀ z : State, 0 ≤ parameterDistance z)
    (hsq : ∀ z : State, parameterSq z = parameterDistance z ^ 2)
    (hε : 0 ≤ ε)
    {z : State}
    (heq : IsEpsilonEquivalent predictionSq ε z) :
    parameterDistance z ≤ ε / Real.sqrt ((κ * c) * h) :=
  parameterDistance_le_of_epsilonEquivalent_of_local_linearized_taylor
    inChart predictionSq linearSq parameterSq parameterDistance htaylor hlin
    hdistance_nonneg hsq hε (hsmall z heq) heq

/--
Source-shaped constant form of the local Taylor-plus-linearized route.

This is the closest formal endpoint to the theorem statement in the current
draft: for sufficiently small `ε`, every epsilon-equivalent representation has
quotient distance at most `(C / sqrt h) * ε` for a positive constant `C`
depending only on the local Taylor and linearized-identification constants.
-/
theorem parameterDistance_le_of_epsilonEquivalent_of_small_epsilon_local_linearized_taylor_exists_constant
    {State : Type*}
    (inChart : State → Prop)
    (predictionSq linearSq parameterSq parameterDistance : State → ℝ)
    {κ c h ε : ℝ}
    (hsmall : EpsilonEquivalentInsideChart inChart predictionSq ε)
    (htaylor :
      LocalPredictionDominatesLinearization inChart predictionSq linearSq κ)
    (hlin :
      LocalLinearizedRestrictedStrongIdentification
        inChart linearSq parameterSq c h)
    (hdistance_nonneg : ∀ z : State, 0 ≤ parameterDistance z)
    (hsq : ∀ z : State, parameterSq z = parameterDistance z ^ 2)
    (hε : 0 ≤ ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {z : State}, IsEpsilonEquivalent predictionSq ε z →
        parameterDistance z ≤ (C / Real.sqrt h) * ε :=
  parameterDistance_le_of_epsilonEquivalent_of_small_epsilon_localRestrictedStrongIdentification_exists_constant
    inChart predictionSq parameterSq parameterDistance hsmall
    (localRestrictedStrongIdentification_of_linearized_and_taylor
      inChart predictionSq linearSq parameterSq htaylor hlin)
    hdistance_nonneg hsq hε

/--
the local stability bound endpoint with the source's heterogeneity index exposed.

This packages the corrected Step 2 proof route: factor Gram lower bounds at
scale `h`, plus an aggregate no-cancellation condition after quotient/gauge
fixing, imply the local linearized restricted-identification premise used by
the source-shaped `C / sqrt(h)` stability theorem.
-/
theorem parameterDistance_le_of_epsilonEquivalent_of_small_epsilon_factorGrams_split_exists_constant
    {K : ℕ} {State Item Model : Type*}
    [Fintype Item] [Fintype Model]
    (inChart : State → Prop)
    (predictionSq parameterDistance : State → ℝ)
    (Ustar : Item → Fin K → ℝ)
    (Vstar : Model → Fin K → ℝ)
    (dU : State → Item → Fin K → ℝ)
    (dV : State → Model → Fin K → ℝ)
    {κ γ h ε : ℝ}
    (hsmall : EpsilonEquivalentInsideChart inChart predictionSq ε)
    (htaylor :
      LocalPredictionDominatesLinearization inChart predictionSq
        (fun z : State => bilinearLinearizedSq Ustar Vstar (dU z) (dV z))
        κ)
    (hγ : 0 < γ)
    (hh : 0 < h)
    (hU : FactorGramLowerBound h Ustar)
    (hV : FactorGramLowerBound h Vstar)
    (hsplit :
      ∀ z : State, inChart z →
        LinearizedSplitLowerBound γ Ustar Vstar (dU z) (dV z))
    (hdistance_nonneg : ∀ z : State, 0 ≤ parameterDistance z)
    (hsq :
      ∀ z : State,
        heterogeneityParameterSq (dU z) (dV z) = parameterDistance z ^ 2)
    (hε : 0 ≤ ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {z : State}, IsEpsilonEquivalent predictionSq ε z →
        parameterDistance z ≤ (C / Real.sqrt h) * ε :=
  parameterDistance_le_of_epsilonEquivalent_of_small_epsilon_local_linearized_taylor_exists_constant
    inChart predictionSq
    (fun z : State => bilinearLinearizedSq Ustar Vstar (dU z) (dV z))
    (fun z : State => heterogeneityParameterSq (dU z) (dV z))
    parameterDistance hsmall htaylor
    (localLinearizedRestrictedStrongIdentification_of_factorGrams_and_split
        inChart Ustar Vstar dU dV hγ hh hU hV hsplit)
    hdistance_nonneg hsq hε

/--
the local stability bound endpoint under a concrete no-cancellation condition.

After quotient/gauge fixing, a nonnegative aggregate cross term means the
linearized item and model perturbation blocks reinforce rather than cancel.
Together with the factor Gram heterogeneity lower bounds, this yields the
source-shaped `C / sqrt(h)` stability rate.
-/
theorem parameterDistance_le_of_epsilonEquivalent_of_small_epsilon_factorGrams_cross_nonnegative_exists_constant
    {K : ℕ} {State Item Model : Type*}
    [Fintype Item] [Fintype Model]
    (inChart : State → Prop)
    (predictionSq parameterDistance : State → ℝ)
    (Ustar : Item → Fin K → ℝ)
    (Vstar : Model → Fin K → ℝ)
    (dU : State → Item → Fin K → ℝ)
    (dV : State → Model → Fin K → ℝ)
    {κ h ε : ℝ}
    (hsmall : EpsilonEquivalentInsideChart inChart predictionSq ε)
    (htaylor :
      LocalPredictionDominatesLinearization inChart predictionSq
        (fun z : State => bilinearLinearizedSq Ustar Vstar (dU z) (dV z))
        κ)
    (hh : 0 < h)
    (hU : FactorGramLowerBound h Ustar)
    (hV : FactorGramLowerBound h Vstar)
    (hcross :
      ∀ z : State, inChart z →
        0 ≤ bilinearLinearizedCrossTerm Ustar Vstar (dU z) (dV z))
    (hdistance_nonneg : ∀ z : State, 0 ≤ parameterDistance z)
    (hsq :
      ∀ z : State,
        heterogeneityParameterSq (dU z) (dV z) = parameterDistance z ^ 2)
    (hε : 0 ≤ ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {z : State}, IsEpsilonEquivalent predictionSq ε z →
        parameterDistance z ≤ (C / Real.sqrt h) * ε :=
  parameterDistance_le_of_epsilonEquivalent_of_small_epsilon_local_linearized_taylor_exists_constant
    inChart predictionSq
    (fun z : State => bilinearLinearizedSq Ustar Vstar (dU z) (dV z))
    (fun z : State => heterogeneityParameterSq (dU z) (dV z))
    parameterDistance hsmall htaylor
    (localLinearizedRestrictedStrongIdentification_of_factorGrams_cross_nonnegative
      inChart Ustar Vstar dU dV hh hU hV hcross)
    hdistance_nonneg hsq hε

/--
the local stability bound as a stability-or-identification-failure dichotomy.

If the local linearized restricted-identification condition holds, the usual
`C / sqrt(h)` stability rate follows.  If it does not hold, there is a local
state whose linearized prediction change is too small relative to its parameter
movement.  This records the high-level interpretation: cancellation is an
identification failure, not merely a proof inconvenience.
-/
theorem parameterDistance_stability_or_local_linearized_identification_failure
    {State : Type*}
    (inChart : State → Prop)
    (predictionSq linearSq parameterSq parameterDistance : State → ℝ)
    {κ c h ε : ℝ}
    (hsmall : EpsilonEquivalentInsideChart inChart predictionSq ε)
    (htaylor :
      LocalPredictionDominatesLinearization inChart predictionSq linearSq κ)
    (hc : 0 < c)
    (hh : 0 < h)
    (hdistance_nonneg : ∀ z : State, 0 ≤ parameterDistance z)
    (hsq : ∀ z : State, parameterSq z = parameterDistance z ^ 2)
    (hε : 0 ≤ ε) :
    (∃ C : ℝ, 0 < C ∧
      ∀ {z : State}, IsEpsilonEquivalent predictionSq ε z →
        parameterDistance z ≤ (C / Real.sqrt h) * ε) ∨
      ∃ z : State, inChart z ∧ linearSq z < c * h * parameterSq z := by
  classical
  by_cases hident :
      LocalLinearizedRestrictedStrongIdentification inChart linearSq parameterSq c h
  · left
    exact
      parameterDistance_le_of_epsilonEquivalent_of_small_epsilon_local_linearized_taylor_exists_constant
        inChart predictionSq linearSq parameterSq parameterDistance hsmall
        htaylor hident hdistance_nonneg hsq hε
  · right
    by_contra hno
    apply hident
    refine ⟨hc, hh, ?_⟩
    intro z hz
    by_contra hle
    exact hno ⟨z, hz, not_le.mp hle⟩

/--
the local stability bound dichotomy with finite Taylor remainder regularity.

This version avoids assuming Taylor domination directly.  Either the
`C / sqrt(h)` stability rate follows, or the local linearized map has a
specific state where its squared prediction movement is too small relative to
the squared quotient-parameter movement.
-/
theorem parameterDistance_stability_or_linearized_identification_failure_remainder
    {State Coord : Type*} [Fintype Coord]
    (inChart : State → Prop)
    (actual linear : State → Coord → ℝ)
    (parameterSq parameterDistance : State → ℝ)
    {c h ε : ℝ}
    (hsmall :
      EpsilonEquivalentInsideChart inChart
        (fun z : State => finiteFunctionSqNorm (actual z)) ε)
    (hremainder :
      ∀ z : State, inChart z →
        4 * finiteFunctionSqNorm (fun coord : Coord => actual z coord - linear z coord) ≤
          finiteFunctionSqNorm (linear z))
    (hc : 0 < c)
    (hh : 0 < h)
    (hdistance_nonneg : ∀ z : State, 0 ≤ parameterDistance z)
    (hsq : ∀ z : State, parameterSq z = parameterDistance z ^ 2)
    (hε : 0 ≤ ε) :
    (∃ C : ℝ, 0 < C ∧
      ∀ {z : State},
        IsEpsilonEquivalent
          (fun z : State => finiteFunctionSqNorm (actual z)) ε z →
        parameterDistance z ≤ (C / Real.sqrt h) * ε) ∨
      ∃ z : State, inChart z ∧
        finiteFunctionSqNorm (linear z) < c * h * parameterSq z := by
  have htaylor :
      LocalPredictionDominatesLinearization inChart
        (fun z : State => finiteFunctionSqNorm (actual z))
        (fun z : State => finiteFunctionSqNorm (linear z))
        (1 / 4 : ℝ) :=
    localPredictionDominatesLinearization_of_remainder_bound
      inChart actual linear hremainder
  exact
    parameterDistance_stability_or_local_linearized_identification_failure
      inChart (fun z : State => finiteFunctionSqNorm (actual z))
      (fun z : State => finiteFunctionSqNorm (linear z))
      parameterSq parameterDistance hsmall htaylor hc hh hdistance_nonneg hsq hε

/--
Bilinear MIRT-shaped version of the linearized-identification dichotomy.

This keeps the exact failure branch from the abstract theorem but rewrites the
linearized squared norm as the source bilinear map:
`<V*_j, dU_i> + <U*_i, dV_j>`.  Thus the alternative is not merely a negative
cross term; it is the semantic failure of the local lower-bound condition
needed for stability.
-/
theorem parameterDistance_stability_or_bilinear_linearized_identification_failure_remainder
    {K : ℕ} {State Item Model Coord : Type*}
    [Fintype Item] [Fintype Model] [Fintype Coord]
    (inChart : State → Prop)
    (actual linear : State → Coord → ℝ)
    (parameterDistance : State → ℝ)
    (Ustar : Item → Fin K → ℝ)
    (Vstar : Model → Fin K → ℝ)
    (dU : State → Item → Fin K → ℝ)
    (dV : State → Model → Fin K → ℝ)
    {c h ε : ℝ}
    (hsmall :
      EpsilonEquivalentInsideChart inChart
        (fun z : State => finiteFunctionSqNorm (actual z)) ε)
    (hremainder :
      ∀ z : State, inChart z →
        4 * finiteFunctionSqNorm (fun coord : Coord => actual z coord - linear z coord) ≤
          finiteFunctionSqNorm (linear z))
    (hlinear :
      ∀ z : State,
        finiteFunctionSqNorm (linear z) =
          bilinearLinearizedSq Ustar Vstar (dU z) (dV z))
    (hc : 0 < c)
    (hh : 0 < h)
    (hdistance_nonneg : ∀ z : State, 0 ≤ parameterDistance z)
    (hsq :
      ∀ z : State,
        heterogeneityParameterSq (dU z) (dV z) = parameterDistance z ^ 2)
    (hε : 0 ≤ ε) :
    (∃ C : ℝ, 0 < C ∧
      ∀ {z : State},
        IsEpsilonEquivalent
          (fun z : State => finiteFunctionSqNorm (actual z)) ε z →
        parameterDistance z ≤ (C / Real.sqrt h) * ε) ∨
      ∃ z : State, inChart z ∧
        bilinearLinearizedSq Ustar Vstar (dU z) (dV z) <
          c * h * heterogeneityParameterSq (dU z) (dV z) := by
  have hmain :=
    parameterDistance_stability_or_linearized_identification_failure_remainder
      inChart actual linear
      (fun z : State => heterogeneityParameterSq (dU z) (dV z))
      parameterDistance hsmall hremainder hc hh hdistance_nonneg hsq hε
  rcases hmain with hstab | hfail
  · exact Or.inl hstab
  · right
    rcases hfail with ⟨z, hz, hlt⟩
    refine ⟨z, hz, ?_⟩
    simpa [hlinear z] using hlt

/--
Factor-Gram version of the local stability bound dichotomy.

Either the quotient/gauge no-cancellation condition holds everywhere locally,
giving the source-shaped stability rate, or there is a local perturbation whose
combined bilinear linearized prediction norm is smaller than the advertised
fraction of the separate item/model block norms.  The latter is the aggregate
cancellation witness.
-/
theorem parameterDistance_stability_or_split_cancellation_witness_of_factorGrams
    {K : ℕ} {State Item Model : Type*}
    [Fintype Item] [Fintype Model]
    (inChart : State → Prop)
    (predictionSq parameterDistance : State → ℝ)
    (Ustar : Item → Fin K → ℝ)
    (Vstar : Model → Fin K → ℝ)
    (dU : State → Item → Fin K → ℝ)
    (dV : State → Model → Fin K → ℝ)
    {κ γ h ε : ℝ}
    (hsmall : EpsilonEquivalentInsideChart inChart predictionSq ε)
    (htaylor :
      LocalPredictionDominatesLinearization inChart predictionSq
        (fun z : State => bilinearLinearizedSq Ustar Vstar (dU z) (dV z))
        κ)
    (hγ : 0 < γ)
    (hh : 0 < h)
    (hU : FactorGramLowerBound h Ustar)
    (hV : FactorGramLowerBound h Vstar)
    (hdistance_nonneg : ∀ z : State, 0 ≤ parameterDistance z)
    (hsq :
      ∀ z : State,
        heterogeneityParameterSq (dU z) (dV z) = parameterDistance z ^ 2)
    (hε : 0 ≤ ε) :
    (∃ C : ℝ, 0 < C ∧
      ∀ {z : State}, IsEpsilonEquivalent predictionSq ε z →
        parameterDistance z ≤ (C / Real.sqrt h) * ε) ∨
      ∃ z : State, inChart z ∧
        bilinearLinearizedSq Ustar Vstar (dU z) (dV z) <
          γ * (itemBlockLinearSq Vstar (dU z) +
            modelBlockLinearSq Ustar (dV z)) := by
  classical
  by_cases hsplit :
      ∀ z : State, inChart z →
        LinearizedSplitLowerBound γ Ustar Vstar (dU z) (dV z)
  · left
    exact
      parameterDistance_le_of_epsilonEquivalent_of_small_epsilon_factorGrams_split_exists_constant
        inChart predictionSq parameterDistance Ustar Vstar dU dV hsmall
        htaylor hγ hh hU hV hsplit hdistance_nonneg hsq hε
  · right
    by_contra hno
    apply hsplit
    intro z hz
    unfold LinearizedSplitLowerBound
    by_contra hle
    exact hno ⟨z, hz, not_le.mp hle⟩

/--
Concrete cross-term dichotomy for the local stability bound.

Either the aggregate cross term is nonnegative throughout the local quotient
chart and the stability bound follows, or some local perturbation has a
negative aggregate cross term.  The second branch is the formal cancellation
witness behind the high-level non-identification interpretation.
-/
theorem parameterDistance_stability_or_negative_cross_witness_of_factorGrams
    {K : ℕ} {State Item Model : Type*}
    [Fintype Item] [Fintype Model]
    (inChart : State → Prop)
    (predictionSq parameterDistance : State → ℝ)
    (Ustar : Item → Fin K → ℝ)
    (Vstar : Model → Fin K → ℝ)
    (dU : State → Item → Fin K → ℝ)
    (dV : State → Model → Fin K → ℝ)
    {κ h ε : ℝ}
    (hsmall : EpsilonEquivalentInsideChart inChart predictionSq ε)
    (htaylor :
      LocalPredictionDominatesLinearization inChart predictionSq
        (fun z : State => bilinearLinearizedSq Ustar Vstar (dU z) (dV z))
        κ)
    (hh : 0 < h)
    (hU : FactorGramLowerBound h Ustar)
    (hV : FactorGramLowerBound h Vstar)
    (hdistance_nonneg : ∀ z : State, 0 ≤ parameterDistance z)
    (hsq :
      ∀ z : State,
        heterogeneityParameterSq (dU z) (dV z) = parameterDistance z ^ 2)
    (hε : 0 ≤ ε) :
    (∃ C : ℝ, 0 < C ∧
      ∀ {z : State}, IsEpsilonEquivalent predictionSq ε z →
        parameterDistance z ≤ (C / Real.sqrt h) * ε) ∨
      ∃ z : State, inChart z ∧
        bilinearLinearizedCrossTerm Ustar Vstar (dU z) (dV z) < 0 := by
  classical
  by_cases hcross :
      ∀ z : State, inChart z →
        0 ≤ bilinearLinearizedCrossTerm Ustar Vstar (dU z) (dV z)
  · left
    exact
      parameterDistance_le_of_epsilonEquivalent_of_small_epsilon_factorGrams_cross_nonnegative_exists_constant
        inChart predictionSq parameterDistance Ustar Vstar dU dV hsmall
        htaylor hh hU hV hcross hdistance_nonneg hsq hε
  · right
    by_contra hno
    apply hcross
    intro z hz
    by_contra hnonneg
    exact hno ⟨z, hz, not_le.mp hnonneg⟩

/--
Fully source-shaped split-failure dichotomy using the finite Taylor remainder
bound rather than taking Taylor domination as a primitive predicate.

This is the cleanest formal version of the proof boundary: either the
`C / sqrt(h)` stability rate holds, or the combined linearized prediction map
does not control the separate item/model tangent blocks at the requested
constant.  The second branch is the local non-identification witness that
replaces a standalone no-cancellation/gauge assumption.
-/
theorem parameterDistance_stability_or_split_cancellation_witness_of_factorGrams_remainder
    {K : ℕ} {State Item Model Coord : Type*}
    [Fintype Item] [Fintype Model] [Fintype Coord]
    (inChart : State → Prop)
    (actual linear : State → Coord → ℝ)
    (parameterDistance : State → ℝ)
    (Ustar : Item → Fin K → ℝ)
    (Vstar : Model → Fin K → ℝ)
    (dU : State → Item → Fin K → ℝ)
    (dV : State → Model → Fin K → ℝ)
    {γ h ε : ℝ}
    (hsmall :
      EpsilonEquivalentInsideChart inChart
        (fun z : State => finiteFunctionSqNorm (actual z)) ε)
    (hremainder :
      ∀ z : State, inChart z →
        4 * finiteFunctionSqNorm (fun c : Coord => actual z c - linear z c) ≤
          finiteFunctionSqNorm (linear z))
    (hlinear :
      ∀ z : State,
        finiteFunctionSqNorm (linear z) =
          bilinearLinearizedSq Ustar Vstar (dU z) (dV z))
    (hγ : 0 < γ)
    (hh : 0 < h)
    (hU : FactorGramLowerBound h Ustar)
    (hV : FactorGramLowerBound h Vstar)
    (hdistance_nonneg : ∀ z : State, 0 ≤ parameterDistance z)
    (hsq :
      ∀ z : State,
        heterogeneityParameterSq (dU z) (dV z) = parameterDistance z ^ 2)
    (hε : 0 ≤ ε) :
    (∃ C : ℝ, 0 < C ∧
      ∀ {z : State},
        IsEpsilonEquivalent (fun z : State => finiteFunctionSqNorm (actual z))
          ε z →
        parameterDistance z ≤ (C / Real.sqrt h) * ε) ∨
      ∃ z : State, inChart z ∧
        bilinearLinearizedSq Ustar Vstar (dU z) (dV z) <
          γ * (itemBlockLinearSq Vstar (dU z) +
            modelBlockLinearSq Ustar (dV z)) := by
  have htaylor_raw :
      LocalPredictionDominatesLinearization inChart
        (fun z : State => finiteFunctionSqNorm (actual z))
        (fun z : State => finiteFunctionSqNorm (linear z))
        (1 / 4 : ℝ) :=
    localPredictionDominatesLinearization_of_remainder_bound
      inChart actual linear hremainder
  have htaylor :
      LocalPredictionDominatesLinearization inChart
        (fun z : State => finiteFunctionSqNorm (actual z))
        (fun z : State => bilinearLinearizedSq Ustar Vstar (dU z) (dV z))
        (1 / 4 : ℝ) := by
    refine ⟨htaylor_raw.1, ?_⟩
    intro z hz
    simpa [hlinear z] using htaylor_raw.2 z hz
  exact
    parameterDistance_stability_or_split_cancellation_witness_of_factorGrams
      inChart (fun z : State => finiteFunctionSqNorm (actual z))
      parameterDistance Ustar Vstar dU dV hsmall htaylor hγ hh hU hV
      hdistance_nonneg hsq hε

/--
Fully source-shaped the local stability bound dichotomy using the finite Taylor remainder
bound rather than taking Taylor domination as a primitive predicate.
-/
theorem parameterDistance_stability_or_negative_cross_witness_of_factorGrams_remainder
    {K : ℕ} {State Item Model Coord : Type*}
    [Fintype Item] [Fintype Model] [Fintype Coord]
    (inChart : State → Prop)
    (actual linear : State → Coord → ℝ)
    (parameterDistance : State → ℝ)
    (Ustar : Item → Fin K → ℝ)
    (Vstar : Model → Fin K → ℝ)
    (dU : State → Item → Fin K → ℝ)
    (dV : State → Model → Fin K → ℝ)
    {h ε : ℝ}
    (hsmall :
      EpsilonEquivalentInsideChart inChart
        (fun z : State => finiteFunctionSqNorm (actual z)) ε)
    (hremainder :
      ∀ z : State, inChart z →
        4 * finiteFunctionSqNorm (fun c : Coord => actual z c - linear z c) ≤
          finiteFunctionSqNorm (linear z))
    (hlinear :
      ∀ z : State,
        finiteFunctionSqNorm (linear z) =
          bilinearLinearizedSq Ustar Vstar (dU z) (dV z))
    (hh : 0 < h)
    (hU : FactorGramLowerBound h Ustar)
    (hV : FactorGramLowerBound h Vstar)
    (hdistance_nonneg : ∀ z : State, 0 ≤ parameterDistance z)
    (hsq :
      ∀ z : State,
        heterogeneityParameterSq (dU z) (dV z) = parameterDistance z ^ 2)
    (hε : 0 ≤ ε) :
    (∃ C : ℝ, 0 < C ∧
      ∀ {z : State},
        IsEpsilonEquivalent (fun z : State => finiteFunctionSqNorm (actual z))
          ε z →
        parameterDistance z ≤ (C / Real.sqrt h) * ε) ∨
      ∃ z : State, inChart z ∧
        bilinearLinearizedCrossTerm Ustar Vstar (dU z) (dV z) < 0 := by
  have htaylor_raw :
      LocalPredictionDominatesLinearization inChart
        (fun z : State => finiteFunctionSqNorm (actual z))
        (fun z : State => finiteFunctionSqNorm (linear z))
        (1 / 4 : ℝ) :=
    localPredictionDominatesLinearization_of_remainder_bound
      inChart actual linear hremainder
  have htaylor :
      LocalPredictionDominatesLinearization inChart
        (fun z : State => finiteFunctionSqNorm (actual z))
        (fun z : State => bilinearLinearizedSq Ustar Vstar (dU z) (dV z))
        (1 / 4 : ℝ) := by
    refine ⟨htaylor_raw.1, ?_⟩
    intro z hz
    simpa [hlinear z] using htaylor_raw.2 z hz
  exact
    parameterDistance_stability_or_negative_cross_witness_of_factorGrams
      inChart (fun z : State => finiteFunctionSqNorm (actual z))
      parameterDistance Ustar Vstar dU dV hsmall htaylor hh hU hV
      hdistance_nonneg hsq hε

/--
One-dimensional IRT-shaped the local stability bound dichotomy.

The heterogeneity scale is the source's one-dimensional Gram index
`min {sum_i U_i^2, sum_j V_j^2}`.  Under finite Taylor remainder control,
either the `C / sqrt(h)` stability rate holds or a local perturbation has a
negative aggregate cross term, i.e. a cancellation/non-identification witness.
-/
theorem parameterDistance_stability_or_negative_cross_witness_oneDim_remainder
    {State Item Model Coord : Type*}
    [Fintype Item] [Fintype Model] [Fintype Coord]
    (inChart : State → Prop)
    (actual linear : State → Coord → ℝ)
    (parameterDistance : State → ℝ)
    (Ustar : Item → Fin 1 → ℝ)
    (Vstar : Model → Fin 1 → ℝ)
    (dU : State → Item → Fin 1 → ℝ)
    (dV : State → Model → Fin 1 → ℝ)
    {ε : ℝ}
    (hsmall :
      EpsilonEquivalentInsideChart inChart
        (fun z : State => finiteFunctionSqNorm (actual z)) ε)
    (hremainder :
      ∀ z : State, inChart z →
        4 * finiteFunctionSqNorm (fun c : Coord => actual z c - linear z c) ≤
          finiteFunctionSqNorm (linear z))
    (hlinear :
      ∀ z : State,
        finiteFunctionSqNorm (linear z) =
          bilinearLinearizedSq Ustar Vstar (dU z) (dV z))
    (hh : 0 < oneDimHeterogeneityIndex Ustar Vstar)
    (hdistance_nonneg : ∀ z : State, 0 ≤ parameterDistance z)
    (hsq :
      ∀ z : State,
        heterogeneityParameterSq (dU z) (dV z) = parameterDistance z ^ 2)
    (hε : 0 ≤ ε) :
    (∃ C : ℝ, 0 < C ∧
      ∀ {z : State},
        IsEpsilonEquivalent (fun z : State => finiteFunctionSqNorm (actual z))
          ε z →
        parameterDistance z ≤
          (C / Real.sqrt (oneDimHeterogeneityIndex Ustar Vstar)) * ε) ∨
      ∃ z : State, inChart z ∧
        bilinearLinearizedCrossTerm Ustar Vstar (dU z) (dV z) < 0 := by
  have hbounds := oneDimHeterogeneityIndex_factorGramLowerBounds Ustar Vstar
  exact
    parameterDistance_stability_or_negative_cross_witness_of_factorGrams_remainder
      inChart actual linear parameterDistance Ustar Vstar dU dV hsmall
      hremainder hlinear hh hbounds.1 hbounds.2 hdistance_nonneg hsq hε

/--
One-dimensional IRT-shaped linearized-identification dichotomy.

The heterogeneity scale is the source's one-dimensional Gram index.  Under
finite Taylor remainder control, either the source-shaped stability rate holds
or the source bilinear linearized map is too small relative to the parameter
movement.  This is the most direct formal version of "heterogeneity gives
stability unless there is a local non-identifiability direction."
-/
theorem parameterDistance_stability_or_bilinear_linearized_identification_failure_oneDim_remainder
    {State Item Model Coord : Type*}
    [Fintype Item] [Fintype Model] [Fintype Coord]
    (inChart : State → Prop)
    (actual linear : State → Coord → ℝ)
    (parameterDistance : State → ℝ)
    (Ustar : Item → Fin 1 → ℝ)
    (Vstar : Model → Fin 1 → ℝ)
    (dU : State → Item → Fin 1 → ℝ)
    (dV : State → Model → Fin 1 → ℝ)
    {c ε : ℝ}
    (hsmall :
      EpsilonEquivalentInsideChart inChart
        (fun z : State => finiteFunctionSqNorm (actual z)) ε)
    (hremainder :
      ∀ z : State, inChart z →
        4 * finiteFunctionSqNorm (fun coord : Coord => actual z coord - linear z coord) ≤
          finiteFunctionSqNorm (linear z))
    (hlinear :
      ∀ z : State,
        finiteFunctionSqNorm (linear z) =
          bilinearLinearizedSq Ustar Vstar (dU z) (dV z))
    (hc : 0 < c)
    (hh : 0 < oneDimHeterogeneityIndex Ustar Vstar)
    (hdistance_nonneg : ∀ z : State, 0 ≤ parameterDistance z)
    (hsq :
      ∀ z : State,
        heterogeneityParameterSq (dU z) (dV z) = parameterDistance z ^ 2)
    (hε : 0 ≤ ε) :
    (∃ C : ℝ, 0 < C ∧
      ∀ {z : State},
        IsEpsilonEquivalent (fun z : State => finiteFunctionSqNorm (actual z))
          ε z →
        parameterDistance z ≤
          (C / Real.sqrt (oneDimHeterogeneityIndex Ustar Vstar)) * ε) ∨
      ∃ z : State, inChart z ∧
        bilinearLinearizedSq Ustar Vstar (dU z) (dV z) <
          c * oneDimHeterogeneityIndex Ustar Vstar *
            heterogeneityParameterSq (dU z) (dV z) :=
  parameterDistance_stability_or_bilinear_linearized_identification_failure_remainder
    inChart actual linear parameterDistance Ustar Vstar dU dV hsmall
    hremainder hlinear hc hh hdistance_nonneg hsq hε

/--
One-dimensional IRT-shaped split-failure dichotomy.

The heterogeneity scale is the source's one-dimensional Gram index.  Under
finite Taylor remainder control, either the source-shaped stability rate holds
or the combined linearized map fails to control the separate item/model
perturbation blocks.  This is the theorem form that avoids adding
no-cancellation as an assumption: cancellation is reported as the other branch
of the dichotomy.
-/
theorem parameterDistance_stability_or_split_cancellation_witness_oneDim_remainder
    {State Item Model Coord : Type*}
    [Fintype Item] [Fintype Model] [Fintype Coord]
    (inChart : State → Prop)
    (actual linear : State → Coord → ℝ)
    (parameterDistance : State → ℝ)
    (Ustar : Item → Fin 1 → ℝ)
    (Vstar : Model → Fin 1 → ℝ)
    (dU : State → Item → Fin 1 → ℝ)
    (dV : State → Model → Fin 1 → ℝ)
    {γ ε : ℝ}
    (hsmall :
      EpsilonEquivalentInsideChart inChart
        (fun z : State => finiteFunctionSqNorm (actual z)) ε)
    (hremainder :
      ∀ z : State, inChart z →
        4 * finiteFunctionSqNorm (fun c : Coord => actual z c - linear z c) ≤
          finiteFunctionSqNorm (linear z))
    (hlinear :
      ∀ z : State,
        finiteFunctionSqNorm (linear z) =
          bilinearLinearizedSq Ustar Vstar (dU z) (dV z))
    (hγ : 0 < γ)
    (hh : 0 < oneDimHeterogeneityIndex Ustar Vstar)
    (hdistance_nonneg : ∀ z : State, 0 ≤ parameterDistance z)
    (hsq :
      ∀ z : State,
        heterogeneityParameterSq (dU z) (dV z) = parameterDistance z ^ 2)
    (hε : 0 ≤ ε) :
    (∃ C : ℝ, 0 < C ∧
      ∀ {z : State},
        IsEpsilonEquivalent (fun z : State => finiteFunctionSqNorm (actual z))
          ε z →
        parameterDistance z ≤
          (C / Real.sqrt (oneDimHeterogeneityIndex Ustar Vstar)) * ε) ∨
      ∃ z : State, inChart z ∧
        bilinearLinearizedSq Ustar Vstar (dU z) (dV z) <
          γ * (itemBlockLinearSq Vstar (dU z) +
            modelBlockLinearSq Ustar (dV z)) := by
  have hbounds := oneDimHeterogeneityIndex_factorGramLowerBounds Ustar Vstar
  exact
    parameterDistance_stability_or_split_cancellation_witness_of_factorGrams_remainder
      inChart actual linear parameterDistance Ustar Vstar dU dV hsmall
      hremainder hlinear hγ hh hbounds.1 hbounds.2 hdistance_nonneg hsq hε

end

end JGR26SubjectivityMonoculture
