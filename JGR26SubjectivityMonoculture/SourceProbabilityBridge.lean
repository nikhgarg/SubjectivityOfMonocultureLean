import JGR26SubjectivityMonoculture.VertexMixtureMeasure
import JGR26SubjectivityMonoculture.ResidualDiscrepancyBridge
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Actual probability laws for IRT and latent vertex mixtures

The source link takes values in the probability interval. An IRT row is an
actual product PMF, not an arbitrary real product of factors. The probit
specialization is the CDF of the standard Gaussian measure. The vertex-mixture
construction includes a joint latent/response PMF and positive-atom conditional
probabilities under that joint law. All finite conditional independence claims
are expressed through event factorization; no assertion is made at null atoms.

The probit implementation uses the pinned Apache-2.0 Mathlib modules
`Mathlib.Probability.CDF` and `Mathlib.Probability.Distributions.Gaussian.Real`;
the link is specifically `cdf (gaussianReal 0 1)`, whose probability range is
proved by Mathlib's `cdf_nonneg` and `cdf_le_one`. Mathlib is pinned to
`v4.30.0-rc2`, commit `5450b53e5ddc75d46418fabb605edbf36bd0beb6`:
<https://github.com/leanprover-community/mathlib4/tree/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Probability>.
-/

namespace JGR26SubjectivityMonoculture

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology unitInterval ProbabilityTheory

noncomputable section

/-- A finite independent Bernoulli response PMF with probability-valued parameters. -/
def probabilityRowPMF {Model : Type*} [Fintype Model] [DecidableEq Model]
    (p : Model → unitInterval) : PMF (Model → Bool) :=
  AppliedModelingLib.pmfPi (fun j => realBernoulliPMF (p j) (p j).2.1 (p j).2.2)

theorem probabilityRowPMF_toReal {Model : Type*} [Fintype Model] [DecidableEq Model]
    (p : Model → unitInterval) (y : Model → Bool) :
    (probabilityRowPMF p y).toReal =
      ∏ j, if y j then (p j : ℝ) else 1 - (p j : ℝ) :=
  productBernoulliPMF_toReal_eq_mass (fun j => p j) (fun j => (p j).2) y

/-- The actual product PMF has the corresponding product probability measure. -/
theorem probabilityRowPMF_toMeasure {Model : Type*} [Fintype Model] [DecidableEq Model]
    (p : Model → unitInterval) :
    (probabilityRowPMF p).toMeasure =
      Measure.pi (fun j => (realBernoulliPMF (p j) (p j).2.1 (p j).2.2).toMeasure) := by
  apply Measure.ext_of_singleton
  intro y
  rw [PMF.toMeasure_apply_singleton _ y (measurableSet_singleton _),
    probabilityRowPMF, AppliedModelingLib.pmfPi_apply, Measure.pi_singleton]
  congr with j
  rw [PMF.toMeasure_apply_singleton _ (y j) (measurableSet_singleton _)]

/-- Coordinates under the probability-valued row constructor are mutually independent. -/
theorem probabilityRowPMF_independent
    {Model : Type*} [Fintype Model] [DecidableEq Model] (p : Model → unitInterval) :
    iIndepFun (fun j (y : Model → Bool) => y j) (probabilityRowPMF p).toMeasure := by
  rw [probabilityRowPMF_toMeasure]
  letI : ∀ j : Model,
      IsProbabilityMeasure (realBernoulliPMF (p j) (p j).2.1 (p j).2.2).toMeasure :=
    fun _ => inferInstance
  exact iIndepFun_pi (X := fun _ => (id : Bool → Bool)) (fun _ => aemeasurable_id)

theorem probabilityRowPMF_successProbability
    {Model : Type*} [Fintype Model] [DecidableEq Model]
    (p : Model → unitInterval) (j : Model) :
    AppliedModelingLib.pmfProb (probabilityRowPMF p) (fun y => y j = true) = p j := by
  rw [probabilityRowPMF]
  rw [AppliedModelingLib.pmfProb_pmfPi_eval_eq
    (fun k => realBernoulliPMF (p k) (p k).2.1 (p k).2.2) j (fun b => b = true)]
  simp [AppliedModelingLib.pmfProb, AppliedModelingLib.pmfExp]

/-- The probability-valued standard-normal CDF is the source's probit link. -/
def sourceProbitLink (x : ℝ) : unitInterval :=
  ⟨cdf (gaussianReal 0 1) x,
    cdf_nonneg (gaussianReal 0 1) x, cdf_le_one (gaussianReal 0 1) x⟩

theorem sourceProbitLink_eq_standardNormalProbability (x : ℝ) :
    (sourceProbitLink x : ℝ) = (gaussianReal 0 1).real (Iic x) :=
  cdf_eq_real (gaussianReal 0 1) x

theorem sourceProbitLink_monotone : Monotone (fun x => (sourceProbitLink x : ℝ)) :=
  monotone_cdf (gaussianReal 0 1)

/-- IRT's fixed-parameter conditional row law is an actual Bernoulli product PMF. -/
def sourceMIRTItemPMF {K : ℕ} {Item Model : Type*} [Fintype Model] [DecidableEq Model]
    (link : ℝ → unitInterval) (itemSlope : Item → Fin K → ℝ)
    (itemDifficulty : Item → ℝ) (modelAbility : Model → Fin K → ℝ)
    (i : Item) : PMF (Model → Bool) :=
  probabilityRowPMF (fun j =>
    link (finiteDot (itemSlope i) (modelAbility j) + itemDifficulty i))

/-- The PMF's real mass is exactly the source's IRT product formula. -/
theorem sourceMIRTItemPMF_toReal
    {K : ℕ} {Item Model : Type*} [Fintype Model] [DecidableEq Model]
    (link : ℝ → unitInterval) (itemSlope : Item → Fin K → ℝ)
    (itemDifficulty : Item → ℝ) (modelAbility : Model → Fin K → ℝ)
    (i : Item) (y : Model → Bool) :
    (sourceMIRTItemPMF link itemSlope itemDifficulty modelAbility i y).toReal =
      MIRTItemLaw (fun x => (link x : ℝ)) itemSlope itemDifficulty modelAbility i y :=
  probabilityRowPMF_toReal _ y

theorem sourceMIRTItemPMF_independent
    {K : ℕ} {Item Model : Type*} [Fintype Model] [DecidableEq Model]
    (link : ℝ → unitInterval) (itemSlope : Item → Fin K → ℝ)
    (itemDifficulty : Item → ℝ) (modelAbility : Model → Fin K → ℝ) (i : Item) :
    iIndepFun (fun j (y : Model → Bool) => y j)
      (sourceMIRTItemPMF link itemSlope itemDifficulty modelAbility i).toMeasure :=
  probabilityRowPMF_independent _

theorem sourceMIRTItemPMF_successProbability
    {K : ℕ} {Item Model : Type*} [Fintype Model] [DecidableEq Model]
    (link : ℝ → unitInterval) (itemSlope : Item → Fin K → ℝ)
    (itemDifficulty : Item → ℝ) (modelAbility : Model → Fin K → ℝ) (i : Item) (j : Model) :
    AppliedModelingLib.pmfProb (sourceMIRTItemPMF link itemSlope itemDifficulty modelAbility i)
      (fun y => y j = true) =
      (link (finiteDot (itemSlope i) (modelAbility j) + itemDifficulty i) : ℝ) :=
  probabilityRowPMF_successProbability _ j

/-- Definition 1 as a family of genuine laws with one fixed probability-valued link. -/
def sourceProbabilityMIRTNull {Item Model : Type*} [Fintype Model]
    (K : ℕ) (link : ℝ → unitInterval) (Q : Item → PMF (Model → Bool)) : Prop := by
  classical
  exact ∃ itemSlope : Item → Fin K → ℝ, ∃ itemDifficulty : Item → ℝ,
    ∃ modelAbility : Model → Fin K → ℝ,
      Q = sourceMIRTItemPMF link itemSlope itemDifficulty modelAbility

/-- Definition 1's chosen probit null, as a family of actual conditional row PMFs. -/
def sourceProbitMIRTNull {Item Model : Type*} [Fintype Model]
    (K : ℕ) (Q : Item → PMF (Model → Bool)) : Prop :=
  sourceProbabilityMIRTNull K sourceProbitLink Q

/-- Zero padding preserves the same probability-valued link and the actual response law. -/
theorem sourceProbabilityMIRTNull_nested
    {Item Model : Type*} [Fintype Model]
    (K : ℕ) (link : ℝ → unitInterval) (Q : Item → PMF (Model → Bool)) :
    sourceProbabilityMIRTNull K link Q → sourceProbabilityMIRTNull (K + 1) link Q := by
  classical
  rintro ⟨a, d, θ, rfl⟩
  refine ⟨fun i => extendFinVectorZero (a i), d,
    fun j => extendFinVectorZero (θ j), ?_⟩
  funext i
  simp only [sourceMIRTItemPMF, finiteDot_extendFinVectorZero_eq]

/-- A binary response vector has a unique probability-cube vertex. -/
theorem responseProbabilityVertex_injective {m : ℕ} :
    Function.Injective (responseProbabilityVertex (m := m)) := by
  intro y z h
  funext j
  have hj := congrArg (fun p : Fin m → unitInterval => (p j : ℝ)) h
  cases hy : y j <;> cases hz : z j <;>
    simp [responseProbabilityVertex, hy, hz] at hj ⊢

/-- The joint latent/response law realizes the source's vertex construction. -/
def vertexLatentResponsePMF {m : ℕ} (P : PMF (Fin m → Bool)) :
    PMF ((Fin m → unitInterval) × (Fin m → Bool)) :=
  P.map (fun y => (responseProbabilityVertex y, y))

theorem vertexLatentResponsePMF_response_marginal {m : ℕ} (P : PMF (Fin m → Bool)) :
    (vertexLatentResponsePMF P).map Prod.snd = P := by
  rw [vertexLatentResponsePMF, PMF.map_comp]
  exact PMF.map_id P

theorem vertexLatentResponsePMF_latent_marginal {m : ℕ} (P : PMF (Fin m → Bool)) :
    ((vertexLatentResponsePMF P).map Prod.fst).toMeasure = vertexMixingMeasure P := by
  rw [vertexLatentResponsePMF, PMF.map_comp]
  exact (PMF.toMeasure_map responseProbabilityVertex P
    (measurable_of_finite responseProbabilityVertex)).symm

/-- Conditional probabilities are ratios of actual joint event probabilities. -/
def jointConditionalResponseProbability {m : ℕ}
    (J : PMF ((Fin m → unitInterval) × (Fin m → Bool)))
    (p : Fin m → unitInterval) (event : (Fin m → Bool) → Prop) : ℝ :=
  (J.toMeasure {z | z.1 = p ∧ event z.2}).toReal /
    (J.toMeasure {z | z.1 = p}).toReal

def vertexConditionalResponseProbability {m : ℕ} (P : PMF (Fin m → Bool))
    (p : Fin m → unitInterval) (event : (Fin m → Bool) → Prop) : ℝ :=
  jointConditionalResponseProbability (vertexLatentResponsePMF P) p event

theorem vertexLatentResponsePMF_joint_event {m : ℕ} (P : PMF (Fin m → Bool))
    (v : Fin m → Bool) (event : (Fin m → Bool) → Prop) :
    (vertexLatentResponsePMF P).toMeasure
      {z | z.1 = responseProbabilityVertex v ∧ event z.2} =
      ({y | event y} : Set (Fin m → Bool)).indicator P v := by
  classical
  have hevent : MeasurableSet {y : Fin m → Bool | event y} :=
    (Set.toFinite _).measurableSet
  have hset : MeasurableSet
      {z : (Fin m → unitInterval) × (Fin m → Bool) |
        z.1 = responseProbabilityVertex v ∧ event z.2} :=
    ((measurableSet_singleton _).preimage measurable_fst).inter
      (hevent.preimage measurable_snd)
  rw [vertexLatentResponsePMF,
    PMF.toMeasure_map_apply _ _ _ (measurable_of_finite _) hset]
  have hpre : (fun y : Fin m → Bool => (responseProbabilityVertex y, y)) ⁻¹'
      {z | z.1 = responseProbabilityVertex v ∧ event z.2} =
      if event v then {v} else ∅ := by
    ext y
    simp only [mem_preimage, mem_setOf_eq,
      responseProbabilityVertex_injective.eq_iff]
    by_cases hy : y = v
    · subst y
      by_cases hv : event v <;> simp [hv]
    · simp [hy]
  rw [hpre]
  by_cases hv : event v <;> simp [hv, Set.indicator]

theorem vertexLatentResponsePMF_latent_atom {m : ℕ} (P : PMF (Fin m → Bool))
    (v : Fin m → Bool) :
    (vertexLatentResponsePMF P).toMeasure {z | z.1 = responseProbabilityVertex v} = P v := by
  simpa using vertexLatentResponsePMF_joint_event P v (fun _ => True)

/-- At every positive latent atom, the conditional response is exactly its binary vertex. -/
theorem vertexConditionalResponseProbability_eq_indicator
    {m : ℕ} (P : PMF (Fin m → Bool)) (v : Fin m → Bool)
    (hv : 0 < (P v).toReal) (event : (Fin m → Bool) → Prop) :
    vertexConditionalResponseProbability P (responseProbabilityVertex v) event =
      ({y | event y} : Set (Fin m → Bool)).indicator (fun _ => (1 : ℝ)) v := by
  classical
  rw [vertexConditionalResponseProbability, jointConditionalResponseProbability,
    vertexLatentResponsePMF_joint_event,
    vertexLatentResponsePMF_latent_atom]
  by_cases hevent : event v <;> simp [hevent, Set.indicator, ne_of_gt hv]

/-- The conditional Bernoulli success parameter is the actual latent coordinate. -/
theorem vertexConditionalResponseProbability_success
    {m : ℕ} (P : PMF (Fin m → Bool)) (v : Fin m → Bool)
    (hv : 0 < (P v).toReal) (j : Fin m) :
    vertexConditionalResponseProbability P (responseProbabilityVertex v)
      (fun y => y j = true) = (responseProbabilityVertex v j : ℝ) := by
  rw [vertexConditionalResponseProbability_eq_indicator P v hv]
  cases h : v j <;> simp [h, responseProbabilityVertex, Set.indicator]

/-- The conditional joint response mass is the independent Bernoulli product mass. -/
theorem vertexConditionalResponseProbability_response_atom
    {m : ℕ} (P : PMF (Fin m → Bool)) (v : Fin m → Bool)
    (hv : 0 < (P v).toReal) (y : Fin m → Bool) :
    vertexConditionalResponseProbability P (responseProbabilityVertex v)
      (fun z => z = y) = cubeBernoulliMass (responseProbabilityVertex v) y := by
  classical
  rw [vertexConditionalResponseProbability_eq_indicator P v hv, cubeBernoulliMass_vertex]
  simp only [vertexLaw, Set.indicator, mem_setOf_eq]
  simp only [eq_comm]

/-- Conditional independence holds for every finite family of coordinate events. -/
theorem vertexConditionalResponseProbability_independence
    {m : ℕ} (P : PMF (Fin m → Bool)) (v : Fin m → Bool)
    (hv : 0 < (P v).toReal) (s : Finset (Fin m)) (events : Fin m → Set Bool) :
    vertexConditionalResponseProbability P (responseProbabilityVertex v)
      (fun y => ∀ j ∈ s, y j ∈ events j) =
      ∏ j ∈ s, vertexConditionalResponseProbability P (responseProbabilityVertex v)
        (fun y => y j ∈ events j) := by
  classical
  simp only [vertexConditionalResponseProbability_eq_indicator P v hv,
    Set.indicator, mem_setOf_eq]
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
      rw [Finset.prod_insert hj]
      by_cases hevent : v j ∈ events j <;>
        simp only [Finset.mem_insert, forall_eq_or_imp, hevent, true_and, false_and,
          ↓reduceIte, zero_mul, one_mul, ih]

/-- A latent cube atom is the mass of its actual marginal PMF. -/
theorem vertexMixingMeasure_atom {m : ℕ} (P : PMF (Fin m → Bool))
    (p : Fin m → unitInterval) :
    vertexMixingMeasure P {p} = (P.map responseProbabilityVertex) p := by
  rw [vertexMixingMeasure,
    PMF.toMeasure_map responseProbabilityVertex P (measurable_of_finite _),
    PMF.toMeasure_apply_singleton _ p (measurableSet_singleton _)]

/-- Every positive latent atom is a positive-mass binary vertex. -/
theorem vertexMixingMeasure_positive_atom {m : ℕ} (P : PMF (Fin m → Bool))
    (p : Fin m → unitInterval) (hp : 0 < (vertexMixingMeasure P {p}).toReal) :
    ∃ v : Fin m → Bool, responseProbabilityVertex v = p ∧ 0 < (P v).toReal := by
  rw [vertexMixingMeasure_atom] at hp
  have hnonzero : (P.map responseProbabilityVertex) p ≠ 0 := by
    intro hzero
    simp [hzero] at hp
  obtain ⟨v, hv, hvertex⟩ := (PMF.mem_support_map_iff responseProbabilityVertex P p).mp
    ((PMF.mem_support_iff _ p).mpr hnonzero)
  exact ⟨v, hvertex, ENNReal.toReal_pos ((PMF.mem_support_iff P v).mp hv) (P.apply_ne_top v)⟩

/-- The mixing measure gives its vertex exactly the original response mass. -/
theorem vertexMixingMeasure_vertex_atom {m : ℕ} (P : PMF (Fin m → Bool))
    (v : Fin m → Bool) : vertexMixingMeasure P {responseProbabilityVertex v} = P v := by
  rw [← vertexLatentResponsePMF_latent_marginal P,
    PMF.toMeasure_map_apply _ _ _ measurable_fst (measurableSet_singleton _)]
  exact vertexLatentResponsePMF_latent_atom P v

/-- Full-measure finite support can omit every zero-mass vertex. -/
theorem vertexMixingMeasure_positive_finite_support {m : ℕ} (P : PMF (Fin m → Bool)) :
    ∃ S : Finset (Fin m → unitInterval), S.card ≤ 2 ^ m ∧
      vertexMixingMeasure P (S : Set _) = 1 ∧
      ∀ p ∈ S, 0 < (vertexMixingMeasure P {p}).toReal := by
  classical
  let V : Finset (Fin m → Bool) := Finset.univ.filter (fun v => P v ≠ 0)
  let S := V.image responseProbabilityVertex
  refine ⟨S, ?_, ?_, ?_⟩
  · calc
      S.card ≤ V.card := Finset.card_image_le
      _ ≤ (Finset.univ : Finset (Fin m → Bool)).card := Finset.card_filter_le _ _
      _ = 2 ^ m := by simp
  · rw [vertexMixingMeasure, Measure.map_apply (measurable_of_finite _)
      (Finset.measurableSet S), PMF.toMeasure_apply_eq_one_iff P
        ((Set.toFinite _).measurableSet)]
    intro v hv
    change responseProbabilityVertex v ∈ S
    exact Finset.mem_image.mpr ⟨v, by simpa [V] using (PMF.mem_support_iff P v).mp hv, rfl⟩
  · intro p hp
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
    rw [vertexMixingMeasure_vertex_atom]
    exact ENNReal.toReal_pos (by simpa [V] using hv) (P.apply_ne_top v)

/--
Theorem 1's full probability construction: one joint latent/response law has
the prescribed response marginal, the finite cube mixing marginal, and the
conditional independent Bernoulli law at every positive latent atom. The
finite support contains only positive atoms, so these conditional clauses
cover a set of full mixing measure.
-/
theorem source_theorem1_joint_vertex_mixture {m : ℕ} (P : PMF (Fin m → Bool)) :
    ∃ J : PMF ((Fin m → unitInterval) × (Fin m → Bool)),
      ∃ H : Measure (Fin m → unitInterval), IsProbabilityMeasure H ∧
        J.map Prod.snd = P ∧ (J.map Prod.fst).toMeasure = H ∧
        (∀ y, (∫ p, cubeBernoulliMass p y ∂H) = (P y).toReal) ∧
        (∃ S : Finset (Fin m → unitInterval), S.card ≤ 2 ^ m ∧ H (S : Set _) = 1 ∧
          ∀ p ∈ S, 0 < (H {p}).toReal) ∧
        ∀ p, 0 < (H {p}).toReal →
          (∀ j, jointConditionalResponseProbability J p (fun y => y j = true) = (p j : ℝ)) ∧
          (∀ y, jointConditionalResponseProbability J p (fun z => z = y) =
            cubeBernoulliMass p y) ∧
          (∀ s : Finset (Fin m), ∀ events : Fin m → Set Bool,
            jointConditionalResponseProbability J p (fun y => ∀ j ∈ s, y j ∈ events j) =
              ∏ j ∈ s, jointConditionalResponseProbability J p (fun y => y j ∈ events j)) := by
  refine ⟨vertexLatentResponsePMF P, vertexMixingMeasure P, inferInstance,
    vertexLatentResponsePMF_response_marginal P,
    vertexLatentResponsePMF_latent_marginal P, vertexMixingMeasure_integral P,
    vertexMixingMeasure_positive_finite_support P, ?_⟩
  intro p hp
  obtain ⟨v, rfl, hv⟩ := vertexMixingMeasure_positive_atom P p hp
  exact ⟨vertexConditionalResponseProbability_success P v hv,
    vertexConditionalResponseProbability_response_atom P v hv,
    vertexConditionalResponseProbability_independence P v hv⟩

/-- The finite-law representation has exactly the actual PMF's Bochner expectation. -/
theorem finiteLawExpectation_eq_PMF_integral
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω]
    (P : PMF Ω) (f : Ω → ℝ) :
    finiteLawExpectation (finiteLawOfPMF P) f = (∫ ω, f ω ∂P.toMeasure) := by
  rw [PMF.integral_eq_sum]
  simp only [finiteLawExpectation, finiteLawOfPMF, smul_eq_mul]

end

end JGR26SubjectivityMonoculture
