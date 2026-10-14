import JGR26SubjectivityMonoculture.VertexMixtureMeasure
import JGR26SubjectivityMonoculture.MIRTIdentification
import JGR26SubjectivityMonoculture.BalancedSourceBridge
import JGR26SubjectivityMonoculture.BalancedNormalizationExamples
import JGR26SubjectivityMonoculture.LogisticPopulationRelativity
import JGR26SubjectivityMonoculture.ResidualCalibration
import JGR26SubjectivityMonoculture.ResidualDiscrepancyBridge
import JGR26SubjectivityMonoculture.EmpiricalResiduals
import JGR26SubjectivityMonoculture.HeterogeneityCounterexamples
import JGR26SubjectivityMonoculture.PopulationRelativity
import JGR26SubjectivityMonoculture.SourceModelDefinitions
import JGR26SubjectivityMonoculture.SourceNormalizationInterface
import JGR26SubjectivityMonoculture.SourceProbabilityBridge

/-!
# The Subjectivity of Monoculture: source-facing draft interface

The mixture, absorption, residual-limit, local-stability and nestedness claims
use actual probability laws and factor arrays. The source link is fixed across
a null ladder and a population comparison. All parameter and prediction norms
are Euclidean sums of squares.
-/

namespace JGR26SubjectivityMonoculture

open Filter MeasureTheory Set
open scoped BigOperators Topology RealInnerProductSpace

noncomputable section

/-- Nonnegative discrepancy on a nonempty null family has a finite, approachable infimum. -/
theorem draftMinimalExcess_exists_of_nonempty {Law : Type*} (D : Law → Law → ℝ)
    (P : Law) (N : Set Law) (hne : N.Nonempty) (hnonneg : ∀ Q ∈ N, 0 ≤ D P Q) :
    ∃ excess, draftMinimalExcess D P N excess := by
  have hvalues : (discrepancyValues D P N).Nonempty := by
    obtain ⟨Q, hQ⟩ := hne
    exact ⟨D P Q, Q, hQ, rfl⟩
  have hbdd : BddBelow (discrepancyValues D P N) := by
    refine ⟨0, ?_⟩
    rintro x ⟨Q, hQ, rfl⟩
    exact hnonneg Q hQ
  refine ⟨sInf (discrepancyValues D P N),
    (draftMinimalExcess_iff_infimum D P N _).mpr ⟨fun x hx => csInf_le hbdd hx, ?_⟩⟩
  intro epsilon hepsilon
  obtain ⟨x, hx, hlt⟩ := exists_lt_of_csInf_lt hvalues
    (lt_add_of_pos_right (sInf (discrepancyValues D P N)) hepsilon)
  exact ⟨x, hx, hlt.le⟩

/-- Theorem 1: a discrete mixing probability measure on the cube recovers every binary law. -/
def draftTheorem1Spec (m : ℕ) (P : PMF (Fin m → Bool)) : Prop :=
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
            ∏ j ∈ s, jointConditionalResponseProbability J p (fun y => y j ∈ events j))

theorem draftTheorem1 (m : ℕ) (P : PMF (Fin m → Bool)) : draftTheorem1Spec m P :=
  source_theorem1_joint_vertex_mixture P

/-- Proposition 2: infimum excess is nonincreasing along a null ladder. -/
def draftProposition2Spec {Law : Type*} (D : Law → Law → ℝ)
    (P : Law) (N : ℕ → Set Law) : Prop :=
  draftNullLadder N → ∀ K excessK excessSucc,
    draftMinimalExcess D P (N K) excessK →
    draftMinimalExcess D P (N (K + 1)) excessSucc → excessSucc ≤ excessK

theorem draftProposition2 {Law : Type*} (D : Law → Law → ℝ)
    (P : Law) (N : ℕ → Set Law) : draftProposition2Spec D P N := by
  intro hNested K excessK excessSucc hK hSucc
  exact infimumMinimalExcess_nonincreasing D P N K hNested
    ((draftMinimalExcess_iff_infimum D P (N K) excessK).mp hK)
    ((draftMinimalExcess_iff_infimum D P (N (K + 1)) excessSucc).mp hSucc)

local instance finiteResponseArrayFintype {Item Model : Type*}
    [Fintype Item] [Fintype Model] : Fintype (Item → Model → Bool) := by
  classical
  infer_instance

/-- Theorem 3: conditional product item marginals and qualitative discrepancy control suffice. -/
def draftTheorem3Spec {Item Model : Type*}
    [Fintype Item] [Nonempty Item] [Fintype Model]
    (D : FiniteLaw (Item → Model → Bool) → FiniteLaw (Item → Model → Bool) → ℝ)
    (observed : FiniteLaw (Item → Model → Bool))
    (fitted : ℕ → FiniteLaw (Item → Model → Bool)) (p : ℕ → Item → Model → ℝ) : Prop :=
  ControlsBoundedExpectationsAtZero D → (∀ K i m, 0 ≤ p K i m ∧ p K i m ≤ 1) →
    (∀ K, HasProductBernoulliItemRowMarginals (fitted K) (p K)) →
    Tendsto (fun K => D observed (fitted K)) atTop (𝓝 0) → ∀ j ℓ, j ≠ ℓ →
      Tendsto (fun K => finiteLawExpectation observed (averagePairResidualFunctional (p K) j ℓ))
        atTop (𝓝 0)

theorem draftTheorem3 {Item Model : Type*}
    [Fintype Item] [Nonempty Item] [Fintype Model]
    (D : FiniteLaw (Item → Model → Bool) → FiniteLaw (Item → Model → Bool) → ℝ)
    (observed : FiniteLaw (Item → Model → Bool))
    (fitted : ℕ → FiniteLaw (Item → Model → Bool)) (p : ℕ → Item → Model → ℝ) :
    draftTheorem3Spec D observed fitted p := by
  intro hD hp hrows hlim j ℓ hjℓ
  exact averagePairResidual_tendsto_zero_of_productItemRowMarginals_and_qualitative_discrepancy
    hD observed fitted p j ℓ hjℓ hp hrows hlim

/-- Lemma 6: zero padding nests actual IRT laws with the same source probit link. -/
def draftLemma6Spec {Item Model : Type*} [Fintype Model] (K : ℕ) : Prop :=
  ∀ Q : Item → PMF (Model → Bool),
    sourceProbitMIRTNull K Q → sourceProbitMIRTNull (K + 1) Q

theorem draftLemma6 {Item Model : Type*} [Fintype Model] (K : ℕ) :
    draftLemma6Spec (Item := Item) (Model := Model) K := by
  intro Q hQ
  exact sourceProbabilityMIRTNull_nested K sourceProbitLink Q hQ

section SourceArrays

variable {K : ℕ} {Item Model : Type*} [Fintype Item] [Fintype Model]

/-- Theorem 5 uses the actual minimum-Gram heterogeneity and the exact prediction fiber. -/
def draftTheorem5Spec (hK : 0 < K)
    (link : EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin K) → ℝ)
    (admissible : Set (SourceFactorParameter Item Model K))
    (probabilities : SourcePredictionArray Item Model)
    (fit : SourceFactorParameter Item Model K) : Prop :=
  sourceSpecifiedAdmissibleFit link admissible probabilities fit →
    (∀ uv, 0 < link uv ∧ link uv < 1) →
    0 < sourceHeterogeneity hK fit → ContDiff ℝ 2 link → ∀ c > 0,
    HasLocalIdentificationAt (sourcePrediction link) fit c (sourceHeterogeneity hK fit) →
    ∃ radius > 0, ∃ C > 0, ∀ epsilon > 0,
      sSup ((fun z => Metric.infDist z {w | sourcePrediction link w = probabilities}) ''
        {z | dist z fit < radius ∧
          (∑ i, ∑ j,
            (link (sourceItemFactor i z, sourceModelFactor j z) -
              probabilities (i, j)) ^ 2) ≤ epsilon ^ 2}) ≤
        (C / Real.sqrt (sourceHeterogeneity hK fit)) * epsilon

theorem draftTheorem5 (hK : 0 < K)
    (link : EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin K) → ℝ)
    (admissible : Set (SourceFactorParameter Item Model K))
    (probabilities : SourcePredictionArray Item Model)
    (fit : SourceFactorParameter Item Model K) :
    draftTheorem5Spec hK link admissible probabilities fit := by
  intro hfit _hlink hh hsmooth c hc hid
  rw [← hfit.2]
  exact source_theorem5_local_heterogeneity link fit hc hh hsmooth hid

/-- Lemma 8: the attained positive derivative minimum gives identification in both domains. -/
def draftLemma8Spec [Nonempty Item] [Nonempty Model] (hK : 0 < K)
    (g : ℝ → ℝ) (fit : SourceFactorParameter Item Model K) : Prop :=
  (∀ t, 0 < g t ∧ g t < 1) →
    ContDiff ℝ 2 g → (∀ t, 0 < deriv g t) → 0 < sourceHeterogeneity hK fit →
    ∃ m > 0,
      (∃ i j, m = deriv g ⟪sourceItemFactor i fit, sourceModelFactor j fit⟫) ∧
      (∀ i j, m ≤ deriv g ⟪sourceItemFactor i fit, sourceModelFactor j fit⟫) ∧
      HasLocalIdentificationAt (sourcePrediction (fun uv => g ⟪uv.1, uv.2⟫)) fit
        (m ^ 2) (sourceHeterogeneity hK fit) ∧
      ∀ fixed : Finset (Fin K),
        HasLocalIdentificationAt (sourceMIRTPredictionWithin fixed g fit) 0
          (m ^ 2) (sourceHeterogeneity hK fit)

theorem draftLemma8 [Nonempty Item] [Nonempty Model] (hK : 0 < K)
    (g : ℝ → ℝ) (fit : SourceFactorParameter Item Model K) : draftLemma8Spec hK g fit := by
  intro _hg hsmooth hpositive hh
  obtain ⟨hU, hV⟩ := sourceHeterogeneity_lowerBounds hK fit
  obtain ⟨m, hm, hattain, hweight, hid⟩ :=
    source_lemma8_mirt_identification g hsmooth hpositive fit hh hU hV
  exact ⟨m, hm, hattain, hweight, hid, fun fixed =>
    source_mirt_localIdentificationWithin_of_gramLowerBounds fixed g hsmooth hpositive
      fit hm hh hweight hU hV⟩

end SourceArrays

/-- Proposed Proposition 7 finite-sample scope: demeaning removes the average calibration error. -/
def proposedDebiasingSpec {Item Model : Type*} [Fintype Item] [Nonempty Item]
    (response truth fitted : Item → Model → ℝ) : Prop :=
  (∀ j, ∑ i, debiasedResidual (fun i j => response i j - fitted i j) i j = 0) ∧
    ∀ i j, debiasedResidual (fun i j => response i j - fitted i j) i j =
      debiasedResidual (fun i j => response i j - truth i j) i j +
        debiasedResidual (fun i j => truth i j - fitted i j) i j

theorem proposedDebiasing {Item Model : Type*} [Fintype Item] [Nonempty Item]
    (response truth fitted : Item → Model → ℝ) : proposedDebiasingSpec response truth fitted := by
  exact ⟨fun j => debiasedResidual_sum_eq_zero (fun i j => response i j - fitted i j) j,
    debiasedResidual_calibration_decomposition response truth fitted⟩

end

end JGR26SubjectivityMonoculture
