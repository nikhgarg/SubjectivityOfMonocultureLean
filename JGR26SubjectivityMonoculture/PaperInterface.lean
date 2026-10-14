import JGR26SubjectivityMonoculture.VertexMixtureMeasure
import JGR26SubjectivityMonoculture.MIRTIdentification
import JGR26SubjectivityMonoculture.BalancedSourceBridge
import JGR26SubjectivityMonoculture.BalancedNormalizationExamples
import JGR26SubjectivityMonoculture.LogisticPopulationRelativity
import JGR26SubjectivityMonoculture.ResidualCalibration
import JGR26SubjectivityMonoculture.ResidualDiscrepancyBridge
import JGR26SubjectivityMonoculture.EmpiricalResiduals
import JGR26SubjectivityMonoculture.PopulationRelativity
import JGR26SubjectivityMonoculture.SourceModelDefinitions
import JGR26SubjectivityMonoculture.SourceNormalizationInterface
import JGR26SubjectivityMonoculture.SourceProbabilityBridge

import JGR26SubjectivityMonoculture.EmpiricalMomentTransfer
import JGR26SubjectivityMonoculture.SourceTheoryPrimitives
import JGR26SubjectivityMonoculture.GenericPopulationNull
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# The Subjectivity of Monoculture

Complete mathematical statements of the nine asserted source results.
The null definitions and parameter conventions are the concrete objects imported below.
Proofs are exported separately by `ProofInterface`.
-/

namespace JGR26SubjectivityMonoculture.PaperInterface

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators Topology RealInnerProductSpace ProbabilityTheory

noncomputable section



def theorem1Spec (m : ℕ) (P : PMF (Fin m → Bool)) : Prop :=
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


def proposition2Spec {Law : Type*} (D : Law → Law → ℝ)
    (P : Law) (N : ℕ → Set Law) : Prop :=
  draftNullLadder N → ∀ K excessK excessSucc,
    draftMinimalExcess D P (N K) excessK →
    draftMinimalExcess D P (N (K + 1)) excessSucc → excessSucc ≤ excessK


section ResidualDiscrepancy

local instance finiteResponseArrayFintype {Item Model : Type*}
    [Fintype Item] [Fintype Model] : Fintype (Item → Model → Bool) := by
  classical
  infer_instance

def theorem3Spec {Item Model : Type*}
    [Fintype Item] [Nonempty Item] [Fintype Model]
    (D : FiniteLaw (Item → Model → Bool) → FiniteLaw (Item → Model → Bool) → ℝ)
    (observed : FiniteLaw (Item → Model → Bool))
    (fitted : ℕ → FiniteLaw (Item → Model → Bool)) (p : ℕ → Item → Model → ℝ) : Prop :=
  ControlsBoundedExpectationsAtZero D → (∀ K i m, 0 ≤ p K i m ∧ p K i m ≤ 1) →
    (∀ K, HasProductBernoulliItemRowMarginals (fitted K) (p K)) →
    Tendsto (fun K => D observed (fitted K)) atTop (𝓝 0) → ∀ j ℓ, j ≠ ℓ →
      Tendsto (fun K => finiteLawExpectation observed (averagePairResidualFunctional (p K) j ℓ))
        atTop (𝓝 0)


end ResidualDiscrepancy

def lemma6Spec {Item Model : Type*} [Fintype Model] (K : ℕ) : Prop :=
  ∀ Q : Item → PMF (Model → Bool),
    sourceProbitMIRTNull K Q → sourceProbitMIRTNull (K + 1) Q


section SourceArrays

variable {K : ℕ} {Item Model : Type*} [Fintype Item] [Fintype Model]


def theorem5Spec (hK : 0 < K)
    (link : EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin K) → ℝ)
    (admissible : Set (SourceFactorParameter Item Model K))
    (probabilities : SourcePredictionArray Item Model)
    (fit : SourceFactorParameter Item Model K) : Prop :=
  sourceSpecifiedAdmissibleFit link admissible probabilities fit →
    sourceMaximumHeterogeneityFit hK link admissible probabilities fit →
    (∀ uv, 0 < link uv ∧ link uv < 1) →
    0 < sourceHeterogeneity hK fit → ContDiff ℝ 2 link → ∀ c > 0,
    HasLocalIdentificationAt (sourcePrediction link) fit c (sourceHeterogeneity hK fit) →
    ∃ radius > 0, ∃ C > 0, ∀ epsilon > 0,
      sSup ((fun z => Metric.infDist z (sourceExactPredictionFiber link probabilities)) ''
        sourceLocalEpsilonSet link probabilities fit radius epsilon) ≤
        (C / Real.sqrt (sourceHeterogeneity hK fit)) * epsilon


def lemma8Spec [Nonempty Item] [Nonempty Model] (hK : 0 < K)
    (g : ℝ → ℝ) (fit : SourceFactorParameter Item Model K) : Prop :=
  (∀ t, 0 < g t ∧ g t < 1) →
    ContDiff ℝ 2 g → (∀ t, 0 < deriv g t) → 0 < sourceHeterogeneity hK fit →
    ∃ m > 0,
      sourceDerivativeMinimum g fit m ∧
      HasLocalIdentificationAt (sourcePrediction (sourceBilinearLink g)) fit
        (m ^ 2) (sourceHeterogeneity hK fit) ∧
      ∀ fixed : Finset (Fin K),
        HasLocalIdentificationAt (sourceMIRTPredictionWithin fixed g fit) 0
          (m ^ 2) (sourceHeterogeneity hK fit)


end SourceArrays


section LogisticWitness

open scoped ContDiff

def proposition4Spec : Prop :=
  ContDiff ℝ ω logisticFiniteOneLink ∧
    (∀ z : (Fin 1 → ℝ) × (Fin 1 → ℝ),
      0 < logisticFiniteOneLink z ∧ logisticFiniteOneLink z < 1) ∧
    (∀ i j : Fin 2, 0 < responseSuccessMarginal logisticTwoItemTruthLaw i j ∧
      responseSuccessMarginal logisticTwoItemTruthLaw i j < 1) ∧
    ∃ U V : Fin 2 → ℝ, ∃ u : ℝ, ∃ W : Fin 2 → ℝ,
      inverseLinkMarginalSquaredDiscrepancy logisticTwoItemTruthLaw
        (logisticRankOneNullLaw U V) = 1 ∧
      draftPopulationSpecificTarget inverseLinkMarginalSquaredDiscrepancy
        logisticTwoItemTruthLaw
        (sourcePopulationNull (Item := Fin 2) (Model := Fin 2) 1 logisticFiniteOneLink)
        (logisticRankOneNullLaw U V) ∧
      inverseLinkMarginalSquaredDiscrepancy
        (logisticTwoItemTruthLaw.map (fun response (_ : Unit) j => response 1 j))
        (restrictedLogisticNullLaw u W) = 0 ∧
      draftPopulationSpecificTarget inverseLinkMarginalSquaredDiscrepancy
        (logisticTwoItemTruthLaw.map (fun response (_ : Unit) j => response 1 j))
        (sourcePopulationNull (Item := Unit) (Model := Fin 2) 1 logisticFiniteOneLink)
        (restrictedLogisticNullLaw u W) ∧
      responseSuccessMarginal (logisticRankOneNullLaw U V) 1 1 ≠
        responseSuccessMarginal (restrictedLogisticNullLaw u W) () 1 ∧
      (logisticRankOneNullLaw U V).map (fun response (_ : Unit) j => response 1 j) ≠
        restrictedLogisticNullLaw u W

end LogisticWitness


def proposition7Spec
    {Ω Row Model : Type*} [MeasurableSpace Ω] [MeasurableSpace Row]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (row : ℕ → Ω → Row) (response : Row → Model → Bool)
    (fitted : ℕ → ℕ → Ω → Model → ℝ) : Prop :=
  Measurable (row 0) → (∀ j, Measurable (fun z => response z j)) →
    Pairwise (fun i k => row i ⟂ᵢ[P] row k) →
    (∀ i, IdentDistrib (row i) (row 0) P P) →
    (∀ n i ω j, i < n → 0 < fitted n i ω j ∧ fitted n i ω j < 1) →
    let truth : Model → ℝ := fun j => sourceSuccessProbability P (fun ω => response (row 0 ω) j)
    (∀ n i j, i < n → AEStronglyMeasurable (fun ω => fitted n i ω j) P →
      (∫ ω, boolAsReal (response (row i ω) j) - fitted n i ω j ∂P) =
      (∫ ω, truth j - fitted n i ω j ∂P)) ∧
    (∀ n, 0 < n → ∀ ω j,
      (∑ i : Fin n, debiasedResidual
        (fun (i : Fin n) m => boolAsReal (response (row i ω) m) - fitted n i ω m) i j) /
        (n : ℝ) = 0) ∧
    (∀ n ω (i : Fin n) j,
      debiasedResidual
        (fun (i : Fin n) m => boolAsReal (response (row i ω) m) - fitted n i ω m) i j =
      debiasedResidual
        (fun (i : Fin n) m => boolAsReal (response (row i ω) m) - truth m) i j +
      debiasedResidual (fun (i : Fin n) m => truth m - fitted n i ω m) i j) ∧
    (∀ j, TendstoInMeasure P
      (fun n : ℕ => fun ω =>
        ((∑ i ∈ Finset.range n,
          (boolAsReal (response (row i ω) j) - fitted n i ω j)) / (n : ℝ)) -
        ((∑ i ∈ Finset.range n, (truth j - fitted n i ω j)) / (n : ℝ)))
      atTop (fun _ => 0))


def remark1Spec
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


end

end JGR26SubjectivityMonoculture.PaperInterface
