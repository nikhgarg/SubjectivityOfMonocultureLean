import JGR26SubjectivityMonoculture.SourceNormalizationInterface
import JGR26SubjectivityMonoculture.SourceProbabilityBridge

/-! # Prediction neighborhoods and residual primitives -/

namespace JGR26SubjectivityMonoculture

open MeasureTheory Set
open scoped BigOperators RealInnerProductSpace

noncomputable section

/-- Representations that reproduce the fitted prediction array exactly. -/
def sourceExactPredictionFiber {K : ℕ} {Item Model : Type*}
    [Fintype Item] [Fintype Model]
    (link : EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin K) → ℝ)
    (probabilities : SourcePredictionArray Item Model) : Set (SourceFactorParameter Item Model K) :=
  {w | sourcePrediction link w = probabilities}

/-- The local Euclidean prediction-error sublevel set around the fitted representation. -/
def sourceLocalEpsilonSet {K : ℕ} {Item Model : Type*}
    [Fintype Item] [Fintype Model]
    (link : EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin K) → ℝ)
    (probabilities : SourcePredictionArray Item Model)
    (fit : SourceFactorParameter Item Model K) (radius epsilon : ℝ) :
    Set (SourceFactorParameter Item Model K) :=
  {z | dist z fit < radius ∧
    (∑ i, ∑ j, (link (sourceItemFactor i z, sourceModelFactor j z) -
      probabilities (i, j)) ^ 2) ≤ epsilon ^ 2}

/-- An increasing scalar link applied to the item/model bilinear score. -/
def sourceBilinearLink {K : ℕ} (g : ℝ → ℝ)
    (uv : EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin K)) : ℝ :=
  g ⟪uv.1, uv.2⟫

/-- The minimum derivative on the finite fitted item/model score table. -/
def sourceDerivativeMinimum {K : ℕ} {Item Model : Type*}
    [Fintype Item] [Fintype Model] (g : ℝ → ℝ)
    (fit : SourceFactorParameter Item Model K) (m : ℝ) : Prop :=
  (∃ i j, m = deriv g ⟪sourceItemFactor i fit, sourceModelFactor j fit⟫) ∧
    ∀ i j, m ≤ deriv g ⟪sourceItemFactor i fit, sourceModelFactor j fit⟫

/-- The true marginal success probability under the observation law. -/
def sourceSuccessProbability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → Bool) : ℝ :=
  (P {ω | Y ω = true}).toReal

end

end JGR26SubjectivityMonoculture
