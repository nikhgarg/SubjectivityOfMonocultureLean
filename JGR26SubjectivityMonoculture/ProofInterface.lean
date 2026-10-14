import JGR26SubjectivityMonoculture.PaperInterface
import JGR26SubjectivityMonoculture.Draft20261013Interface
import JGR26SubjectivityMonoculture.AdoptedDraft20261013Interface

/-! # Proofs of the source-facing mathematical statements -/

namespace JGR26SubjectivityMonoculture.ProofInterface

open JGR26SubjectivityMonoculture.PaperInterface
open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators Topology RealInnerProductSpace ProbabilityTheory

noncomputable section

theorem theorem1 (m : ℕ) (P : PMF (Fin m → Bool)) : theorem1Spec m P :=
  source_theorem1_joint_vertex_mixture P


theorem proposition2 {Law : Type*} (D : Law → Law → ℝ)
    (P : Law) (N : ℕ → Set Law) : proposition2Spec D P N := by
  intro hNested K excessK excessSucc hK hSucc
  exact infimumMinimalExcess_nonincreasing D P N K hNested
    ((draftMinimalExcess_iff_infimum D P (N K) excessK).mp hK)
    ((draftMinimalExcess_iff_infimum D P (N (K + 1)) excessSucc).mp hSucc)

local instance finiteResponseArrayFintype {Item Model : Type*}
    [Fintype Item] [Fintype Model] : Fintype (Item → Model → Bool) := by
  classical
  infer_instance


theorem theorem3 {Item Model : Type*}
    [Fintype Item] [Nonempty Item] [Fintype Model]
    (D : FiniteLaw (Item → Model → Bool) → FiniteLaw (Item → Model → Bool) → ℝ)
    (observed : FiniteLaw (Item → Model → Bool))
    (fitted : ℕ → FiniteLaw (Item → Model → Bool)) (p : ℕ → Item → Model → ℝ) :
    theorem3Spec D observed fitted p := by
  intro hD hp hrows hlim j ℓ hjℓ
  exact averagePairResidual_tendsto_zero_of_productItemRowMarginals_and_qualitative_discrepancy
    hD observed fitted p j ℓ hjℓ hp hrows hlim


theorem lemma6 {Item Model : Type*} [Fintype Model] (K : ℕ) :
    lemma6Spec (Item := Item) (Model := Model) K := by
  intro Q hQ
  exact sourceProbabilityMIRTNull_nested K sourceProbitLink Q hQ


section SourceArrays

variable {K : ℕ} {Item Model : Type*} [Fintype Item] [Fintype Model]

theorem theorem5 (hK : 0 < K)
    (link : EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ (Fin K) → ℝ)
    (admissible : Set (SourceFactorParameter Item Model K))
    (probabilities : SourcePredictionArray Item Model)
    (fit : SourceFactorParameter Item Model K) :
    theorem5Spec hK link admissible probabilities fit := by
  intro hfit _hmax _hlink hh hsmooth c hc hid
  rw [← hfit.2]
  exact source_theorem5_local_heterogeneity link fit hc hh hsmooth hid


theorem lemma8 [Nonempty Item] [Nonempty Model] (hK : 0 < K)
    (g : ℝ → ℝ) (fit : SourceFactorParameter Item Model K) : lemma8Spec hK g fit := by
  intro _hg hsmooth hpositive hh
  obtain ⟨hU, hV⟩ := sourceHeterogeneity_lowerBounds hK fit
  obtain ⟨m, hm, hattain, hweight, hid⟩ :=
    source_lemma8_mirt_identification g hsmooth hpositive fit hh hU hV
  exact ⟨m, hm, ⟨hattain, hweight⟩, hid, fun fixed =>
    source_mirt_localIdentificationWithin_of_gramLowerBounds fixed g hsmooth hpositive
      fit hm hh hweight hU hV⟩


end SourceArrays

theorem proposition4 : proposition4Spec := by
  refine ⟨logisticFiniteOneLink_smooth, logisticFiniteOneLink_strictlyInterior,
    logisticTwoItemTruthLaw_successMarginal_strictlyInterior,
    firstCoordinateFactor, firstCoordinateFactor, 1, secondCoordinateFactor, ?_⟩
  exact ⟨logisticLawDiscrepancy_firstCoordinate_eq_one,
    logisticFirstCoordinate_is_sourcePopulationNull_minimizer,
    populationRelativity_logistic_responseLaw_witness.2.2.1,
    logisticSecondCoordinate_is_sourcePopulationNull_minimizer,
    by
      simp only [logisticRankOneNullLaw_successMarginal,
        restrictedLogisticNullLaw_successMarginal]
      exact logisticPopulationRelativity_prediction_mismatch,
    logisticPopulationRelativity_responseLaw_mismatch⟩


theorem proposition7
    {Ω Row Model : Type*} [MeasurableSpace Ω] [MeasurableSpace Row]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (row : ℕ → Ω → Row) (response : Row → Model → Bool)
    (fitted : ℕ → ℕ → Ω → Model → ℝ) :
    proposition7Spec P row response fitted := by
  intro hrow hresponse hindep hident hfitted
  have h := adoptedProposition7 P row response fitted hrow hresponse hindep hident hfitted
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  intro j
  apply tendstoInMeasure_of_tendsto_ae _ (h.2.2.2 j)
  intro n
  let truth : ℝ := (P {ω | response (row 0 ω) j = true}).toReal
  have hscore (i : ℕ) : AEStronglyMeasurable
      (fun ω => boolAsReal (response (row i ω) j)) P := by
    have hid := (hident i).comp ((measurable_of_finite boolAsReal).comp (hresponse j))
    exact hid.aestronglyMeasurable_iff.mpr
      (((measurable_of_finite boolAsReal).comp ((hresponse j).comp hrow)).aestronglyMeasurable)
  have heq : (fun ω =>
      ((∑ i ∈ Finset.range n, (boolAsReal (response (row i ω) j) - fitted n i ω j)) / (n : ℝ)) -
      ((∑ i ∈ Finset.range n, (truth - fitted n i ω j)) / (n : ℝ))) =
      (fun ω => ((∑ i ∈ Finset.range n, boolAsReal (response (row i ω) j)) / (n : ℝ)) -
        ((n : ℝ) * truth) / (n : ℝ)) := by
    funext ω
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  change AEStronglyMeasurable (fun ω =>
      ((∑ i ∈ Finset.range n, (boolAsReal (response (row i ω) j) - fitted n i ω j)) / (n : ℝ)) -
      ((∑ i ∈ Finset.range n, (truth - fitted n i ω j)) / (n : ℝ))) P
  rw [heq]
  have hs : AEStronglyMeasurable
      (fun ω => ∑ i ∈ Finset.range n, boolAsReal (response (row i ω) j)) P := by
    convert Finset.aestronglyMeasurable_sum (Finset.range n) (fun i _ => hscore i) using 1
    ext ω
    simp only [Finset.sum_apply]
  simpa only [div_eq_mul_inv, Pi.sub_apply] using
    (hs.mul_const (n : ℝ)⁻¹).sub
      (aestronglyMeasurable_const (b := ((n : ℝ) * truth) / (n : ℝ)))

theorem remark1
    {ι Item Model : Type*} [Fintype Item] [Nonempty Item] [Fintype Model]
    [Fintype (Item → Model → Bool)]
    (l : Filter ι) (dimension sampleSize : ι → ℕ)
    (sampleItem : ι → ℕ → Item) (response : ι → ℕ → Model → Bool)
    (observed : FiniteLaw (Item → Model → Bool))
    (null : ℕ → FiniteLaw (Item → Model → Bool))
    (D : FiniteLaw (Item → Model → Bool) → FiniteLaw (Item → Model → Bool) → ℝ)
    (p : ℕ → Item → Model → ℝ) (fitted : ι → ℕ → Model → ℝ)
    (error : ι → ℝ) (j ℓ : Model) :
    remark1Spec l dimension sampleSize sampleItem response observed null D p fitted error j ℓ := by
  unfold remark1Spec
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

end JGR26SubjectivityMonoculture.ProofInterface
