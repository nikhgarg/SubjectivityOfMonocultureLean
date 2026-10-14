import JGR26SubjectivityMonoculture.LogisticPopulationRelativity
import JGR26SubjectivityMonoculture.ResidualCalibration
import JGR26SubjectivityMonoculture.EmpiricalResiduals
import JGR26SubjectivityMonoculture.SourceModelDefinitions
import JGR26SubjectivityMonoculture.Draft20261013Interface

/-!
# Population relativity and empirical residuals

Proposition 4 states the possibility of different population-specific optima.
Its concrete witness uses the same smooth rank-one logistic link and the same
inverse-link squared marginal discrepancy on both populations. Proposition 7
states the expectation identity, exact finite-sample demeaning identities, and
the response-averaging limit for arbitrary sample-dependent fits. Remark 1
takes the sample-size limit at each fixed dimension before the dimension limit.
Pearson normalization is conditional on an eventual positive variance floor.
-/

namespace JGR26SubjectivityMonoculture

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators Topology ProbabilityTheory

noncomputable section

section LogisticWitness

open scoped ContDiff

/--
Proposition 4: a smooth, strictly interior rank-one logistic null can have
incompatible full-population and restricted-population global minimizers.
The truth law has independent Bernoulli responses with identity logits.
The restriction retains the second of the two items and both models.

The existential quantifiers choose actual real factors. Full-population
optimality is over all laws with rank-one logistic success marginals, including
every conditionally independent null law. The exact restricted fit is optimal
even among all laws. The last clause compares actual response laws after
marginalization, rather than only a parameter representation.
-/
def adoptedProposition4Spec : Prop :=
  ContDiff ℝ ω (fun z : ℝ × ℝ => Real.sigmoid (z.1 * z.2)) ∧
    (∀ z : ℝ × ℝ, 0 < Real.sigmoid (z.1 * z.2) ∧
      Real.sigmoid (z.1 * z.2) < 1) ∧
    (∀ i j : Fin 2, 0 < responseSuccessMarginal logisticTwoItemTruthLaw i j ∧
      responseSuccessMarginal logisticTwoItemTruthLaw i j < 1) ∧
    ∃ U V : Fin 2 → ℝ, ∃ u : ℝ, ∃ W : Fin 2 → ℝ,
      inverseLinkMarginalSquaredDiscrepancy logisticTwoItemTruthLaw
        (logisticRankOneNullLaw U V) = 1 ∧
      draftPopulationSpecificTarget inverseLinkMarginalSquaredDiscrepancy
        logisticTwoItemTruthLaw
        {Q | ∃ A B : Fin 2 → ℝ, Q = logisticRankOneNullLaw A B}
        (logisticRankOneNullLaw U V) ∧
      inverseLinkMarginalSquaredDiscrepancy
        (logisticTwoItemTruthLaw.map (fun response (_ : Unit) j => response 1 j))
        (restrictedLogisticNullLaw u W) = 0 ∧
      draftPopulationSpecificTarget inverseLinkMarginalSquaredDiscrepancy
        (logisticTwoItemTruthLaw.map (fun response (_ : Unit) j => response 1 j))
        {Q | ∃ a : ℝ, ∃ B : Fin 2 → ℝ, Q = restrictedLogisticNullLaw a B}
        (restrictedLogisticNullLaw u W) ∧
      (logisticRankOneNullLaw U V).map (fun response (_ : Unit) j => response 1 j) ≠
        restrictedLogisticNullLaw u W

theorem adoptedProposition4 : adoptedProposition4Spec := by
  refine ⟨logisticBilinearLink_smooth, logisticBilinearLink_strictlyInterior,
    logisticTwoItemTruthLaw_successMarginal_strictlyInterior,
    firstCoordinateFactor, firstCoordinateFactor, 1, secondCoordinateFactor, ?_⟩
  refine ⟨logisticLawDiscrepancy_firstCoordinate_eq_one, ?_,
    populationRelativity_logistic_responseLaw_witness.2.2.1,
    ?_, logisticPopulationRelativity_responseLaw_mismatch⟩
  · refine ⟨⟨_, _, rfl⟩, ?_⟩
    rintro Q ⟨A, B, rfl⟩
    apply logisticFirstCoordinate_is_global_responseLaw_minimizer
    exact ⟨A, B, fun i j => logisticRankOneNullLaw_successMarginal A B i j⟩
  · refine ⟨⟨_, _, rfl⟩, ?_⟩
    intro Q _
    exact logisticSecondCoordinate_is_global_restricted_responseLaw_minimizer Q

end LogisticWitness

/-- A binary response's expectation is its actual success-event probability. -/
theorem integral_boolAsReal_eq_successProbability
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y : Ω → Bool)
    (hY : Measurable Y) :
    (∫ ω, boolAsReal (Y ω) ∂P) = (P {ω | Y ω = true}).toReal := by
  have hset : MeasurableSet {ω | Y ω = true} := hY (measurableSet_singleton true)
  have hscore : (fun ω => boolAsReal (Y ω)) =
      ({ω | Y ω = true} : Set Ω).indicator (fun _ => (1 : ℝ)) := by
    funext ω
    cases h : Y ω <;> simp [h, boolAsReal]
  rw [hscore, integral_indicator_const 1 hset]
  simp only [smul_eq_mul, mul_one]
  rfl

/--
Proposition 7: residual expectations equal average calibration errors;
demeaning removes exactly their sample mean and retains the centered itemwise
error; the residual mean tracks empirical average calibration error.

`row` is the IID evaluation-row sequence under the probability law `P`.
`response` is a measurable binary coordinate of a row. Thus its unconditional
success probability is the same for every item. `fitted n i` may use the entire
sample of size `n`. Its measurability is required only in the expectation
clause, where strict probability bounds then supply integrability. No
measurability, independence or consistency of fitted values is needed for
the exact demeaning identities or for their cancelling mean difference.
The averaging conclusion holds almost surely, a stronger mode than the
stated convergence in probability of the residual-mean difference.
-/
def adoptedProposition7Spec
    {Ω Row Model : Type*} [MeasurableSpace Ω] [MeasurableSpace Row]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (row : ℕ → Ω → Row) (response : Row → Model → Bool)
    (fitted : ℕ → ℕ → Ω → Model → ℝ) : Prop :=
  Measurable (row 0) → (∀ j, Measurable (fun z => response z j)) →
    Pairwise (fun i k => row i ⟂ᵢ[P] row k) →
    (∀ i, IdentDistrib (row i) (row 0) P P) →
    (∀ n i ω j, i < n → 0 < fitted n i ω j ∧ fitted n i ω j < 1) →
    let truth : Model → ℝ := fun j => (P {ω | response (row 0 ω) j = true}).toReal
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
    (∀ j, ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ =>
        ((∑ i ∈ Finset.range n,
          (boolAsReal (response (row i ω) j) - fitted n i ω j)) / (n : ℝ)) -
        ((∑ i ∈ Finset.range n, (truth j - fitted n i ω j)) / (n : ℝ)))
      atTop (𝓝 0))

theorem adoptedProposition7
    {Ω Row Model : Type*} [MeasurableSpace Ω] [MeasurableSpace Row]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (row : ℕ → Ω → Row) (response : Row → Model → Bool)
    (fitted : ℕ → ℕ → Ω → Model → ℝ) :
    adoptedProposition7Spec P row response fitted := by
  unfold adoptedProposition7Spec
  intro hrow hresponse hindep hident hfitted
  dsimp only
  let truth : Model → ℝ := fun j => (P {ω | response (row 0 ω) j = true}).toReal
  have hscore (j : Model) : Measurable (fun z => boolAsReal (response z j)) :=
    (measurable_of_finite boolAsReal).comp (hresponse j)
  have hbound (z : Row) (j : Model) : |boolAsReal (response z j)| ≤ 1 := by
    cases response z j <;> norm_num [boolAsReal]
  have hint0 (j : Model) : Integrable (fun ω => boolAsReal (response (row 0 ω) j)) P :=
    integrable_rowScore_of_bounded (row 0) hrow _ (hscore j) 1 (fun z => hbound z j)
  have hscoreIdent (i : ℕ) (j : Model) :
      IdentDistrib (fun ω => boolAsReal (response (row i ω) j))
        (fun ω => boolAsReal (response (row 0 ω) j)) P P :=
    (hident i).comp (hscore j)
  have hmean0 (j : Model) :
      (∫ ω, boolAsReal (response (row 0 ω) j) ∂P) = truth j :=
    integral_boolAsReal_eq_successProbability P _ ((hresponse j).comp hrow)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n i j hi hmeas
    have hint := (hscoreIdent i j).integrable_iff.mpr (hint0 j)
    have hfitint : Integrable (fun ω => fitted n i ω j) P := by
      apply Integrable.of_bound hmeas 1
      exact Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (hfitted n i ω j hi).1]
        exact (hfitted n i ω j hi).2.le
    rw [integral_sub hint hfitint, integral_sub (integrable_const _) hfitint,
      (hscoreIdent i j).integral_eq, hmean0 j]
    simp [truth]
  · intro n hn ω j
    letI : NeZero n := ⟨ne_of_gt hn⟩
    rw [debiasedResidual_sum_eq_zero]
    exact zero_div _
  · intro n ω i j
    exact debiasedResidual_calibration_decomposition
      (fun (i : Fin n) m => boolAsReal (response (row i ω) m)) (fun _ m => truth m)
      (fun (i : Fin n) m => fitted n i ω m) i j
  · intro j
    exact ae_rawResidualMean_sub_averageCalibration_tendsto_zero
      (fun i ω => boolAsReal (response (row i ω) j))
      (fun n i ω => fitted n i ω j) (truth j) (hint0 j)
      (fun i k hik => (hindep hik).comp (hscore j) (hscore j))
      (fun i => hscoreIdent i j) (hmean0 j)

/--
Remark 1: uniformly consistent fitted probabilities inherit the population
residual-covariance limit under IID evaluation sampling, and inherit the
Pearson limit when both population residual variances have an eventual common
positive lower bound.

The error envelope is a uniform bound over all rows in each evaluation sample;
its almost-sure convergence is required separately at each fixed dimension.
It imposes no independence on fitted probabilities, which may depend on the
whole sample. Measurable bounded oracle scores supply their moment strong laws.
The displayed population moment subtracts the two residual means, so a raw
cross-moment is never silently identified with a centered covariance. Its
zero limit is the corresponding population residual-moment premise.

The order `eventually K, eventually n` means sample size tends to infinity at
fixed dimension before dimension tends to infinity. The sample threshold can
depend on the dimension and accuracy; no joint or diagonal rate is assumed.
Only the Pearson clause uses the variance floor, which also ensures eventually
nonzero empirical normalization after the fixed-dimension sampling limit.
-/
def adoptedRemark1Spec
    {Ω Row Model : Type*} [MeasurableSpace Ω] [MeasurableSpace Row]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (row : ℕ → Ω → Row) (response : Row → Model → Bool)
    (p : ℕ → Row → Model → ℝ) (j ℓ : Model)
    (fitted : ℕ → ℕ → ℕ → Ω → Model → ℝ)
    (error : ℕ → ℕ → Ω → ℝ) : Prop :=
  Measurable (row 0) → (∀ m, Measurable (fun z => response z m)) →
    (∀ K m, Measurable (fun z => p K z m)) →
    (∀ K z m, 0 ≤ p K z m ∧ p K z m ≤ 1) →
    Pairwise (fun i k => row i ⟂ᵢ[P] row k) →
    (∀ i, IdentDistrib (row i) (row 0) P P) →
    (∀ K n ω i, i < n → ∀ m,
      0 ≤ fitted K n i ω m ∧ fitted K n i ω m ≤ 1) →
    (∀ K n ω i, i < n → ∀ m,
      |fitted K n i ω m - p K (row i ω) m| ≤ error K n ω) →
    (∀ K, ∀ᵐ ω ∂P, Tendsto (fun n => error K n ω) atTop (𝓝 0)) →
    let population : ℕ → Model → Model → ℝ := fun K a b =>
      (∫ ω, (boolAsReal (response (row 0 ω) a) - p K (row 0 ω) a) *
        (boolAsReal (response (row 0 ω) b) - p K (row 0 ω) b) ∂P) -
      (∫ ω, boolAsReal (response (row 0 ω) a) - p K (row 0 ω) a ∂P) *
        (∫ ω, boolAsReal (response (row 0 ω) b) - p K (row 0 ω) b ∂P)
    let sampleCovariance : ℕ → ℕ → Ω → Model → Model → ℝ := fun K n ω a b =>
      ((∑ i ∈ Finset.range n,
        (boolAsReal (response (row i ω) a) - fitted K n i ω a) *
          (boolAsReal (response (row i ω) b) - fitted K n i ω b)) / (n : ℝ)) -
      ((∑ i ∈ Finset.range n,
        (boolAsReal (response (row i ω) a) - fitted K n i ω a)) / (n : ℝ)) *
      ((∑ i ∈ Finset.range n,
        (boolAsReal (response (row i ω) b) - fitted K n i ω b)) / (n : ℝ))
    Tendsto (fun K => population K j ℓ) atTop (𝓝 0) →
      (∀ᵐ ω ∂P, ∀ K, Tendsto (fun n => sampleCovariance K n ω j ℓ)
        atTop (𝓝 (population K j ℓ))) ∧
      (∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ᶠ K in atTop, ∀ᶠ n in atTop,
        |sampleCovariance K n ω j ℓ| < ε) ∧
      (∀ v : ℝ, 0 < v →
        (∀ᶠ K in atTop, v ≤ population K j j ∧ v ≤ population K ℓ ℓ) →
        ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ᶠ K in atTop, ∀ᶠ n in atTop,
          0 < sampleCovariance K n ω j j ∧ 0 < sampleCovariance K n ω ℓ ℓ ∧
          |sampleCovariance K n ω j ℓ /
            Real.sqrt (sampleCovariance K n ω j j * sampleCovariance K n ω ℓ ℓ)| < ε)

theorem adoptedRemark1
    {Ω Row Model : Type*} [MeasurableSpace Ω] [MeasurableSpace Row]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (row : ℕ → Ω → Row) (response : Row → Model → Bool)
    (p : ℕ → Row → Model → ℝ) (j ℓ : Model)
    (fitted : ℕ → ℕ → ℕ → Ω → Model → ℝ)
    (error : ℕ → ℕ → Ω → ℝ) :
    adoptedRemark1Spec P row response p j ℓ fitted error := by
  unfold adoptedRemark1Spec
  intro hrow hresponse hpmeas hp hindep hident hfitted herror hconsistent
  dsimp only
  intro hpopulation
  refine ⟨?_, ?_, ?_⟩
  · rw [ae_all_iff]
    intro K
    exact ae_fittedBinaryResidualCovariance_tendsto_of_uniform_consistency
      row hrow (p K) response j ℓ (hpmeas K) hresponse (hp K) hindep hident
      (fitted K) (error K) (hfitted K) (herror K) (hconsistent K)
  · exact ae_sequential_fittedResidualCovariance_vanishes_of_iid_and_consistency
      row hrow p response j ℓ hpmeas hresponse hp hindep hident
      fitted error hfitted herror hconsistent hpopulation
  · intro v hv hfloor
    have hpearson :=
      ae_sequential_fittedResidualPearson_vanishes_of_iid_consistency_and_variance_floor
      row hrow p response j ℓ hpmeas hresponse hp hindep hident
      fitted error hfitted herror hconsistent hpopulation v hv hfloor
    have hvariances : ∀ᵐ ω ∂P, ∀ K,
        Tendsto (fun n => empiricalBinaryResidualCovariance
          (fun i m => fitted K n i ω m) (fun i m => response (row i ω) m) j j n)
          atTop (𝓝 (populationRowCovariance P row
            (fun z => binaryResidual (p K z j) (response z j))
            (fun z => binaryResidual (p K z j) (response z j)))) ∧
        Tendsto (fun n => empiricalBinaryResidualCovariance
          (fun i m => fitted K n i ω m) (fun i m => response (row i ω) m) ℓ ℓ n)
          atTop (𝓝 (populationRowCovariance P row
            (fun z => binaryResidual (p K z ℓ) (response z ℓ))
            (fun z => binaryResidual (p K z ℓ) (response z ℓ)))) := by
      rw [ae_all_iff]
      intro K
      exact (ae_fittedBinaryResidualCovariance_tendsto_of_uniform_consistency
        row hrow (p K) response j j (hpmeas K) hresponse (hp K) hindep hident
        (fitted K) (error K) (hfitted K) (herror K) (hconsistent K)).and
        (ae_fittedBinaryResidualCovariance_tendsto_of_uniform_consistency
          row hrow (p K) response ℓ ℓ (hpmeas K) hresponse (hp K) hindep hident
          (fitted K) (error K) (hfitted K) (herror K) (hconsistent K))
    filter_upwards [hpearson, hvariances] with ω hpearson hvariances
    intro ε hε
    filter_upwards [hpearson ε hε, hfloor] with K hpearson hfloor
    have hj := (hvariances K).1.eventually
      (eventually_gt_nhds (lt_of_lt_of_le hv hfloor.1))
    have hℓ := (hvariances K).2.eventually
      (eventually_gt_nhds (lt_of_lt_of_le hv hfloor.2))
    filter_upwards [hj, hℓ, hpearson] with n hj hℓ hpearson
    exact ⟨hj, hℓ, hpearson⟩

end

end JGR26SubjectivityMonoculture
