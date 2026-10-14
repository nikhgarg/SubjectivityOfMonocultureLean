import JGR26SubjectivityMonoculture.LogisticPopulationRelativity
import JGR26SubjectivityMonoculture.ResidualDiscrepancyBridge
import JGR26SubjectivityMonoculture.SourceModelDefinitions

/-!
# Fixed-link population nulls and population relativity

The source population null uses fixed finite-dimensional item and model
factors and one fixed link. For each item its model responses have the product
Bernoulli law implied by those factors. The joint law between distinct items
is unrestricted.

The rank-one logistic witness minimizes the fixed inverse-link discrepancy
over this entire population-null family, and its restricted marginal differs
from a globally optimal fit on the restricted population.
-/

namespace JGR26SubjectivityMonoculture

open Set
open scoped BigOperators ContDiff

noncomputable section

/--
The population null at fixed factor dimension and fixed link. Item factors
and model factors are finite real vectors. The actual law of each item's
model-response row is product Bernoulli with the link's success probabilities.
This condition places no independence requirement on distinct item rows.
-/
def sourcePopulationNull
    {Item Model : Type*} [Fintype Item] [Fintype Model]
    [Fintype (Item → Model → Bool)]
    (r : ℕ) (link : (Fin r → ℝ) × (Fin r → ℝ) → ℝ) :
    Set (PMF (Item → Model → Bool)) := by
  classical
  exact {Q | ∃ U : Item → Fin r → ℝ, ∃ V : Model → Fin r → ℝ,
    (∀ i j, 0 < link (U i, V j) ∧ link (U i, V j) < 1) ∧
    HasProductBernoulliItemRowMarginals (finiteLawOfPMF Q)
      (fun i j => link (U i, V j))}

/-- Actual product row marginals determine each coordinate's success probability. -/
theorem responseSuccessMarginal_eq_of_productItemRowMarginals
    {Item Model : Type*} [Fintype Item] [Fintype Model]
    [DecidableEq Item] [DecidableEq Model]
    [fState : Fintype (Item → Model → Bool)]
    (Q : PMF (Item → Model → Bool)) (p : Item → Model → ℝ)
    (hp : ∀ i j, 0 ≤ p i j ∧ p i j ≤ 1)
    (hrows : HasProductBernoulliItemRowMarginals (finiteLawOfPMF Q) p)
    (i : Item) (j : Model) : responseSuccessMarginal Q i j = p i j := by
  have henum : fState = (Pi.instFintype : Fintype (Item → Model → Bool)) :=
    Subsingleton.elim _ _
  cases henum
  classical
  change finiteLawExpectation (finiteLawOfPMF Q)
    (fun response => boolAsReal (response i j)) = p i j
  rw [finiteLawExpectation_itemRow_eq_of_productBernoulliItemRowMarginals
    (finiteLawOfPMF Q) p hrows i (fun row => boolAsReal (row j))]
  let μ : Model → PMF Bool := fun m => realBernoulliPMF (p i m) (hp i m).1 (hp i m).2
  have hsum : (∑ row : Model → Bool, productBernoulliMass (p i) row * boolAsReal (row j)) =
      AppliedModelingLib.pmfExp (AppliedModelingLib.pmfPi μ) (fun row => boolAsReal (row j)) := by
    unfold AppliedModelingLib.pmfExp
    exact Finset.sum_congr rfl fun row _ => by
      rw [productBernoulliPMF_toReal_eq_mass (p i) (hp i) row]
  rw [hsum, AppliedModelingLib.pmfExp_pmfPi_eval_eq μ j boolAsReal]
  simp [AppliedModelingLib.pmfExp, μ, boolAsReal]

/-- Every member of the population null has its factor-implied success marginals. -/
theorem sourcePopulationNull_successMarginals
    {Item Model : Type*} [Fintype Item] [Fintype Model]
    [DecidableEq Item] [DecidableEq Model]
    [Fintype (Item → Model → Bool)]
    {r : ℕ} {link : (Fin r → ℝ) × (Fin r → ℝ) → ℝ}
    {Q : PMF (Item → Model → Bool)} (hQ : Q ∈ sourcePopulationNull r link) :
    ∃ U : Item → Fin r → ℝ, ∃ V : Model → Fin r → ℝ,
      ∀ i j, responseSuccessMarginal Q i j = link (U i, V j) := by
  classical
  obtain ⟨U, V, hp, hrows⟩ := hQ
  refine ⟨U, V, fun i j => ?_⟩
  exact responseSuccessMarginal_eq_of_productItemRowMarginals Q
    (fun i j => link (U i, V j)) (fun i j => ⟨(hp i j).1.le, (hp i j).2.le⟩) hrows i j

/-- A full product response law is one feasible joint law in the population null. -/
theorem fixedDesignResponsePMF_mem_sourcePopulationNull
    {Item Model : Type*} [Fintype Item] [Fintype Model]
    [DecidableEq Item] [DecidableEq Model]
    [Fintype (Item → Model → Bool)]
    (r : ℕ) (link : (Fin r → ℝ) × (Fin r → ℝ) → ℝ)
    (U : Item → Fin r → ℝ) (V : Model → Fin r → ℝ)
    (hp : ∀ i j, 0 < link (U i, V j) ∧ link (U i, V j) < 1) :
    fixedDesignResponsePMF (fun i j => link (U i, V j))
      (fun i j => ⟨(hp i j).1.le, (hp i j).2.le⟩) ∈ sourcePopulationNull r link := by
  classical
  refine ⟨U, V, hp, ?_⟩
  simpa only [fixedDesignResponseLaw] using
    fixedDesignResponseLaw_hasProductBernoulliItemRowMarginals
      (fun i j => link (U i, V j)) (fun i j => ⟨(hp i j).1.le, (hp i j).2.le⟩)

/-- The fixed rank-one logistic link on one-coordinate finite real vectors. -/
def logisticFiniteOneLink (z : (Fin 1 → ℝ) × (Fin 1 → ℝ)) : ℝ :=
  Real.sigmoid (z.1 0 * z.2 0)

theorem logisticFiniteOneLink_strictlyInterior (z : (Fin 1 → ℝ) × (Fin 1 → ℝ)) :
    0 < logisticFiniteOneLink z ∧ logisticFiniteOneLink z < 1 :=
  ⟨Real.sigmoid_pos _, Real.sigmoid_lt_one _⟩

theorem logisticFiniteOneLink_smooth : ContDiff ℝ ω logisticFiniteOneLink := by
  exact contDiff_sigmoid.comp
    (((contDiff_apply ℝ ℝ (0 : Fin 1)).comp contDiff_fst).mul
      ((contDiff_apply ℝ ℝ (0 : Fin 1)).comp contDiff_snd))

/-- Every chosen full-population logistic product law belongs to the full source null family. -/
theorem logisticRankOneNullLaw_mem_sourcePopulationNull (U V : Fin 2 → ℝ) :
    logisticRankOneNullLaw U V ∈
      sourcePopulationNull (Item := Fin 2) (Model := Fin 2) 1 logisticFiniteOneLink := by
  simpa only [logisticRankOneNullLaw, logisticRankOnePrediction, rankOnePrediction,
    logisticFiniteOneLink] using
    fixedDesignResponsePMF_mem_sourcePopulationNull 1 logisticFiniteOneLink
      (fun i _ => U i) (fun j _ => V j)
      (fun i j => logisticFiniteOneLink_strictlyInterior (fun _ => U i, fun _ => V j))

/-- Every chosen restricted-population logistic product law is source-null feasible. -/
theorem restrictedLogisticNullLaw_mem_sourcePopulationNull (u : ℝ) (V : Fin 2 → ℝ) :
    restrictedLogisticNullLaw u V ∈
      sourcePopulationNull (Item := Unit) (Model := Fin 2) 1 logisticFiniteOneLink := by
  simpa only [restrictedLogisticNullLaw, restrictedLogisticPrediction,
    logisticFiniteOneLink] using
    fixedDesignResponsePMF_mem_sourcePopulationNull 1 logisticFiniteOneLink
      (fun (_ : Unit) (_ : Fin 1) => u) (fun j _ => V j)
      (fun _ j => logisticFiniteOneLink_strictlyInterior (fun _ => u, fun _ => V j))

/-- The displayed full fit globally minimizes over all conditionally independent source nulls. -/
theorem logisticFirstCoordinate_is_sourcePopulationNull_minimizer :
    draftPopulationSpecificTarget inverseLinkMarginalSquaredDiscrepancy logisticTwoItemTruthLaw
      (sourcePopulationNull (Item := Fin 2) (Model := Fin 2) 1 logisticFiniteOneLink)
      (logisticRankOneNullLaw firstCoordinateFactor firstCoordinateFactor) := by
  refine ⟨logisticRankOneNullLaw_mem_sourcePopulationNull _ _, ?_⟩
  intro Q hQ
  apply logisticFirstCoordinate_is_global_responseLaw_minimizer Q
  obtain ⟨U, V, hprob⟩ := sourcePopulationNull_successMarginals hQ
  refine ⟨fun i => U i 0, fun j => V j 0, ?_⟩
  exact hprob

/-- The restricted exact fit globally minimizes over the restricted source null family. -/
theorem logisticSecondCoordinate_is_sourcePopulationNull_minimizer :
    draftPopulationSpecificTarget inverseLinkMarginalSquaredDiscrepancy
      (restrictSecondItemResponseLaw logisticTwoItemTruthLaw)
      (sourcePopulationNull (Item := Unit) (Model := Fin 2) 1 logisticFiniteOneLink)
      (restrictedLogisticNullLaw 1 secondCoordinateFactor) := by
  refine ⟨restrictedLogisticNullLaw_mem_sourcePopulationNull _ _, ?_⟩
  intro Q _
  exact logisticSecondCoordinate_is_global_restricted_responseLaw_minimizer Q

/--
Proposition 4: for the fixed smooth rank-one logistic link and one fixed
inverse-link discrepancy, a full-population global null optimizer and a
restricted-population global null optimizer can have different restricted
response laws. Both minimizations range over the actual source population
nulls, including arbitrary dependence between distinct item rows.
-/
def genericPopulationRelativitySpec : Prop :=
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
      (logisticRankOneNullLaw U V).map (fun response (_ : Unit) j => response 1 j) ≠
        restrictedLogisticNullLaw u W

/-- The full source-null-family population-relativity witness of Proposition 4. -/
theorem genericPopulationRelativity : genericPopulationRelativitySpec := by
  refine ⟨logisticFiniteOneLink_smooth, logisticFiniteOneLink_strictlyInterior,
    logisticTwoItemTruthLaw_successMarginal_strictlyInterior,
    firstCoordinateFactor, firstCoordinateFactor, 1, secondCoordinateFactor, ?_⟩
  exact ⟨logisticLawDiscrepancy_firstCoordinate_eq_one,
    logisticFirstCoordinate_is_sourcePopulationNull_minimizer,
    populationRelativity_logistic_responseLaw_witness.2.2.1,
    logisticSecondCoordinate_is_sourcePopulationNull_minimizer,
    logisticPopulationRelativity_responseLaw_mismatch⟩

end

end JGR26SubjectivityMonoculture
