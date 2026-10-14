import JGR26SubjectivityMonoculture.MainTheorems
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Topology.UnitInterval

/-!
# The finite vertex mixture as a probability measure on the unit cube

The mixing measure is the pushforward of the response law along its binary
vertices. At each vertex the product Bernoulli law is deterministic, so its
mixture integral recovers the original law. The finite vertex set has `2^m`
points, including vertices with zero mixing weight.
-/

namespace JGR26SubjectivityMonoculture

open MeasureTheory
open scoped BigOperators unitInterval

noncomputable section

/-- A binary response vector is a vertex of the probability cube. -/
def responseProbabilityVertex {m : ℕ} (y : Fin m → Bool) : Fin m → unitInterval :=
  fun j => if y j then 1 else 0

/-- The conditional independent Bernoulli mass at a latent cube point. -/
def cubeBernoulliMass {m : ℕ} (p : Fin m → unitInterval) (y : Fin m → Bool) : ℝ :=
  ∏ j, if y j then (p j : ℝ) else 1 - (p j : ℝ)

/-- A product Bernoulli law at a binary vertex is the point mass at that vertex. -/
theorem productBernoulliMass_at_vertex {m : ℕ} (v y : Fin m → Bool) :
    productBernoulliMass (fun j => boolAsReal (v j)) y = vertexLaw v y := by
  classical
  by_cases hy : y = v
  · subst y
    simp only [vertexLaw, if_pos rfl]
    apply Finset.prod_eq_one
    intro j _
    cases hv : v j <;> simp [boolAsReal, hv]
  · rw [vertexLaw, if_neg hy]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hy
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    cases hv : v j <;> cases hyj : y j <;> simp_all [boolAsReal]

theorem cubeBernoulliMass_vertex {m : ℕ} (v y : Fin m → Bool) :
    cubeBernoulliMass (responseProbabilityVertex v) y = vertexLaw v y := by
  have h : cubeBernoulliMass (responseProbabilityVertex v) y =
      productBernoulliMass (fun j => boolAsReal (v j)) y := by
    apply Finset.prod_congr rfl
    intro j _
    cases hv : v j <;> cases hy : y j <;>
      simp [responseProbabilityVertex, boolAsReal, hv, hy]
  rw [h, productBernoulliMass_at_vertex]

/-- The mixing measure is a probability measure on `[0,1]^m`. -/
def vertexMixingMeasure {m : ℕ} (P : PMF (Fin m → Bool)) : Measure (Fin m → unitInterval) :=
  P.toMeasure.map responseProbabilityVertex

instance vertexMixingMeasure_isProbabilityMeasure {m : ℕ} (P : PMF (Fin m → Bool)) :
    IsProbabilityMeasure (vertexMixingMeasure P) := by
  exact MeasureTheory.Measure.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable

theorem continuous_cubeBernoulliMass {m : ℕ} (y : Fin m → Bool) :
    Continuous (fun p : Fin m → unitInterval => cubeBernoulliMass p y) := by
  unfold cubeBernoulliMass
  apply continuous_finset_prod
  intro j _
  cases y j <;> simp <;> fun_prop

/-- Theorem 1's integral is exactly the given response-law mass. -/
theorem vertexMixingMeasure_integral {m : ℕ} (P : PMF (Fin m → Bool)) (y : Fin m → Bool) :
    (∫ p, cubeBernoulliMass p y ∂vertexMixingMeasure P) = (P y).toReal := by
  rw [vertexMixingMeasure, integral_map (measurable_of_finite _).aemeasurable
    (continuous_cubeBernoulliMass y).aestronglyMeasurable]
  rw [PMF.integral_eq_sum]
  simp only [cubeBernoulliMass_vertex, smul_eq_mul]
  exact vertexMixtureLaw_eq (fun v => (P v).toReal) y

/-- The mixing probability measure is concentrated on at most `2^m` cube points. -/
theorem vertexMixingMeasure_finite_support {m : ℕ} (P : PMF (Fin m → Bool)) :
    ∃ S : Finset (Fin m → unitInterval), S.card ≤ 2 ^ m ∧
      vertexMixingMeasure P (S : Set (Fin m → unitInterval)) = 1 := by
  classical
  let S := Finset.univ.image (responseProbabilityVertex (m := m))
  refine ⟨S, ?_, ?_⟩
  · exact (Finset.card_image_le).trans (by simp [boolVector_card])
  · rw [vertexMixingMeasure, Measure.map_apply (measurable_of_finite _)
      (Finset.measurableSet S)]
    have hpre : responseProbabilityVertex ⁻¹' (S : Set (Fin m → unitInterval)) = Set.univ := by
      ext y
      simp [S]
    rw [hpre, measure_univ]

/-- Theorem 1, including a genuine cube mixing measure and the finite support bound. -/
theorem source_theorem1_vertex_mixture {m : ℕ} (P : PMF (Fin m → Bool)) :
    ∃ H : Measure (Fin m → unitInterval), IsProbabilityMeasure H ∧
      (∀ y, (∫ p, cubeBernoulliMass p y ∂H) = (P y).toReal) ∧
      ∃ S : Finset (Fin m → unitInterval), S.card ≤ 2 ^ m ∧ H (S : Set _) = 1 := by
  exact ⟨vertexMixingMeasure P, inferInstance,
    vertexMixingMeasure_integral P, vertexMixingMeasure_finite_support P⟩

end

end JGR26SubjectivityMonoculture
