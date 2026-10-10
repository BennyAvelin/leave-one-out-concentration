import LOOConcentrationManuscript.Internal.MeanQuadraticRateConvergence
import LOOConcentrationRevision.Frozen.Definitions.Stable

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open Filter MeasureTheory ProbabilityTheory
open scoped Topology

/-- The six numerical rate fields use the actual variance and the literal
response embedding. This does not assert the other stability fields. -/
theorem quadraticMean_actual_response_rate_fields
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    let φ := fun x : ℝ =>
      (((fun _ : Fin 1 => (0 : ℝ)), (fun _ : Fin 1 => x)) : LOOConcentration.Observation 1 1)
    let ν := μ.map φ
    let δ₁ := fun N : ℕ => fun z : LOOConcentration.Observation 1 1 =>
      2 * |z.2 0| / Real.sqrt (N : ℝ)
    let δ₂ := fun N : ℕ => fun _z : LOOConcentration.Observation 1 1 => (2 : ℝ) / (N : ℝ)
    let δ₃ := fun N : ℕ => variance (id : ℝ → ℝ) μ / ((N : ℝ) * ((N : ℝ) - 1))
    (∀ r z, 0 ≤ δ₁ (r + 1) z) ∧
    (∀ᵐ z ∂ν, Tendsto (fun r => δ₁ (r + 1) z) atTop (𝓝 0)) ∧
    (∀ r z, 0 ≤ δ₂ (r + 1) z) ∧
    (∀ᵐ z ∂ν, Tendsto (fun r => δ₂ (r + 1) z) atTop (𝓝 0)) ∧
    (∀ n, 0 ≤ δ₃ (n + 2)) ∧
    Tendsto (fun n => δ₃ (n + 2)) atTop (𝓝 0) := by
  classical
  intro φ ν δ₁ δ₂ δ₃
  have h (z : LOOConcentration.Observation 1 1) :=
    quadraticMean_rates_nonnegative_tendsto (variance (id : ℝ → ℝ) μ)
      (z.2 0) (variance_nonneg _ _)
  have hδ₃ (n : ℕ) : δ₃ (n + 2) =
      variance (id : ℝ → ℝ) μ / ((n + 2 : ℝ) * (n + 1 : ℝ)) := by
    dsimp [δ₃]
    congr 2 <;> push_cast <;> ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r z
    simpa only [δ₁, Nat.cast_add, Nat.cast_one] using (h z).1 r
  · exact Filter.Eventually.of_forall fun z => by
      simpa only [δ₁, Nat.cast_add, Nat.cast_one] using (h z).2.1
  · intro r z
    simpa only [δ₂, Nat.cast_add, Nat.cast_one] using (h z).2.2.1 r
  · exact Filter.Eventually.of_forall fun z => by
      simpa only [δ₂, Nat.cast_add, Nat.cast_one] using (h z).2.2.2.1
  · intro n
    rw [hδ₃ n]
    exact (h (0 : LOOConcentration.Observation 1 1)).2.2.2.2.1 n
  · simpa only [hδ₃] using (h (0 : LOOConcentration.Observation 1 1)).2.2.2.2.2

end LOOConcentration.Manuscript.Internal
