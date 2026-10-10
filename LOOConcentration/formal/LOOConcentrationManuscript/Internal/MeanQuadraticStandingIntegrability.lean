import LOOConcentrationManuscript.Frozen.Definitions.EmpiricalMean
import Mathlib.Probability.Moments.Variance

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open MeasureTheory
open scoped ENNReal

/-- Finite scalar second moment supplies the actual response-law integrability
needed for the quadratic-mean standing assumption. -/
theorem scalarResponse_quadraticStanding_integrability
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hSecond : Integrable (fun x : ℝ => x ^ 2) μ) :
    let φ := fun x : ℝ =>
      (((fun _ : Fin 1 => (0 : ℝ)), (fun _ : Fin 1 => x)) : LOOConcentration.Observation 1 1)
    let ν := μ.map φ
    Integrable (fun z : LOOConcentration.Observation 1 1 => |z.2 0|) ν ∧
    (∀ r : ℕ, Integrable (fun z : LOOConcentration.Observation 1 1 =>
      2 * |z.2 0| / Real.sqrt ((r + 1 : ℕ) : ℝ)) ν) ∧
    (∀ r : ℕ, Integrable (fun _z : LOOConcentration.Observation 1 1 =>
      (2 : ℝ) / ((r + 1 : ℕ) : ℝ)) ν) ∧
    (∀ r : ℕ, Integrable (fun z : LOOConcentration.Observation 1 1 =>
      (empiricalMean r (0 : EuclideanSpace ℝ (Fin (r + 1))) - z.2 0) ^ 2) ν) := by
  intro φ ν
  have hφ : Measurable φ := by fun_prop
  let : IsProbabilityMeasure ν := μ.isProbabilityMeasure_map hφ.aemeasurable
  have hIdLp : MemLp (id : ℝ → ℝ) 2 μ :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2 hSecond
  have hAbs : Integrable (fun x : ℝ => |x|) μ := by
    simpa only [Real.norm_eq_abs, id_eq] using (hIdLp.integrable one_le_two).norm
  have hResponseAbs : Integrable (fun z : LOOConcentration.Observation 1 1 => |z.2 0|) ν := by
    exact (integrable_map_measure (by fun_prop) hφ.aemeasurable).2 hAbs
  refine ⟨hResponseAbs, ?_, ?_, ?_⟩
  · intro r
    exact (hResponseAbs.const_mul 2).div_const _
  · intro r
    exact integrable_const _
  · intro r
    apply (integrable_map_measure (by fun_prop) hφ.aemeasurable).2
    simpa [Function.comp_def, φ, empiricalMean] using hSecond

end LOOConcentration.Manuscript.Internal
