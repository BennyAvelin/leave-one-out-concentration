import LOOConcentrationManuscript.Internal.MeanQuadraticStandingIntegrability
import LOOConcentration.Frozen.Foundations.FittedLoss

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open MeasureTheory

/-- The six actual delta and zero-fit integrability fields, with the same
literal learner and loss as the quadratic-mean application. -/
theorem scalarResponse_quadraticStanding_integrability_fields
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hSecond : Integrable (fun x : ℝ => x ^ 2) μ) (n : ℕ) :
    let φ := fun x : ℝ =>
      (((fun _ : Fin 1 => (0 : ℝ)), (fun _ : Fin 1 => x)) : LOOConcentration.Observation 1 1)
    let ν := μ.map φ
    let T : ∀ r : ℕ, LOOConcentration.Estimator 1 1 (r + 1) := fun r D =>
      ContinuousMap.const (LOOConcentration.Features 1)
        (fun _ : Fin 1 => empiricalMean r (WithLp.toLp 2 (fun i => (D i).2 0)))
    let L := fun y y' : LOOConcentration.Responses 1 => (y 0 - y' 0) ^ 2
    let δ₁ := fun N : ℕ => fun z : LOOConcentration.Observation 1 1 =>
      2 * |z.2 0| / Real.sqrt (N : ℝ)
    let δ₂ := fun N : ℕ => fun _z : LOOConcentration.Observation 1 1 => (2 : ℝ) / (N : ℝ)
    Integrable (δ₁ (n + 1)) ν ∧ Integrable (δ₂ (n + 1)) ν ∧
    Integrable (δ₁ (n + 2)) ν ∧ Integrable (δ₂ (n + 2)) ν ∧
    Integrable (fun z => LOOConcentration.fittedLoss (T n) L 0 z) ν ∧
    Integrable (fun z => LOOConcentration.fittedLoss (T (n + 1)) L 0 z) ν := by
  intro φ ν T L δ₁ δ₂
  obtain ⟨_, hδ₁, hδ₂, hZero⟩ := scalarResponse_quadraticStanding_integrability μ hSecond
  refine ⟨hδ₁ n, hδ₂ n, ?_, ?_, ?_, ?_⟩
  · convert hδ₁ (n + 1) using 1
  · convert hδ₂ (n + 1) using 1
  · simpa [LOOConcentration.fittedLoss, T, L, empiricalMean] using hZero n
  · simpa [LOOConcentration.fittedLoss, T, L, empiricalMean] using hZero (n + 1)

end LOOConcentration.Manuscript.Internal
