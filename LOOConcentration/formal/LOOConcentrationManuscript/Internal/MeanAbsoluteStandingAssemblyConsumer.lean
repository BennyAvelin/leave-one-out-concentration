import LOOConcentrationManuscript.Internal.MeanAbsoluteStandingAssembly
import LOOConcentrationRevision.Frozen.Definitions.LooRiskL1_characterization

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal

open MeasureTheory
open scoped Topology ENNReal

/-- The actual response-only empirical mean standing proof supplies the
integrability witness for the frozen sample-conditioned risk characterization. -/
theorem empiricalMean_absolute_actual_standing_and_conditionalRisk
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hSecond : Integrable (fun x : ℝ => x ^ 2) μ)
    (hFinite : let scalar := fun x : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => x)
      letI : IsProbabilityMeasure (μ.map scalar) := μ.isProbabilityMeasure_map (by fun_prop)
      LOOConcentration.Revision.logSobolevConstant (μ.map scalar) < ⊤) :
    let φ : ℝ → LOOConcentration.Observation 1 1 :=
      fun x => ((fun _ : Fin 1 => 0), (fun _ : Fin 1 => x))
    let ν := μ.map φ
    letI : IsProbabilityMeasure ν := μ.isProbabilityMeasure_map (by fun_prop)
    let T : ∀ r : ℕ, LOOConcentration.Estimator 1 1 (r + 1) := fun r D =>
      ContinuousMap.const (LOOConcentration.Features 1)
        (fun _ : Fin 1 => empiricalMean r
          (WithLp.toLp 2 (fun i : Fin (r + 1) => (D i).2 0)))
    let L : LOOConcentration.Responses 1 → LOOConcentration.Responses 1 → ℝ :=
      fun y y' => |y 0 - y' 0|
    let δ₁ := fun N : ℕ => fun _z : LOOConcentration.Observation 1 1 =>
      (Real.sqrt (N : ℝ))⁻¹
    let δ₂ := fun _N : ℕ => fun _z : LOOConcentration.Observation 1 1 => (0 : ℝ)
    let δ₃ := fun N : ℕ =>
      2 * (∫ x : ℝ, |x| ∂μ) / ((N : ℝ) - 1)
    ∀ n : ℕ,
      ∃ hStanding : LOOConcentration.Revision.StandingAssumption
          (n := n) ν T L δ₁ δ₂ δ₃ 1 0,
        ((Measure.pi (fun _ : Fin (n + 2) => ν)).prod ν)[
          (fun p : LOOConcentration.Dataset
              (LOOConcentration.Observation 1 1) (n + 2) ×
              LOOConcentration.Observation 1 1 =>
            LOOConcentration.fittedLoss (T (n + 1)) L p.1 p.2) |
          MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[
            ((Measure.pi (fun _ : Fin (n + 2) => ν)).prod ν)]
          fun p => (LOOConcentration.Revision.looRiskL1 ν (T (n + 1)) L
            (hStanding.stable.integrable_full n)) p.1 := by
  intro φ ν
  have hνProb : IsProbabilityMeasure ν := μ.isProbabilityMeasure_map (by fun_prop)
  intro T L δ₁ δ₂ δ₃ n
  refine ⟨empiricalMean_absoluteStanding_of_scalarLaw μ hSecond hFinite n, ?_⟩
  exact @LOOConcentration.Revision.looRiskL1_characterization 1 1 n
    ν hνProb (T (n + 1)) L
    ((empiricalMean_absoluteStanding_of_scalarLaw μ hSecond hFinite n).stable.integrable_full n)

end LOOConcentration.Manuscript.Internal
