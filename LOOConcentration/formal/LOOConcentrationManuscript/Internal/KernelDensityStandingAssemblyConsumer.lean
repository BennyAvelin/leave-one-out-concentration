import LOOConcentrationManuscript.Internal.KernelDensityStandingAssembly
import LOOConcentrationRevision.Frozen.Definitions.LooRiskL1_characterization

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LOOConcentration.Manuscript.Internal

open MeasureTheory
open scoped Topology ENNReal

/-- The actual zero-response KDE standing proof supplies the integrability
witness consumed by the frozen conditional L¹ risk characterization. -/
theorem kde_actual_standing_and_conditionalRisk
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hSecond : Integrable (fun x : ℝ => x ^ 2) μ)
    (hLSI : let scalar := fun x : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => x)
      letI : IsProbabilityMeasure (μ.map scalar) := μ.isProbabilityMeasure_map (by fun_prop)
      LOOConcentration.Revision.logSobolevConstant (μ.map scalar) < ⊤)
    (K : {K : ℝ → ℝ // ContDiff ℝ 1 K ∧ (∀ x, 0 ≤ K x) ∧
      (∃ B : ℝ, ∀ x, |K x| ≤ B) ∧ (∫ x : ℝ, K x) = 1 ∧
      (∃ B : ℝ, ∀ x, |deriv K x| ≤ B)})
    (h : {t : ℝ // 0 < t}) :
    let φ := fun x : ℝ => ((fun _ : Fin 1 => x), (fun _ : Fin 1 => (0 : ℝ)))
    let ν := μ.map φ
    letI : IsProbabilityMeasure ν := μ.isProbabilityMeasure_map (by fun_prop)
    let T := fun r : ℕ => LOOConcentration.Manuscript.kernelDensityEstimator K h r
    let L := fun a _ : LOOConcentration.Responses 1 => |a 0|
    ∃ M : ℝ, 0 < M ∧ ∀ n : ℕ,
      ∃ hStanding : LOOConcentration.Revision.StandingAssumption (n := n) ν T L
        (fun N _ => M / (h.val ^ 2 * Real.sqrt (N : ℝ)))
        (fun _ _ => 0) (fun _ => 0) (M / h.val ^ 2) 0,
        ((Measure.pi (fun _ : Fin (n + 2) => ν)).prod ν)[
          (fun p : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (n + 2) ×
            LOOConcentration.Observation 1 1 =>
            LOOConcentration.fittedLoss (T (n + 1)) L p.1 p.2) |
            MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[
              ((Measure.pi (fun _ : Fin (n + 2) => ν)).prod ν)]
          fun p => (LOOConcentration.Revision.looRiskL1 ν (T (n + 1)) L
            (hStanding.stable.integrable_full n)) p.1 := by
  intro φ ν T L
  have hνProb : IsProbabilityMeasure ν := μ.isProbabilityMeasure_map (by fun_prop)
  obtain ⟨M, hM, hAll⟩ := kde_actual_complete_standing μ hSecond hLSI K h
  refine ⟨M, hM, ?_⟩
  intro n
  refine ⟨hAll n, ?_⟩
  exact @LOOConcentration.Revision.looRiskL1_characterization 1 1 n
    ν hνProb (T (n + 1)) L ((hAll n).stable.integrable_full n)

end LOOConcentration.Manuscript.Internal
