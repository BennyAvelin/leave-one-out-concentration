import LOOConcentrationManuscript.Internal.RidgeConditionalMainApplication
import LOOConcentrationManuscript.Internal.RidgeExpectedFullSnocBiasConsumer
import LOOConcentrationRevision.Frozen.Results.MainConcentration

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal
open MeasureTheory Filter
open scoped Topology ENNReal

/-- Both main-theorem tails for the actual stabilized Ridge risk minus its
delete-one loss average. The expected bias is derived internally from the
source law and moments; its constant and the shared regularity constants are
fixed before every sample size. -/
theorem ridge_actual_source_main_tails
    (μ : Measure (LOOConcentration.Observation 1 1)) [IsProbabilityMeasure μ]
    (hSecond : Integrable LOOConcentration.observationNormSq μ)
    (hLSI : LOOConcentration.Revision.observationLogSobolevConstant μ < ⊤)
    (b δ : {t : ℝ // 0 < t}) :
    ∃ B : ℝ, 0 < B ∧
    let T := fun r => LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r
    let L := fun u v : Fin 1 → ℝ => |u 0 - v 0|
    let σ := (LOOConcentration.Revision.observationLogSobolevConstant μ).toReal
    let M₂ := ∫ z, LOOConcentration.observationNormSq z ∂μ
    let Θ := fun (r : ℕ) (t a b : ℝ) =>
      if σ = 0 then 0 else
      if a ^ 2 + 2 * b ^ 2 * (r : ℝ) * M₂ = 0 then
        if b = 0 then 0 else Real.exp (-(t / (8 * σ * b)))
      else if b = 0 then
        Real.exp (-(t ^ 2 / (8 * σ * (a ^ 2 + 2 * b ^ 2 * (r : ℝ) * M₂))))
      else Real.exp (-(min
        (t ^ 2 / (8 * σ * (a ^ 2 + 2 * b ^ 2 * (r : ℝ) * M₂)))
        (t / (8 * σ * b))))
    ∃ C : ℝ, 0 < C ∧ ∃ M : ℝ, 0 < M ∧ ∀ n : ℕ,
      ∃ hStanding : LOOConcentration.Revision.StandingAssumption (n := n) μ T L
        (fun N z => C * (1 + |z.1 0|) / Real.sqrt (N : ℝ))
        (fun N _ => C / (N : ℝ)) (fun N => B / (N : ℝ)) M 0,
      ∀ ε : ℝ, 3 * (B / (n + 2 : ℝ)) < ε →
        let H := fun D =>
          (LOOConcentration.Revision.looRiskL1 μ (T (n + 1)) L
            (hStanding.stable.integrable_full n)) D -
          LOOConcentration.looEstimate (T n) L D
        let rhs := (n + 2 : ℝ) * (∫ z, Θ (n + 1) (ε / 3)
            (C * (1 + |z.1 0|) / Real.sqrt (n + 1 : ℝ)) (C / (n + 1 : ℝ)) ∂μ) +
          Θ (n + 2) (ε / 3) (M / Real.sqrt (n + 2 : ℝ)) 0 +
          Θ (n + 2) (ε / 3 - B / (n + 2 : ℝ))
            (C * (1 + ∫ z, |z.1 0| ∂μ) / Real.sqrt (n + 2 : ℝ)) (C / (n + 2 : ℝ))
        (Measure.pi fun _ : Fin (n + 2) => μ).real {D | H D > ε} ≤ rhs ∧
        (Measure.pi fun _ : Fin (n + 2) => μ).real {D | -H D > ε} ≤ rhs := by
  have hY1 := (iidResponse_full_and_deleted_absolute_mean μ hSecond).1
  have hX4 := (observation_nativeLSI_feature_fourth_moment μ hLSI hSecond).2
  obtain ⟨B, hB, hBias⟩ := ridge_actual_ordered_expected_delete_bias μ hY1 hX4 b δ
  exact ⟨B, hB, ridge_actual_main_tails_of_ordered_bias μ hSecond hLSI b δ B hB.le hBias⟩

end LOOConcentration.Manuscript.Internal
