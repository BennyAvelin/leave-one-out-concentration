import LOOConcentrationRevision.Concentration.StandingUniformI1Source
import LOOConcentrationRevision.Results.StandingLossDecomposition
import LOOConcentration.Frozen.Foundations.LooEstimate
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Revision
open MeasureTheory

/-- Exact decomposition of the source `standingI1` on ordered samples into its
actual deleted fitted-loss sections. -/
theorem standing_I1_actual_deleted_section_average
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)
    (D : Dataset (Observation k m) (n + 2)) :
    standingI1 μ T L δ₁ δ₂ δ₃ c d hSt D =
      (∑ i : Fin (n + 2),
        (meanFittedLoss μ (T n) L (D i) (hSt.mean_integrable (D i)) -
          fittedLoss (T n) L (deleteAt D i) (D i))) / (n + 2 : ℝ) := by
  simp only [standingI1, standingV, LOOConcentration.looEstimate,
    LOOConcentration.fittedLoss]
  rw [← sub_div]
  congr 1
  rw [Finset.sum_sub_distrib]

/-- Named consumer of the actual positive-growth deleted-fit MGF on the source
training carrier. -/
theorem standing_deleted_fit_positive_source_mgf_consumer
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d) :
    ∀ᵐ z ∂μ, 0 < δ₂ (n + 1) z →
      ∀ s : ℝ,
        |s| ≤ 1 / (4 * (observationLogSobolevConstant μ).toReal * δ₂ (n + 1) z) →
        Integrable
          (fun D : Dataset (Observation k m) (n + 1) =>
            Real.exp (s * (fittedLoss (T n) L D z -
              meanFittedLoss μ (T n) L z (hSt.mean_integrable z))))
          (Measure.pi fun _ : Fin (n + 1) => μ) ∧
        (∫ D : Dataset (Observation k m) (n + 1),
          Real.exp (s * (fittedLoss (T n) L D z -
            meanFittedLoss μ (T n) L z (hSt.mean_integrable z)))
          ∂Measure.pi fun _ : Fin (n + 1) => μ) ≤
          Real.exp ((2 * (observationLogSobolevConstant μ).toReal *
            ((δ₁ (n + 1) z)^2 + 2 * (δ₂ (n + 1) z)^2 *
              ((n + 1 : ℕ) : ℝ) * (∫ y, observationNormSq y ∂μ)) * s^2)) ∧
        Real.log (∫ D : Dataset (Observation k m) (n + 1),
          Real.exp (s * (fittedLoss (T n) L D z -
            meanFittedLoss μ (T n) L z (hSt.mean_integrable z)))
          ∂Measure.pi fun _ : Fin (n + 1) => μ) ≤
          (2 * (observationLogSobolevConstant μ).toReal *
            ((δ₁ (n + 1) z)^2 + 2 * (δ₂ (n + 1) z)^2 *
              ((n + 1 : ℕ) : ℝ) * (∫ y, observationNormSq y ∂μ)) * s^2) :=
  standing_deleted_loss_centered_exp_log_bound μ T L δ₁ δ₂ δ₃ c d hSt

#print axioms standing_I1_actual_deleted_section_average
#print axioms standing_deleted_fit_positive_source_mgf_consumer
#print axioms standing_deleted_loss_centered_exp_log_bound
#print axioms standing_deleted_loss_centered_exp_log_bound_zero

end LOOConcentration.Revision
