import LOOConcentrationManuscript.Internal.GenericUnboundedGrowthPoincare
import LOOConcentrationManuscript.Internal.GenericUnitVarianceGrowthRates
import LOOConcentrationRevision.Frozen.Definitions.LogSobolevConstant
import Mathlib.Topology.Algebra.Order.Field

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal

open MeasureTheory Filter
open scoped ENNReal Topology

/-- The actual source family under the finite product law. Every variance is
the literal centered-square integral of the same locally Lipschitz statistic;
only the source coefficient `δ₂(N)` varies with sample size. The critical
conclusion is an upper bound and asserts no positive lower bound. -/
theorem generic_unit_variance_growth_rates_consumer
    (μ : Measure (EuclideanSpace ℝ (Fin 1))) [IsProbabilityMeasure μ]
    (hfinite : LOOConcentration.Revision.logSobolevConstant μ < ⊤)
    (hM2 : Integrable (fun x : EuclideanSpace ℝ (Fin 1) => ‖x‖ ^ 2) μ)
    (hmean : (∫ x : EuclideanSpace ℝ (Fin 1), x 0 ∂μ) = 0)
    (hcentered :
      (∫ x : EuclideanSpace ℝ (Fin 1),
        (x 0 - ∫ y : EuclideanSpace ℝ (Fin 1), y 0 ∂μ) ^ 2 ∂μ) = 1)
    (δ₂ : ℕ → NNReal)
    (F : ∀ r : ℕ, EuclideanSpace ℝ (Fin (r + 1) × Fin 1) → ℝ)
    (hF : ∀ r, LocallyLipschitz (F r))
    (hgrad : ∀ r, ∀ᵐ x ∂(volume :
      Measure (EuclideanSpace ℝ (Fin (r + 1) × Fin 1))),
      DifferentiableAt ℝ (F r) x ∧
        ‖gradient (F r) x‖ ≤ (δ₂ (r + 1) : ℝ) * ‖x‖) :
    let V : ℕ → ℝ := fun r =>
      ∫ x : EuclideanSpace ℝ (Fin (r + 1) × Fin 1),
        (F r x - ∫ y, F r y ∂LOOConcentration.Revision.euclideanProductLaw
          (κ := Fin (r + 1)) μ) ^ 2 ∂LOOConcentration.Revision.euclideanProductLaw
            (κ := Fin (r + 1)) μ
    (∀ r, V r ≤ (LOOConcentration.Revision.logSobolevConstant μ).toReal *
      (r + 1 : ℝ) * (δ₂ (r + 1) : ℝ) ^ 2) ∧
    (∀ B : ℝ, 0 ≤ B →
      (∀ r, (δ₂ (r + 1) : ℝ) ≤ B / Real.sqrt (r + 1 : ℝ)) →
      ∀ r, V r ≤ (LOOConcentration.Revision.logSobolevConstant μ).toReal * B ^ 2) ∧
    (Tendsto (fun r : ℕ => (δ₂ (r + 1) : ℝ) * Real.sqrt (r + 1 : ℝ)) atTop (𝓝 0) →
      Tendsto V atTop (𝓝 0)) := by
  dsimp
  let V : ℕ → ℝ := fun r =>
    ∫ x : EuclideanSpace ℝ (Fin (r + 1) × Fin 1),
      (F r x - ∫ y, F r y ∂LOOConcentration.Revision.euclideanProductLaw
        (κ := Fin (r + 1)) μ) ^ 2 ∂LOOConcentration.Revision.euclideanProductLaw
          (κ := Fin (r + 1)) μ
  have hvariance (r : ℕ) :
      V r ≤ (LOOConcentration.Revision.logSobolevConstant μ).toReal *
        (r + 1 : ℝ) * (δ₂ (r + 1) : ℝ) ^ 2 := by
    dsimp [V]
    exact generic_unbounded_growth_variance_le μ hfinite hM2 hmean hcentered r
      (F r) (hF r) (δ₂ (r + 1)) (hgrad r)
  have hVnonneg (r : ℕ) : 0 ≤ V r := by
    dsimp [V]
    exact integral_nonneg (fun x => sq_nonneg _)
  refine ⟨hvariance, ?_, ?_⟩
  · intro B hB hcritical
    exact generic_unit_variance_critical_rate_upper
      (LOOConcentration.Revision.logSobolevConstant μ).toReal B
      ENNReal.toReal_nonneg hB δ₂ V hvariance hcritical
  · intro hsubcritical
    exact generic_unit_variance_subcritical_rate_tendsto_zero
      (LOOConcentration.Revision.logSobolevConstant μ).toReal δ₂ V
      hvariance hVnonneg hsubcritical

end LOOConcentration.Manuscript.Internal
