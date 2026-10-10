import LOOConcentrationManuscript.Internal.GenericUnitVarianceGrowthRatesConsumer
import LOOConcentrationManuscript.Internal.GenericPoincareGrowthEnergyConsumer
import LOOConcentrationManuscript.Internal.GenericUnitVarianceBoundCriterion

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

/-- Actual source family combines law-native cap energy, unbounded variance,
and the exact upper-bound vanishing criterion. No cap admission, moment
identity, gradient-law transfer, energy or variance inequality is supplied. -/
theorem generic_unit_variance_complete_source_consumer
    (μ : Measure (EuclideanSpace ℝ (Fin 1))) [IsProbabilityMeasure μ]
    (hFinite : LOOConcentration.Revision.logSobolevConstant μ < ⊤)
    (hM2 : Integrable (fun x => ‖x‖ ^ 2) μ)
    (hMean : (∫ x, x 0 ∂μ) = 0)
    (hUnitVariance : (∫ x, (x 0 - ∫ y, y 0 ∂μ) ^ 2 ∂μ) = 1)
    (b : ℕ → NNReal)
    (F : ∀ r : ℕ, EuclideanSpace ℝ (Fin (r + 1) × Fin 1) → ℝ)
    (hLoc : ∀ r, LocallyLipschitz (F r))
    (hGrad : ∀ r, ∀ᵐ x ∂(volume :
      Measure (EuclideanSpace ℝ (Fin (r + 1) × Fin 1))),
      DifferentiableAt ℝ (F r) x ∧ ‖gradient (F r) x‖ ≤ (b (r + 1) : ℝ) * ‖x‖) :
    let C := (LOOConcentration.Revision.logSobolevConstant μ).toReal
    let V : ℕ → ℝ := fun r =>
      ∫ x : EuclideanSpace ℝ (Fin (r + 1) × Fin 1),
        (F r x - ∫ y, F r y ∂LOOConcentration.Revision.euclideanProductLaw
          (κ := Fin (r + 1)) μ) ^ 2 ∂LOOConcentration.Revision.euclideanProductLaw
            (κ := Fin (r + 1)) μ
    0 < C ∧
    (∀ (r : ℕ) (R : NNReal),
      let ν := LOOConcentration.Revision.euclideanProductLaw (κ := Fin (r + 1)) μ
      let : IsProbabilityMeasure ν :=
        LOOConcentration.Revision.euclideanProductLaw_isProbabilityMeasure μ
      ∃ u : LOOConcentration.Revision.SobolevPair ν,
        ((WithLp.ofLp u.val).1 : EuclideanSpace ℝ (Fin (r + 1) × Fin 1) → ℝ) =ᵐ[ν]
          (fun x => max (-(R : ℝ)) (min (F r x) (R : ℝ))) ∧
        (LOOConcentration.Revision.sobolevEnergy ν u).toReal ≤
          (b (r + 1) : ℝ) ^ 2 * ((r + 1 : ℕ) : ℝ)) ∧
    (∀ r, V r ≤ C * (r + 1 : ℝ) * (b (r + 1) : ℝ) ^ 2) ∧
    (∀ B : ℝ, 0 ≤ B → (∀ r, (b (r + 1) : ℝ) ≤ B / Real.sqrt (r + 1 : ℝ)) →
      ∀ r, V r ≤ C * B ^ 2) ∧
    (Tendsto (fun r : ℕ => C * (b (r + 1) : ℝ) ^ 2 * (r + 1 : ℝ)) atTop (𝓝 0) ↔
      Tendsto (fun r : ℕ => (b (r + 1) : ℝ) * Real.sqrt (r + 1 : ℝ)) atTop (𝓝 0)) ∧
    (Tendsto (fun r : ℕ => (b (r + 1) : ℝ) * Real.sqrt (r + 1 : ℝ)) atTop (𝓝 0) →
      Tendsto V atTop (𝓝 0)) := by
  intro C V
  have hUnit := scalar_unit_variance_norm_sq_integral μ hMean hUnitVariance
  have hCriterion := generic_unit_variance_native_upper_bound_criterion
    μ hFinite hM2 hUnitVariance b
  have hRates := generic_unit_variance_growth_rates_consumer
    μ hFinite hM2 hMean hUnitVariance b F hLoc hGrad
  refine ⟨hCriterion.1, ?_, hRates.1, hRates.2.1, hCriterion.2, hRates.2.2⟩
  intro r R
  exact generic_product_source_growth_cap_energy μ hM2 hUnit r (F r)
    (hLoc r) (b (r + 1)) R (hGrad r)

end LOOConcentration.Manuscript.Internal
