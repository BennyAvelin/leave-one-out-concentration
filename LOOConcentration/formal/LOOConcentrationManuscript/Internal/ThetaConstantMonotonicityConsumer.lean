import LOOConcentrationManuscript.Internal.ThetaConstantMonotonicity
import LOOConcentrationRevision.Frozen.Definitions.LogSobolevConstant
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal

open MeasureTheory
open scoped ENNReal

/-- The certified native LSI bound for coordinate padding supplies the
constant order used by the manuscript's unchanged theta rate. The moment is
the actual squared-norm integral; no finite-second-moment hypothesis is
needed for this comparison. -/
theorem coordinatePaddingFinOneFinTwo_thetaRate_mono_native
    (μ : Measure (EuclideanSpace ℝ (Fin 1))) [IsProbabilityMeasure μ]
    (hfinite : LOOConcentration.Revision.logSobolevConstant μ < ⊤)
    (r : ℕ) (hr : 1 ≤ r) (t : ℝ) (ht : 0 < t)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    letI : IsProbabilityMeasure (μ.map coordinatePaddingFinOneFinTwo) :=
      μ.isProbabilityMeasure_map
        coordinatePaddingFinOneFinTwo.continuous.measurable.aemeasurable
    let M₂ : ℝ := ∫ x : EuclideanSpace ℝ (Fin 1), ‖x‖ ^ 2 ∂μ
    (LOOConcentration.Revision.logSobolevConstant
        (μ.map coordinatePaddingFinOneFinTwo) < ⊤) ∧
      LOOConcentration.Revision.thetaRate
          (LOOConcentration.Revision.logSobolevConstant
            (μ.map coordinatePaddingFinOneFinTwo)).toReal
          M₂ ENNReal.toReal_nonneg (integral_nonneg (fun x => sq_nonneg ‖x‖))
          r hr t ht a b ha hb ≤
        LOOConcentration.Revision.thetaRate
          (LOOConcentration.Revision.logSobolevConstant μ).toReal
          M₂ ENNReal.toReal_nonneg (integral_nonneg (fun x => sq_nonneg ‖x‖))
          r hr t ht a b ha hb := by
  have hnative := coordinatePaddingFinOneFinTwo_logSobolevConstant_le μ
  let μ₂ : Measure (EuclideanSpace ℝ (Fin 2)) :=
    μ.map coordinatePaddingFinOneFinTwo
  have hμ₂prob : IsProbabilityMeasure μ₂ :=
    μ.isProbabilityMeasure_map
      coordinatePaddingFinOneFinTwo.continuous.measurable.aemeasurable
  let Cimage : ℝ≥0∞ :=
    @LOOConcentration.Revision.logSobolevConstant (Fin 2) inferInstance inferInstance
      μ₂ hμ₂prob
  have hnative' : Cimage ≤ LOOConcentration.Revision.logSobolevConstant μ := by
    exact hnative
  have hImageFinite :
      Cimage < ⊤ := lt_of_le_of_lt hnative' hfinite
  have hRealOrder := ENNReal.toReal_mono hfinite.ne hnative'
  let M₂ : ℝ := ∫ x : EuclideanSpace ℝ (Fin 1), ‖x‖ ^ 2 ∂μ
  have hM₂ : 0 ≤ M₂ := by
    dsimp [M₂]
    exact integral_nonneg (fun x => sq_nonneg ‖x‖)
  constructor
  · change Cimage < ⊤
    exact hImageFinite
  · change LOOConcentration.Revision.thetaRate Cimage.toReal M₂
      ENNReal.toReal_nonneg (integral_nonneg (fun x => sq_nonneg ‖x‖))
      r hr t ht a b ha hb ≤ _
    exact thetaRate_mono_constant Cimage.toReal
      (LOOConcentration.Revision.logSobolevConstant μ).toReal
      M₂ ENNReal.toReal_nonneg ENNReal.toReal_nonneg hM₂ hRealOrder
      r hr t ht a b ha hb

end LOOConcentration.Manuscript.Internal
