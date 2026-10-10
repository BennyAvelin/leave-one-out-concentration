import LOOConcentrationManuscript.Internal.ScalarObservationThetaRate

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open MeasureTheory
open scoped ENNReal

/-- The literal quadratic-mean response embedding supplies a rate comparison
using the manuscript's unchanged scalar constant and second moment. -/
theorem scalarResponse_thetaRate_le_original_source
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hSecond : Integrable (fun x : ℝ => x ^ 2) μ)
    (hfinite :
      let scalar := fun x : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => x)
      letI : IsProbabilityMeasure (μ.map scalar) := μ.isProbabilityMeasure_map (by fun_prop)
      LOOConcentration.Revision.logSobolevConstant (μ.map scalar) < ⊤)
    (r : ℕ) (hr : 1 ≤ r) (t : ℝ) (ht : 0 < t)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    let φ := fun x : ℝ =>
      (((fun _ : Fin 1 => (0 : ℝ)), (fun _ : Fin 1 => x)) : LOOConcentration.Observation 1 1)
    let scalar := fun x : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => x)
    letI : IsProbabilityMeasure (μ.map φ) := μ.isProbabilityMeasure_map (by fun_prop)
    letI : IsProbabilityMeasure (μ.map scalar) := μ.isProbabilityMeasure_map (by fun_prop)
    (LOOConcentration.Revision.observationLogSobolevConstant (μ.map φ) < ⊤) ∧
      LOOConcentration.Revision.thetaRate
        (LOOConcentration.Revision.observationLogSobolevConstant (μ.map φ)).toReal
        (∫ z, LOOConcentration.observationNormSq z ∂(μ.map φ))
        ENNReal.toReal_nonneg (integral_nonneg LOOConcentration.observationNormSq_nonneg)
        r hr t ht a b ha hb ≤
      LOOConcentration.Revision.thetaRate
        (LOOConcentration.Revision.logSobolevConstant (μ.map scalar)).toReal
        (∫ x : ℝ, x ^ 2 ∂μ)
        ENNReal.toReal_nonneg (integral_nonneg (fun x => sq_nonneg x))
        r hr t ht a b ha hb := by
  exact scalarObservation_thetaRate_le_scalar_source μ hSecond true hfinite r hr t ht a b ha hb

end LOOConcentration.Manuscript.Internal
