import LOOConcentrationManuscript.Internal.ScalarObservationLSITransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open MeasureTheory
open scoped ENNReal

theorem scalarFeatureObservation_nativeConstant_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    let φ := fun x : ℝ =>
      (((fun _ : Fin 1 => x), (fun _ : Fin 1 => (0 : ℝ))) : LOOConcentration.Observation 1 1)
    let scalar := fun x : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => x)
    letI : IsProbabilityMeasure (μ.map φ) := μ.isProbabilityMeasure_map (by fun_prop)
    letI : IsProbabilityMeasure (μ.map scalar) := μ.isProbabilityMeasure_map (by fun_prop)
    LOOConcentration.Revision.observationLogSobolevConstant (μ.map φ) ≤
      LOOConcentration.Revision.logSobolevConstant (μ.map scalar) :=
  scalarObservation_logSobolevConstant_le μ false

theorem scalarResponseObservation_nativeConstant_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    let φ := fun x : ℝ =>
      (((fun _ : Fin 1 => (0 : ℝ)), (fun _ : Fin 1 => x)) : LOOConcentration.Observation 1 1)
    let scalar := fun x : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => x)
    letI : IsProbabilityMeasure (μ.map φ) := μ.isProbabilityMeasure_map (by fun_prop)
    letI : IsProbabilityMeasure (μ.map scalar) := μ.isProbabilityMeasure_map (by fun_prop)
    LOOConcentration.Revision.observationLogSobolevConstant (μ.map φ) ≤
      LOOConcentration.Revision.logSobolevConstant (μ.map scalar) :=
  scalarObservation_logSobolevConstant_le μ true

end LOOConcentration.Manuscript.Internal
