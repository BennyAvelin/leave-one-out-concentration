import LOOConcentrationManuscript.Internal.ScalarObservationLSITransport
import LOOConcentrationManuscript.Internal.ScalarObservationMomentLawTransportConsumer
import LOOConcentrationManuscript.Internal.ThetaConstantMonotonicity

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open MeasureTheory
open scoped ENNReal

/-- The actual observation law's rate is bounded by the unchanged scalar source
rate, with its original native constant and its original second moment. -/
theorem scalarObservation_thetaRate_le_scalar_source
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hSecond : Integrable (fun x : ℝ => x ^ 2) μ) (response : Bool)
    (hfinite :
      let scalar := fun x : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => x)
      letI : IsProbabilityMeasure (μ.map scalar) := μ.isProbabilityMeasure_map (by fun_prop)
      LOOConcentration.Revision.logSobolevConstant (μ.map scalar) < ⊤)
    (r : ℕ) (hr : 1 ≤ r) (t : ℝ) (ht : 0 < t)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    let φ := fun x : ℝ => (if response then
      ((fun _ : Fin 1 => 0), (fun _ : Fin 1 => x)) else
      ((fun _ : Fin 1 => x), (fun _ : Fin 1 => 0)) : LOOConcentration.Observation 1 1)
    let scalar := fun x : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => x)
    letI : IsProbabilityMeasure (μ.map φ) := μ.isProbabilityMeasure_map
      (by
        have h : Continuous φ := by
          cases response
          · change Continuous (fun x : ℝ => ((fun _ : Fin 1 => x), (fun _ : Fin 1 => (0 : ℝ))))
            fun_prop
          · change Continuous (fun x : ℝ => ((fun _ : Fin 1 => (0 : ℝ)), (fun _ : Fin 1 => x)))
            fun_prop
        exact h.measurable.aemeasurable)
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
  classical
  intro φ scalar
  have hφ : Measurable φ := by
    cases response
    · change Measurable (fun x : ℝ => ((fun _ : Fin 1 => x), (fun _ : Fin 1 => (0 : ℝ))))
      fun_prop
    · change Measurable (fun x : ℝ => ((fun _ : Fin 1 => (0 : ℝ)), (fun _ : Fin 1 => x)))
      fun_prop
  have hs : Measurable scalar := by fun_prop
  let : IsProbabilityMeasure (μ.map φ) := μ.isProbabilityMeasure_map hφ.aemeasurable
  let : IsProbabilityMeasure (μ.map scalar) := μ.isProbabilityMeasure_map hs.aemeasurable
  have hnative := scalarObservation_logSobolevConstant_le μ response
  have hImageFinite := lt_of_le_of_lt hnative hfinite
  have hRealOrder := ENNReal.toReal_mono hfinite.ne hnative
  have hmoment : (∫ z : LOOConcentration.Observation 1 1,
      LOOConcentration.observationNormSq z ∂(μ.map φ)) = ∫ x : ℝ, x ^ 2 ∂μ :=
    (scalarObservation_sample_and_fresh_test_transport μ hSecond response 0).2.2.1
  have hM₂ : 0 ≤ ∫ x : ℝ, x ^ 2 ∂μ :=
    integral_nonneg (fun x => sq_nonneg x)
  refine ⟨hImageFinite, ?_⟩
  simpa only [hmoment] using
    thetaRate_mono_constant
      (LOOConcentration.Revision.observationLogSobolevConstant (μ.map φ)).toReal
      (LOOConcentration.Revision.logSobolevConstant (μ.map scalar)).toReal
      (∫ x : ℝ, x ^ 2 ∂μ) ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      hM₂ hRealOrder r hr t ht a b ha hb

end LOOConcentration.Manuscript.Internal
