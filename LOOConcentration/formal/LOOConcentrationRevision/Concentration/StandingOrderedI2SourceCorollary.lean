import LOOConcentrationRevision.Concentration.StandingValidationThetaSourceCorollary
import LOOConcentrationRevision.Concentration.StandingValidationAverageGradient
import LOOConcentrationRevision.Geometry.CoordinateTransport
import LOOConcentrationRevision.Probability.ProductSecondMoment

set_option autoImplicit false

namespace LOOConcentration.Revision

open MeasureTheory

/-- Both strict tails for the source ordered-product mean-minus-validation-average
term. The product mean and the event transfer are internal to this consumer. -/
theorem standing_validation_ordered_I2_tails_via_source_corollary
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)
    (t : ℝ) (ht : 0 < t) :
    let P := Measure.pi fun _ : Fin (n+2) => μ
    let V := fun D : Dataset (Observation k m) (n+2) =>
      (∑ i : Fin (n+2), meanFittedLoss μ (T n) L (D i)
        (hSt.mean_integrable (D i))) / (n+2:ℝ)
    let I₂ := fun D : Dataset (Observation k m) (n+2) =>
      (∫ E, V E ∂P) - V D
    let C := (observationLogSobolevConstant μ).toReal
    let M₂ := ∫ z, observationNormSq z ∂μ
    let a := c / Real.sqrt (n+2:ℝ)
    let b := d / (n+2:ℝ)
    let θ := thetaRate C M₂ (ENNReal.toReal_nonneg)
      (integral_nonneg_of_ae (ae_of_all _ fun z => observationNormSq_nonneg z))
      (n+2) (by omega) t ht a b
      (div_nonneg hSt.c_nonneg (Real.sqrt_nonneg _))
      (div_nonneg hSt.d_nonneg (by positivity))
    P.real {D | I₂ D > t} ≤ θ ∧ P.real {D | -I₂ D > t} ≤ θ := by
  let P : Measure (Dataset (Observation k m) (n+2)) :=
    Measure.pi fun _ : Fin (n+2) => μ
  let ν := datasetLawOfObservation (r := n+2) μ
  let F : EuclideanSpace ℝ (DatasetCoordinate k m (n+2)) → ℝ := fun x =>
    standingValidationAverage μ T L δ₁ δ₂ δ₃ c d hSt (datasetOfEuclidean x)
  let V : Dataset (Observation k m) (n+2) → ℝ := fun D =>
    (∑ i : Fin (n+2), meanFittedLoss μ (T n) L (D i)
      (hSt.mean_integrable (D i))) / (n+2:ℝ)
  let I₂ : Dataset (Observation k m) (n+2) → ℝ :=
    fun D => (∫ E, V E ∂P) - V D
  let C : ℝ := (observationLogSobolevConstant μ).toReal
  let M₂ : ℝ := ∫ z, observationNormSq z ∂μ
  let a : ℝ := c / Real.sqrt (n+2:ℝ)
  let b : ℝ := d / (n+2:ℝ)
  let θ : ℝ := thetaRate C M₂ (ENNReal.toReal_nonneg)
    (integral_nonneg_of_ae (ae_of_all _ fun z => observationNormSq_nonneg z))
    (n+2) (by omega) t ht a b
    (div_nonneg hSt.c_nonneg (Real.sqrt_nonneg _))
    (div_nonneg hSt.d_nonneg (by positivity))
  have hν : ν = P.map datasetToEuclidean := rfl
  have hFcont : Continuous F := by
    exact (standing_validation_average_gradient μ T L δ₁ δ₂ δ₃ c d hSt).1.continuous
  have hFmeas : Measurable F := hFcont.measurable
  have hVeq (D : Dataset (Observation k m) (n+2)) :
      V D = standingValidationAverage μ T L δ₁ δ₂ δ₃ c d hSt D := by
    simp [V, standingValidationAverage]
    ring
  have hVmap (D : Dataset (Observation k m) (n+2)) :
      F (datasetToEuclidean D) = V D := by
    calc
      F (datasetToEuclidean D) =
          standingValidationAverage μ T L δ₁ δ₂ δ₃ c d hSt D := by
        simp [F, datasetOfEuclidean_datasetToEuclidean]
      _ = V D := (hVeq D).symm
  have hMean : (∫ x, F x ∂ν) = ∫ D, V D ∂P := by
    rw [hν]
    rw [integral_map measurable_datasetToEuclidean.aemeasurable
      hFmeas.aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards [] with D
    exact hVmap D
  have hI₂map (D : Dataset (Observation k m) (n+2)) :
      I₂ D = (∫ x, F x ∂ν) - F (datasetToEuclidean D) := by
    simp only [I₂]
    rw [hMean, ← hVmap]
  have hEventI₂ : MeasurableSet {x : EuclideanSpace ℝ (DatasetCoordinate k m (n+2)) |
      (∫ y, F y ∂ν) - F x > t} :=
    measurableSet_Ioi.preimage (measurable_const.sub hFmeas)
  have hEventNegI₂ : MeasurableSet {x : EuclideanSpace ℝ (DatasetCoordinate k m (n+2)) |
      F x - (∫ y, F y ∂ν) > t} :=
    measurableSet_Ioi.preimage (hFmeas.sub measurable_const)
  have hMapI₂ : ν {x | (∫ y, F y ∂ν) - F x > t} =
      P {D | I₂ D > t} := by
    change (P.map datasetToEuclidean) {x | (∫ y, F y ∂ν) - F x > t} = _
    rw [Measure.map_apply measurable_datasetToEuclidean hEventI₂]
    congr 1
    ext D
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    rw [hI₂map]
  have hMapNegI₂ : ν {x | F x - (∫ y, F y ∂ν) > t} =
      P {D | -I₂ D > t} := by
    change (P.map datasetToEuclidean) {x | F x - (∫ y, F y ∂ν) > t} = _
    rw [Measure.map_apply measurable_datasetToEuclidean hEventNegI₂]
    congr 1
    ext D
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    rw [hI₂map]
    constructor <;> intro h <;> linarith
  have hMapI₂Real : ν.real {x | (∫ y, F y ∂ν) - F x > t} =
      P.real {D | I₂ D > t} := by
    unfold Measure.real
    rw [hMapI₂]
  have hMapNegI₂Real : ν.real {x | F x - (∫ y, F y ∂ν) > t} =
      P.real {D | -I₂ D > t} := by
    unfold Measure.real
    rw [hMapNegI₂]
  have hθ := standing_validation_theta_tails_via_source_corollary
    μ T L δ₁ δ₂ δ₃ c d hSt t ht
  change P.real {D | I₂ D > t} ≤ θ ∧ P.real {D | -I₂ D > t} ≤ θ
  constructor
  · rw [← hMapI₂Real]
    simpa [ν, F, C, M₂, a, b, θ] using hθ.2
  · rw [← hMapNegI₂Real]
    simpa [ν, F, C, M₂, a, b, θ] using hθ.1

end LOOConcentration.Revision
