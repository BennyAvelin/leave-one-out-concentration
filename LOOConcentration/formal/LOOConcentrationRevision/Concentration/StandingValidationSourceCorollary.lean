import LOOConcentrationRevision.Results.SourceProductThetaTails
import LOOConcentrationRevision.Concentration.StandingValidationAveragePositiveMGF

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory

/-- Actual source validation-average tails, using the quadratic-gradient
corollary with every premise supplied by the standing assumption. -/
theorem standing_validation_tails_via_source_corollary
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)
    (t : ℝ) (ht : 0 < t) :
    let ν := datasetLawOfObservation (r := n+2) μ
    let F := fun x : EuclideanSpace ℝ (DatasetCoordinate k m (n+2)) =>
      standingValidationAverage μ T L δ₁ δ₂ δ₃ c d hSt (datasetOfEuclidean x)
    let C := (observationLogSobolevConstant μ).toReal
    let M₂ := ∫ z, observationNormSq z ∂μ
    let a := c / Real.sqrt (n+2:ℝ)
    let b := d / (n+2:ℝ)
    let θ := thetaRate C M₂ ENNReal.toReal_nonneg
      (integral_nonneg_of_ae (ae_of_all _ fun z => observationNormSq_nonneg z))
      (n+2) (by omega) t ht a b
      (div_nonneg hSt.c_nonneg (Real.sqrt_nonneg _))
      (div_nonneg hSt.d_nonneg (by positivity))
    let G := if C * a ^ 2 = 0 then 0 else Real.exp (-(t ^ 2 / (2 * C * a ^ 2)))
    ν.real {x | F x - ∫ y, F y ∂ν > t} ≤ (if b = 0 then G else θ) ∧
      ν.real {x | ∫ y, F y ∂ν - F x > t} ≤ (if b = 0 then G else θ) := by
  let μE : Measure (EuclideanSpace ℝ (ObservationCoordinate k m)) :=
    μ.map observationToEuclidean
  let : IsProbabilityMeasure μE :=
    Measure.isProbabilityMeasure_map measurable_observationToEuclidean.aemeasurable
  let F : EuclideanSpace ℝ (DatasetCoordinate k m (n+2)) → ℝ := fun x =>
    standingValidationAverage μ T L δ₁ δ₂ δ₃ c d hSt (datasetOfEuclidean x)
  have hM2 : Integrable (fun x : EuclideanSpace ℝ (ObservationCoordinate k m) =>
      ‖x‖ ^ 2) μE := by
    have hcomp : Integrable
        (fun z : Observation k m => ‖observationToEuclidean z‖ ^ 2) μ :=
      hSt.second_moment.congr (ae_of_all _ fun z => by
        calc
          observationNormSq z = observationNorm z ^ 2 := (observationNorm_sq z).symm
          _ = ‖observationToEuclidean z‖ ^ 2 := by rw [observationNorm_eq_euclidean])
    exact (integrable_map_measure (continuous_norm.pow 2).aestronglyMeasurable
      measurable_observationToEuclidean.aemeasurable).2 hcomp
  have hM2eq :
      (∫ x : EuclideanSpace ℝ (ObservationCoordinate k m), ‖x‖ ^ 2 ∂μE) =
        ∫ z, observationNormSq z ∂μ := by
    change (∫ x : EuclideanSpace ℝ (ObservationCoordinate k m), ‖x‖ ^ 2
      ∂(μ.map observationToEuclidean)) = _
    have hnorm : Continuous
        (fun x : EuclideanSpace ℝ (ObservationCoordinate k m) => ‖x‖ ^ 2) :=
      continuous_norm.pow 2
    rw [integral_map measurable_observationToEuclidean.aemeasurable
      hnorm.aestronglyMeasurable]
    congr 1
    funext z
    rw [← observationNorm_eq_euclidean, observationNorm_sq]
  have hreg := standing_validation_average_gradient μ T L δ₁ δ₂ δ₃ c d hSt
  have hsrc := source_product_theta_tails (n+2) (by omega) μE
    hSt.lsi.ne hM2 F hreg.1 (c / Real.sqrt (n+2:ℝ)) (d / (n+2:ℝ))
    (div_nonneg hSt.c_nonneg (Real.sqrt_nonneg _))
    (div_nonneg hSt.d_nonneg (by positivity)) hreg.2 t ht
  dsimp only at hsrc ⊢
  simp_rw [hM2eq] at hsrc
  simpa [μE, F, DatasetCoordinate, observationLogSobolevConstant,
    euclideanProductLaw_observation_map_eq_datasetLaw μ, Nat.cast_add, Nat.cast_ofNat]
    using hsrc

end LOOConcentration.Revision
