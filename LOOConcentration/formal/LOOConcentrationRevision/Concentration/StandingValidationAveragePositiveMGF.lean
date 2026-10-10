import LOOConcentrationRevision.Concentration.StandingValidationAverageGradient
import LOOConcentrationRevision.Concentration.SourceProductMgfAllSizes
import LOOConcentrationRevision.Probability.ProductLawTransport
import LOOConcentrationRevision.Frozen.Definitions.Measurable_observationToEuclidean
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false

namespace LOOConcentration.Revision

open MeasureTheory

noncomputable def standingValidationAverageEuclidean
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d) :
    EuclideanSpace ℝ (DatasetCoordinate k m (n+2)) → ℝ :=
  fun x => standingValidationAverage μ T L δ₁ δ₂ δ₃ c d hSt (datasetOfEuclidean x)

/-- The positive-growth source consumer applied to the actual validation average.
The centered law is the exact ordered dataset law, and the raw second moment
remains the source observation moment. -/
theorem standing_validation_average_positive_growth_mgf
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)
    (hd : 0 < d) (t : ℝ)
    (hcut : |t| ≤ 1 / (4 * (observationLogSobolevConstant μ).toReal *
      (d / (n+2:ℝ)))) :
    let ν := datasetLawOfObservation (r := n+2) μ
    let F := fun x : EuclideanSpace ℝ (DatasetCoordinate k m (n+2)) =>
      standingValidationAverage μ T L δ₁ δ₂ δ₃ c d hSt (datasetOfEuclidean x)
    let V := (2 * (observationLogSobolevConstant μ).toReal *
      ((c / Real.sqrt (n+2:ℝ)) ^ 2 +
        2 * (d / (n+2:ℝ)) ^ 2 * (n+2:ℝ) *
          ∫ z, observationNormSq z ∂μ)) * t^2
    Integrable F ν ∧
      Integrable (fun x => Real.exp (t * (F x - ∫ y, F y ∂ν))) ν ∧
      (∫ x, Real.exp (t * (F x - ∫ y, F y ∂ν)) ∂ν) ≤ Real.exp V ∧
      Real.log (∫ x, Real.exp (t * (F x - ∫ y, F y ∂ν)) ∂ν) ≤ V := by
  let μE : Measure (EuclideanSpace ℝ (ObservationCoordinate k m)) :=
    μ.map observationToEuclidean
  let C : ℝ := (observationLogSobolevConstant μ).toReal
  let a : NNReal := Real.toNNReal (c / Real.sqrt (n+2:ℝ))
  let b : NNReal := Real.toNNReal (d / (n+2:ℝ))
  let F : EuclideanSpace ℝ (DatasetCoordinate k m (n+2)) → ℝ := fun x =>
    standingValidationAverage μ T L δ₁ δ₂ δ₃ c d hSt (datasetOfEuclidean x)
  let νE := euclideanProductLaw (κ := Fin (n+2)) μE
  have hμE : IsProbabilityMeasure μE :=
    Measure.isProbabilityMeasure_map measurable_observationToEuclidean.aemeasurable
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hLC : logSobolevConstant μE ≤ ENNReal.ofReal C := by
    change logSobolevConstant (μ.map observationToEuclidean) ≤
      ENNReal.ofReal (observationLogSobolevConstant μ).toReal
    rw [ENNReal.ofReal_toReal hSt.lsi.ne]
    rfl
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
      (∫ x : EuclideanSpace ℝ (ObservationCoordinate k m), ‖x‖^2 ∂μE) =
        ∫ z, observationNormSq z ∂μ := by
    change (∫ x : EuclideanSpace ℝ (ObservationCoordinate k m), ‖x‖^2
      ∂(μ.map observationToEuclidean)) = _
    have hnorm : Continuous
        (fun x : EuclideanSpace ℝ (ObservationCoordinate k m) => ‖x‖^2) :=
      continuous_norm.pow 2
    rw [integral_map measurable_observationToEuclidean.aemeasurable
      hnorm.aestronglyMeasurable]
    congr 1
    funext z
    calc
      ‖observationToEuclidean z‖^2 = observationNorm z^2 := by
        rw [observationNorm_eq_euclidean]
      _ = observationNormSq z := observationNorm_sq z
  have hca : (a : ℝ) = c / Real.sqrt (n+2:ℝ) := by
    exact Real.coe_toNNReal _ (div_nonneg hSt.c_nonneg (Real.sqrt_nonneg _))
  have hdb : (b : ℝ) = d / (n+2:ℝ) := by
    exact Real.coe_toNNReal _ (div_nonneg hSt.d_nonneg (by positivity))
  have hb : 0 < (b : ℝ) := by rw [hdb]; exact div_pos hd (by positivity)
  have hreg := standing_validation_average_gradient μ T L δ₁ δ₂ δ₃ c d hSt
  have hgrad : ∀ᵐ x ∂(volume :
      Measure (EuclideanSpace ℝ (DatasetCoordinate k m (n+2)))),
      DifferentiableAt ℝ F x ∧ ‖gradient F x‖ ≤ (a:ℝ)+(b:ℝ)*‖x‖ := by
    filter_upwards [hreg.2] with x hx
    simpa [F, hca, hdb] using hx
  have hcutSrc : |t| ≤ 1/(4*C*(b:ℝ)) := by simpa [C,hdb] using hcut
  have hsrc := source_product_centered_mgf_positive_growth_all_sizes
    (n+2) μE C hC hLC hM2 F hreg.1 a b hb hgrad t hcutSrc
  simp_rw [hM2eq] at hsrc
  have hsrcD := hsrc
  simp only [μE, euclideanProductLaw_observation_map_eq_datasetLaw μ] at hsrcD
  dsimp only
  simpa [F, C, hca, hdb, DatasetCoordinate] using hsrcD

end LOOConcentration.Revision
