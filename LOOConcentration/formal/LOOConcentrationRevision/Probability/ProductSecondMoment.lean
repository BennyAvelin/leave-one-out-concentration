import LOOConcentration.Probability.SampleMoments
import LOOConcentration.Geometry.NormTransport
import LOOConcentrationRevision.Geometry.CoordinateTransport
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false

namespace LOOConcentration.Revision

open MeasureTheory

/-- The actual Euclidean law of an ordered sample with independent observations. -/
noncomputable def datasetLawOfObservation {k m r : ℕ}
    (μ : Measure (Observation k m)) :
    Measure (EuclideanSpace ℝ (DatasetCoordinate k m r)) :=
  (Measure.pi fun _ : Fin r => μ).map datasetToEuclidean

theorem measurable_datasetToEuclidean {k m r : ℕ} :
    Measurable (datasetToEuclidean : Dataset (Observation k m) r →
      EuclideanSpace ℝ (DatasetCoordinate k m r)) := by
  have hcont : Continuous (datasetToEuclidean : Dataset (Observation k m) r →
      EuclideanSpace ℝ (DatasetCoordinate k m r)) := by
    change Continuous (fun D : Dataset (Observation k m) r =>
      WithLp.toLp (2 : ENNReal) (fun q : DatasetCoordinate k m r =>
        Sum.elim (D q.1).1 (D q.1).2 q.2))
    exact (PiLp.continuous_toLp (p := (2 : ENNReal))
        (β := fun _ : DatasetCoordinate k m r => ℝ)).comp (by
      apply continuous_pi
      intro q
      rcases q with ⟨i, c⟩
      cases c with
      | inl j =>
          exact ((continuous_apply j).comp continuous_fst).comp (continuous_apply i)
      | inr j =>
          exact ((continuous_apply j).comp continuous_snd).comp (continuous_apply i))
  exact hcont.measurable

theorem datasetLawOfObservation_isProbabilityMeasure {k m r : ℕ}
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (datasetLawOfObservation (r := r) μ) := by
  dsimp [datasetLawOfObservation]
  exact Measure.isProbabilityMeasure_map measurable_datasetToEuclidean.aemeasurable

private theorem norm_sq_datasetToEuclidean {k m r : ℕ}
    (D : Dataset (Observation k m) r) :
    ‖datasetToEuclidean D‖ ^ 2 = datasetNormSq D := by
  calc
    ‖datasetToEuclidean D‖ ^ 2 =
        datasetNorm (datasetOfEuclidean (datasetToEuclidean D)) ^ 2 := by
      rw [datasetNorm_datasetOfEuclidean]
    _ = datasetNorm D ^ 2 := by rw [datasetOfEuclidean_datasetToEuclidean]
    _ = datasetNormSq D := datasetNorm_sq D

theorem integrable_datasetLaw_norm_sq {k m r : ℕ}
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (hM2 : Integrable observationNormSq μ) :
    Integrable (fun x : EuclideanSpace ℝ (DatasetCoordinate k m r) => ‖x‖ ^ 2)
      (datasetLawOfObservation (r := r) μ) := by
  let P : Measure (Dataset (Observation k m) r) := Measure.pi fun _ : Fin r => μ
  have hcomp : Integrable
      ((fun x : EuclideanSpace ℝ (DatasetCoordinate k m r) => ‖x‖ ^ 2) ∘
        datasetToEuclidean) P := by
    convert integrable_datasetNormSq (μ := μ) (n := r) hM2 using 1
    funext D
    exact norm_sq_datasetToEuclidean D
  have hnorm : Continuous
      (fun x : EuclideanSpace ℝ (DatasetCoordinate k m r) => ‖x‖ ^ 2) :=
    continuous_norm.pow 2
  exact (integrable_map_measure hnorm.aestronglyMeasurable
    measurable_datasetToEuclidean.aemeasurable).2 hcomp

theorem integral_datasetLaw_norm_sq {k m r : ℕ}
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (hM2 : Integrable observationNormSq μ) :
    (∫ x : EuclideanSpace ℝ (DatasetCoordinate k m r), ‖x‖ ^ 2
      ∂datasetLawOfObservation (r := r) μ) =
      (r : ℝ) * ∫ z, observationNormSq z ∂μ := by
  let P : Measure (Dataset (Observation k m) r) := Measure.pi fun _ : Fin r => μ
  have hnorm : Continuous
      (fun x : EuclideanSpace ℝ (DatasetCoordinate k m r) => ‖x‖ ^ 2) :=
    continuous_norm.pow 2
  change (∫ x : EuclideanSpace ℝ (DatasetCoordinate k m r), ‖x‖ ^ 2
      ∂(Measure.pi fun _ : Fin r => μ).map datasetToEuclidean) = _
  rw [integral_map measurable_datasetToEuclidean.aemeasurable
    hnorm.aestronglyMeasurable]
  have hEq : (fun D : Dataset (Observation k m) r =>
      ‖datasetToEuclidean D‖ ^ 2) = datasetNormSq := by
    funext D
    exact norm_sq_datasetToEuclidean D
  rw [hEq]
  exact integral_datasetNormSq (μ := μ) (n := r) hM2

#print axioms LOOConcentration.Revision.datasetLawOfObservation
#print axioms LOOConcentration.Revision.measurable_datasetToEuclidean
#print axioms LOOConcentration.Revision.datasetLawOfObservation_isProbabilityMeasure
#print axioms LOOConcentration.Revision.integrable_datasetLaw_norm_sq
#print axioms LOOConcentration.Revision.integral_datasetLaw_norm_sq

end LOOConcentration.Revision
