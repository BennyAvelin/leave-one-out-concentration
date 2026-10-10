import LOOConcentrationRevision.Frozen.Definitions.ObservationOfEuclidean
import LOOConcentrationRevision.Frozen.Definitions.DatasetOfEuclidean

/-!
# Coordinate transport for the approved revision

The approved inverse maps undo the historical coordinate flattening. These
identities include empty feature, response and sample index sets.
-/

set_option autoImplicit false

namespace LOOConcentration.Revision

@[simp]
theorem observationOfEuclidean_observationToEuclidean {k m : ℕ}
    (z : Observation k m) : observationOfEuclidean (observationToEuclidean z) = z := by
  rfl

@[simp]
theorem observationToEuclidean_observationOfEuclidean {k m : ℕ}
    (x : EuclideanSpace ℝ (ObservationCoordinate k m)) :
    observationToEuclidean (observationOfEuclidean x) = x := by
  apply PiLp.ext
  intro q
  cases q <;> rfl

@[simp]
theorem datasetOfEuclidean_datasetToEuclidean {k m r : ℕ}
    (D : Dataset (Observation k m) r) : datasetOfEuclidean (datasetToEuclidean D) = D := by
  rfl

@[simp]
theorem datasetToEuclidean_datasetOfEuclidean {k m r : ℕ}
    (x : EuclideanSpace ℝ (DatasetCoordinate k m r)) :
    datasetToEuclidean (datasetOfEuclidean x) = x := by
  apply PiLp.ext
  rintro ⟨i, q⟩
  cases q <;> rfl

theorem observationNorm_observationOfEuclidean {k m : ℕ}
    (x : EuclideanSpace ℝ (ObservationCoordinate k m)) :
    observationNorm (observationOfEuclidean x) = ‖x‖ := by
  rw [observationNorm_eq_euclidean, observationToEuclidean_observationOfEuclidean]

theorem datasetNorm_datasetOfEuclidean {k m r : ℕ}
    (x : EuclideanSpace ℝ (DatasetCoordinate k m r)) :
    datasetNorm (datasetOfEuclidean x) = ‖x‖ := by
  rw [datasetNorm_eq_euclidean, datasetToEuclidean_datasetOfEuclidean]

theorem continuous_observationOfEuclidean {k m : ℕ} :
    Continuous (observationOfEuclidean :
      EuclideanSpace ℝ (ObservationCoordinate k m) → Observation k m) := by
  apply Continuous.prodMk
  · exact continuous_pi fun i => PiLp.continuous_apply 2 (fun _ => ℝ) (Sum.inl i)
  · exact continuous_pi fun j => PiLp.continuous_apply 2 (fun _ => ℝ) (Sum.inr j)

theorem measurable_observationOfEuclidean {k m : ℕ} :
    Measurable (observationOfEuclidean :
      EuclideanSpace ℝ (ObservationCoordinate k m) → Observation k m) :=
  continuous_observationOfEuclidean.measurable

theorem continuous_datasetOfEuclidean {k m r : ℕ} :
    Continuous (datasetOfEuclidean :
      EuclideanSpace ℝ (DatasetCoordinate k m r) → Dataset (Observation k m) r) := by
  apply continuous_pi
  intro i
  apply Continuous.prodMk
  · exact continuous_pi fun j => PiLp.continuous_apply 2 (fun _ => ℝ) (i, Sum.inl j)
  · exact continuous_pi fun j => PiLp.continuous_apply 2 (fun _ => ℝ) (i, Sum.inr j)

theorem measurable_datasetOfEuclidean {k m r : ℕ} :
    Measurable (datasetOfEuclidean :
      EuclideanSpace ℝ (DatasetCoordinate k m r) → Dataset (Observation k m) r) :=
  continuous_datasetOfEuclidean.measurable

end LOOConcentration.Revision
