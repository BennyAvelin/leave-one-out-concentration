import LOOConcentrationManuscript.Internal.EuclideanClipping
import LOOConcentrationRevision.Frozen.Definitions.DatasetOfEuclidean

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal

/-- Clipping every source feature and response coordinate gives exactly the
dataset bound used in the manuscript's truncation-sensitivity proof. -/
theorem datasetClipping_lipschitz_and_exact_dimension_bound
    (k m r : ℕ) (b : ℝ) (hb : 0 ≤ b) :
    let clip := fun D : EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (r + 1)) =>
      WithLp.toLp 2 (fun i => max (min (D i) b) (-b))
    LipschitzWith 1 clip ∧
    ∀ D : EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (r + 1)),
      ‖clip D‖ ≤ b * Real.sqrt (((k + m) * (r + 1) : ℕ) : ℝ) := by
  simpa only [LOOConcentration.DatasetCoordinate, LOOConcentration.ObservationCoordinate,
    Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, Nat.mul_comm] using
    euclideanClipping_lipschitz_and_norm
      (LOOConcentration.DatasetCoordinate k m (r + 1)) b hb

end LOOConcentration.Manuscript.Internal
