import LOOConcentrationManuscript.Internal.AmbientMeanLossRegularity
import LOOConcentrationRevision.Geometry.CoordinateTransport
import LOOConcentrationRevision.Frozen.Definitions.DatasetOfEuclidean
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

open scoped Topology ContDiff
open LOOConcentration.Revision

namespace LOOConcentration.Manuscript

/-- The response-only embedding in the actual full observation coordinate
space: response entries are retained and feature entries are zero. -/
private def scalarResponseEmbedding (r : ℕ)
    (Y : EuclideanSpace ℝ (Fin (r + 1))) :
    EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate 1 1 (r + 1)) :=
  WithLp.toLp 2 (fun q =>
    Sum.elim (fun _ : Fin 1 => 0) (fun _ : Fin 1 => Y q.1) q.2)

private theorem scalarResponseEmbedding_coordinates (r : ℕ)
    (Y : EuclideanSpace ℝ (Fin (r + 1))) (i : Fin (r + 1)) :
    scalarResponseEmbedding r Y (i, Sum.inl 0) = 0 ∧
      scalarResponseEmbedding r Y (i, Sum.inr 0) = Y i := by
  constructor <;> rfl

/-- The actual Euclidean dataset carrier stores arbitrary feature and response
coordinates. Its response-column quadratic mean loss satisfies the ambient
regularity result at every point. -/
theorem empiricalMean_quadraticLoss_actualDataset_ambient_regular
    (r : ℕ) (z : ℝ)
    (E : EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate 1 1 (r + 1))) :
    ContDiff ℝ ∞ (fun X : EuclideanSpace ℝ
      (LOOConcentration.DatasetCoordinate 1 1 (r + 1)) =>
        (empiricalMean r (WithLp.toLp 2
          (fun i => (datasetOfEuclidean X i).2 0)) - z) ^ 2) ∧
      ‖gradient (fun X : EuclideanSpace ℝ
        (LOOConcentration.DatasetCoordinate 1 1 (r + 1)) =>
          (empiricalMean r (WithLp.toLp 2
            (fun i => (datasetOfEuclidean X i).2 0)) - z) ^ 2) E‖ ≤
        2 * |z| / Real.sqrt ((r + 1 : ℕ) : ℝ) +
          (2 / ((r + 1 : ℕ) : ℝ)) * ‖E‖ := by
  simpa only [datasetOfEuclidean] using
    (empiricalMean_quadraticLoss_ambient_regular r z E)

/-- The same ambient result specializes to the source's response-only
embedding, whose feature column is zero. -/
theorem empiricalMean_quadraticLoss_embeddedResponse_ambient_regular
    (r : ℕ) (z : ℝ) (Y : EuclideanSpace ℝ (Fin (r + 1))) :
    ContDiff ℝ ∞ (fun X : EuclideanSpace ℝ
      (LOOConcentration.DatasetCoordinate 1 1 (r + 1)) =>
        (empiricalMean r (WithLp.toLp 2
          (fun i => (datasetOfEuclidean X i).2 0)) - z) ^ 2) ∧
      ‖gradient (fun X : EuclideanSpace ℝ
        (LOOConcentration.DatasetCoordinate 1 1 (r + 1)) =>
          (empiricalMean r (WithLp.toLp 2
            (fun i => (datasetOfEuclidean X i).2 0)) - z) ^ 2)
        (scalarResponseEmbedding r Y)‖ ≤
        2 * |z| / Real.sqrt ((r + 1 : ℕ) : ℝ) +
          (2 / ((r + 1 : ℕ) : ℝ)) * ‖scalarResponseEmbedding r Y‖ := by
  exact empiricalMean_quadraticLoss_actualDataset_ambient_regular r z
    (scalarResponseEmbedding r Y)

end LOOConcentration.Manuscript
