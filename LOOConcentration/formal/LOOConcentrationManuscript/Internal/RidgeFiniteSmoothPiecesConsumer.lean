import LOOConcentrationManuscript.Internal.RidgeFiniteSmoothPieces

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal
open scoped ContDiff

/-- The actual frozen predictor consumes the finite smooth pieces on a finite
closed cover of every paired dataset, including every clipping endpoint. -/
theorem stabilizedLinearEstimator_public_finite_closed_smooth_cover
    (b δ : {t : ℝ // 0 < t}) (r : ℕ) (x : ℝ) :
    (∀ mode : Fin (r + 1) → Fin 3,
      IsClosed (ridgeResponseChamber b.val r mode) ∧
      ContDiff ℝ ∞ (ridgePredictorSmoothPiece b δ r x mode) ∧
      Set.EqOn (fun E => (LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r
        (LOOConcentration.Revision.datasetOfEuclidean E) (fun _ => x)) 0)
        (ridgePredictorSmoothPiece b δ r x mode) (ridgeResponseChamber b.val r mode)) ∧
    (∀ E, ∃ mode : Fin (r + 1) → Fin 3, E ∈ ridgeResponseChamber b.val r mode) := by
  have h := stabilizedLinearEstimator_finite_smooth_pieces b δ r x
  refine ⟨?_, h.2⟩
  intro mode
  exact ⟨ridgeResponseChamber_isClosed b.val r mode, (h.1 mode).1, (h.1 mode).2⟩

end LOOConcentration.Manuscript.Internal
