import LOOConcentrationManuscript.Internal.RidgeGroupedSlopeGradients

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

/-!
Downstream source consumer for the grouped ridge-slope gradient estimates.
The slope function is the literal public stabilized estimator prediction
at query one minus its prediction at query zero.
-/

namespace LOOConcentration.Manuscript.Internal

/-- Grouped gradient bounds for the actual query-difference slope of the
public stabilized estimator, on its full paired Euclidean training carrier. -/
theorem stabilizedLinearEstimator_actual_source_grouped_gradient_bounds
    (r : ℕ) (b δ : {t : ℝ // 0 < t})
    (E : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1)))
    (hclips : ∀ j : Fin (r + 1), ∃ γ : ℝ,
      HasDerivAt (fun y : ℝ => max (min y b.val) (-b.val)) γ
        ((LOOConcentration.Revision.datasetOfEuclidean E j).2 0)) :
    let D := LOOConcentration.Revision.datasetOfEuclidean E
    let N : ℝ := ((r + 1 : ℕ) : ℝ)
    let X := LOOConcentrationManuscript.featureValues D
    let U := LOOConcentrationManuscript.clippedResponseValues D b.val
    let a : ℝ := (∑ i : Fin (r + 1), X i) * N⁻¹
    let c : ℝ := (∑ i : Fin (r + 1), U i) * N⁻¹
    let v : ℝ := (∑ i : Fin (r + 1), (X i - a) ^ 2) * N⁻¹
    let s : ℝ := (∑ i : Fin (r + 1), (X i - a) * (U i - c)) * N⁻¹
    let β : ℝ := s / (v + δ.val)
    ‖WithLp.toLp 2 (fun j : Fin (r + 1) =>
        gradient (stabilizedLinearEstimator_actualSlope b δ r) E (j, Sum.inr 0))‖ ≤
      Real.sqrt v / (Real.sqrt N * (v + δ.val)) ∧
    ‖WithLp.toLp 2 (fun j : Fin (r + 1) =>
        gradient (stabilizedLinearEstimator_actualSlope b δ r) E (j, Sum.inl 0))‖ ≤
      (b.val + 2 * |β| * Real.sqrt v) /
        (Real.sqrt N * (v + δ.val)) := by
  exact stabilizedLinearEstimator_actual_grouped_gradient_bounds r b δ E hclips

end LOOConcentration.Manuscript.Internal
