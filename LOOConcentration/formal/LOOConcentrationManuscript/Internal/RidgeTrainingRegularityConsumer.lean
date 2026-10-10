import LOOConcentrationManuscript.Internal.RidgeTrainingRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

/-!
The public training-regularity consumer used for every sample size and every
test observation.  Its loss is the literal fitted loss of the frozen public
stabilized ridge estimator on `datasetOfEuclidean`.
-/

namespace LOOConcentration.Manuscript.Internal
open MeasureTheory

/-- Consume the source-level ridge training-gradient producer uniformly in
the sample size and query.  The same parameter-only constant is returned for
the actual public fitted loss on the unrestricted paired Euclidean carrier. -/
theorem stabilizedLinearEstimator_actual_training_gradient_regular_consumer
    (b δ : {t : ℝ // 0 < t}) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℕ) (z : LOOConcentration.Observation 1 1),
      let actualLoss := stabilizedLinearEstimatorActualTrainingLoss b δ r z
      LocallyLipschitz actualLoss ∧
        ∀ᵐ E ∂(volume : Measure
          (EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1)))),
          DifferentiableAt ℝ actualLoss E ∧
            ‖gradient actualLoss E‖ ≤
              C * (1 + |z.1 0|) / Real.sqrt ((r + 1 : ℕ) : ℝ) +
                C * ‖E‖ / ((r + 1 : ℕ) : ℝ) := by
  obtain ⟨C, hC, hregular⟩ :=
    stabilizedLinearEstimator_actual_training_gradient_regular b δ
  refine ⟨C, hC, ?_⟩
  intro r z
  exact hregular r z

end LOOConcentration.Manuscript.Internal
