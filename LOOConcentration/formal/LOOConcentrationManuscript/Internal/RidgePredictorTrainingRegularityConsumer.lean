import LOOConcentrationManuscript.Internal.RidgePredictorTrainingRegularity
import LOOConcentrationManuscript.Internal.RidgeTrainingRegularityConsumer

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal
open MeasureTheory

/-- The actual predictor and absolute fitted loss share one parameter-only
training-gradient constant before every sample size and query. -/
theorem stabilizedLinearEstimator_actual_predictor_training_gradient_regular_consumer
    (b δ : {t : ℝ // 0 < t}) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℕ) (z : LOOConcentration.Observation 1 1),
      let P := stabilizedLinearEstimatorActualTrainingPredictor b δ r (z.1 0)
      let L := stabilizedLinearEstimatorActualTrainingLoss b δ r z
      LocallyLipschitz P ∧ LocallyLipschitz L ∧
        ∀ᵐ E ∂(volume : Measure
          (EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1)))),
          DifferentiableAt ℝ P E ∧ DifferentiableAt ℝ L E ∧
            ‖gradient P E‖ ≤
              C * (1 + |z.1 0|) / Real.sqrt ((r + 1 : ℕ) : ℝ) +
                C * ‖E‖ / ((r + 1 : ℕ) : ℝ) ∧
            ‖gradient L E‖ ≤
              C * (1 + |z.1 0|) / Real.sqrt ((r + 1 : ℕ) : ℝ) +
                C * ‖E‖ / ((r + 1 : ℕ) : ℝ) := by
  obtain ⟨CP, hCP, hP⟩ :=
    stabilizedLinearEstimator_actual_predictor_training_gradient_regular b δ
  obtain ⟨CL, hCL, hL⟩ :=
    stabilizedLinearEstimator_actual_training_gradient_regular_consumer b δ
  refine ⟨max CP CL, lt_of_lt_of_le hCP (le_max_left _ _), ?_⟩
  intro r z
  obtain ⟨hPLoc, hPGrad⟩ := hP r (z.1 0)
  obtain ⟨hLLoc, hLGrad⟩ := hL r z
  refine ⟨hPLoc, hLLoc, ?_⟩
  filter_upwards [hPGrad, hLGrad] with E hPE hLE
  refine ⟨hPE.1, hLE.1, ?_, ?_⟩
  · exact hPE.2.trans (add_le_add
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left CP CL) (by positivity))
        (Real.sqrt_nonneg _))
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left CP CL) (norm_nonneg E))
        (by positivity)))
  · exact hLE.2.trans (add_le_add
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right CP CL) (by positivity))
        (Real.sqrt_nonneg _))
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right CP CL) (norm_nonneg E))
        (by positivity)))

end LOOConcentration.Manuscript.Internal
