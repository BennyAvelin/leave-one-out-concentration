import LOOConcentrationManuscript.Internal.RidgeUniformSlopeLipschitzConsumer
import LOOConcentrationManuscript.Internal.RidgeEndpointLocalSlopes
import LOOConcentrationManuscript.Internal.RidgeFiniteSmoothPiecesConsumer

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal
open MeasureTheory
open scoped ContDiff

private theorem ridgeSourceGrowth_mono (r : ℕ) (x R C₀ C : ℝ)
    (hR : 0 ≤ R) (hC : C₀ ≤ C) :
    C₀ * (1 + |x|) / Real.sqrt ((r + 1 : ℕ) : ℝ) +
        C₀ * R / ((r + 1 : ℕ) : ℝ) ≤
      C * (1 + |x|) / Real.sqrt ((r + 1 : ℕ) : ℝ) + C * R / ((r + 1 : ℕ) : ℝ) := by
  exact add_le_add
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC (by positivity))
      (Real.sqrt_nonneg _))
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC hR) (by positivity))

/-- One source constant is fixed before every size and query, and controls
both the actual gradients and the frozen endpoint local slopes. The literal
predictor and beta also consume the finite closed smooth cover. -/
theorem stabilizedLinearEstimator_actual_source_joint_regularity
    (b δ : {t : ℝ // 0 < t}) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℕ) (z : LOOConcentration.Observation 1 1),
      let β := stabilizedLinearEstimatorActualTrainingBeta b δ r
      let P := stabilizedLinearEstimatorActualTrainingPredictor b δ r (z.1 0)
      let L := stabilizedLinearEstimatorActualTrainingLoss b δ r z
      LocallyLipschitz β ∧ LocallyLipschitz P ∧ LocallyLipschitz L ∧
      (∀ᵐ E ∂(volume : Measure
        (EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1)))),
        DifferentiableAt ℝ β E ∧ DifferentiableAt ℝ P E ∧ DifferentiableAt ℝ L E ∧
        ‖gradient β E‖ ≤ C / Real.sqrt ((r + 1 : ℕ) : ℝ) ∧
        ‖gradient P E‖ ≤ C * (1 + |z.1 0|) / Real.sqrt ((r + 1 : ℕ) : ℝ) +
          C * ‖E‖ / ((r + 1 : ℕ) : ℝ) ∧
        ‖gradient L E‖ ≤ C * (1 + |z.1 0|) / Real.sqrt ((r + 1 : ℕ) : ℝ) +
          C * ‖E‖ / ((r + 1 : ℕ) : ℝ)) ∧
      (∃ B P' L' : LOOConcentration.LocallyLipschitzDataFunction 0 0 r,
        (∀ D, B.1 D = LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r D
          (fun _ : Fin 1 => 1) 0 - LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r D
          (fun _ : Fin 1 => 0) 0) ∧
        (∀ D, P'.1 D = LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r D
          (fun _ : Fin 1 => z.1 0) 0) ∧
        (∀ D, L'.1 D = LOOConcentration.fittedLoss
          (LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r)
          (fun u v : Fin 1 → ℝ => |u 0 - v 0|) D z) ∧
        (∀ D, LOOConcentration.datasetLocalSlope B D ≤ C / Real.sqrt ((r + 1 : ℕ) : ℝ) ∧
          LOOConcentration.datasetLocalSlope P' D ≤
            C * (1 + |z.1 0|) / Real.sqrt ((r + 1 : ℕ) : ℝ) +
              C * LOOConcentration.datasetNorm D / ((r + 1 : ℕ) : ℝ) ∧
          LOOConcentration.datasetLocalSlope L' D ≤
            C * (1 + |z.1 0|) / Real.sqrt ((r + 1 : ℕ) : ℝ) +
              C * LOOConcentration.datasetNorm D / ((r + 1 : ℕ) : ℝ))) ∧
      (∀ mode : Fin (r + 1) → Fin 3,
        IsClosed (ridgeResponseChamber b.val r mode) ∧
        ContDiff ℝ ∞ (ridgePredictorSmoothPiece b δ r (z.1 0) mode) ∧
        Set.EqOn P (ridgePredictorSmoothPiece b δ r (z.1 0) mode)
          (ridgeResponseChamber b.val r mode) ∧
        ContDiff ℝ ∞ (fun E => ridgePredictorSmoothPiece b δ r 1 mode E -
          ridgePredictorSmoothPiece b δ r 0 mode E) ∧
        Set.EqOn β (fun E => ridgePredictorSmoothPiece b δ r 1 mode E -
          ridgePredictorSmoothPiece b δ r 0 mode E) (ridgeResponseChamber b.val r mode)) ∧
      (∀ E, ∃ mode : Fin (r + 1) → Fin 3, E ∈ ridgeResponseChamber b.val r mode) := by
  obtain ⟨Cβ, hCβ, hβ⟩ := stabilizedLinearEstimator_actual_beta_uniform_lipschitz_gradient b δ
  obtain ⟨CB, hCB, hB⟩ := stabilizedLinearEstimator_actual_beta_frozen_dataset_local_slope_consumer b δ
  obtain ⟨CG, hCG, hG⟩ := stabilizedLinearEstimator_actual_predictor_training_gradient_regular_consumer b δ
  obtain ⟨CE, hCE, hEndpoint⟩ := stabilizedLinearEstimator_actual_endpoint_local_slopes b δ
  let C := Cβ + CB + CG + CE
  have hC : 0 < C := by dsimp [C]; linarith
  have hβC : Cβ ≤ C := by dsimp [C]; linarith
  have hBC : CB ≤ C := by dsimp [C]; linarith
  have hGC : CG ≤ C := by dsimp [C]; linarith
  have hEC : CE ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro r z
  obtain ⟨_hLipβ, _hKβ, hLocβ, hGradβ⟩ := hβ r
  obtain ⟨hLocP, hLocL, hGrad⟩ := hG r z
  refine ⟨hLocβ, hLocP, hLocL, ?_, ?_, ?_, ridgeResponseChambers_cover b.val r⟩
  · filter_upwards [hGradβ, hGrad] with E hβE hE
    refine ⟨hβE.1, hE.1, hE.2.1, ?_, ?_, ?_⟩
    · exact hβE.2.trans (div_le_div_of_nonneg_right hβC (Real.sqrt_nonneg _))
    · exact hE.2.2.1.trans (ridgeSourceGrowth_mono r (z.1 0) ‖E‖ CG C (norm_nonneg _) hGC)
    · exact hE.2.2.2.trans (ridgeSourceGrowth_mono r (z.1 0) ‖E‖ CG C (norm_nonneg _) hGC)
  · obtain ⟨B, hBId, hBSlope⟩ := hB r
    obtain ⟨P', L', hPId, hLId, hPSlope, hLSlope⟩ := hEndpoint r z
    refine ⟨B, P', L', hBId, hPId, hLId, ?_⟩
    intro D
    refine ⟨(hBSlope D).trans (div_le_div_of_nonneg_right hBC (Real.sqrt_nonneg _)), ?_, ?_⟩
    · exact (hPSlope D).trans (ridgeSourceGrowth_mono r (z.1 0)
        (LOOConcentration.datasetNorm D) CE C (by rw [LOOConcentration.datasetNorm_eq_euclidean]; exact norm_nonneg _) hEC)
    · exact (hLSlope D).trans (ridgeSourceGrowth_mono r (z.1 0)
        (LOOConcentration.datasetNorm D) CE C (by rw [LOOConcentration.datasetNorm_eq_euclidean]; exact norm_nonneg _) hEC)
  · intro mode
    have hP := (stabilizedLinearEstimator_finite_smooth_pieces b δ r (z.1 0)).1 mode
    have hβPiece := stabilizedLinearEstimator_slope_finite_smooth_pieces b δ r mode
    exact ⟨ridgeResponseChamber_isClosed b.val r mode, hP.1, hP.2, hβPiece.1, hβPiece.2⟩

end LOOConcentration.Manuscript.Internal
