import LOOConcentrationManuscript.Internal.RidgeUniformSlopeLipschitz
import LOOConcentration.Concentration.SegmentEstimate
import LOOConcentration.Frozen.Slopes.DatasetLocalSlope
import LOOConcentration.Geometry.LocalSlopeFacts
import LOOConcentration.Geometry.NormTransport
import LOOConcentrationManuscript.Frozen.Definitions.StabilizedLinearEstimator
import LOOConcentrationRevision.Frozen.Definitions.DatasetOfEuclidean

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

/-! A source-facing consumer on the actual frozen Ridge estimator and dataset carrier. -/

namespace LOOConcentration.Manuscript.Internal
open Filter

private theorem ridgeBeta_dataset_map_sub (r : ℕ)
    (D E : LOOConcentration.DataCarrier 0 0 r) :
    LOOConcentration.datasetToEuclidean (D - E) =
      LOOConcentration.datasetToEuclidean D - LOOConcentration.datasetToEuclidean E := by
  apply PiLp.ext
  intro q
  rcases q with ⟨i, c⟩
  cases c <;> simp [LOOConcentration.datasetToEuclidean]

private theorem ridgeBeta_actual_frozen_dataset_pair_bound
    (b δ : {t : ℝ // 0 < t}) (r : ℕ) (rate : ℝ) (K : NNReal)
    (hK : (K : ℝ) = rate)
    (hLip : LipschitzWith K (stabilizedLinearEstimatorActualTrainingBeta b δ r))
    (D E : LOOConcentration.DataCarrier 0 0 r) :
    |stabilizedLinearEstimatorActualTrainingBeta b δ r
        (LOOConcentration.datasetToEuclidean D) -
      stabilizedLinearEstimatorActualTrainingBeta b δ r
        (LOOConcentration.datasetToEuclidean E)| ≤
      rate * LOOConcentration.datasetNorm (D - E) := by
  have hDist :
      dist (LOOConcentration.datasetToEuclidean D)
          (LOOConcentration.datasetToEuclidean E) =
        LOOConcentration.datasetNorm (D - E) := by
    calc
      _ = ‖LOOConcentration.datasetToEuclidean D -
          LOOConcentration.datasetToEuclidean E‖ := by rw [dist_eq_norm]
      _ = ‖LOOConcentration.datasetToEuclidean (D - E)‖ := by
        rw [← ridgeBeta_dataset_map_sub]
      _ = LOOConcentration.datasetNorm (D - E) :=
        (LOOConcentration.datasetNorm_eq_euclidean (D - E)).symm
  calc
    _ = dist
        (stabilizedLinearEstimatorActualTrainingBeta b δ r
          (LOOConcentration.datasetToEuclidean D))
        (stabilizedLinearEstimatorActualTrainingBeta b δ r
          (LOOConcentration.datasetToEuclidean E)) := by rw [Real.dist_eq]
    _ ≤ (K : ℝ) * dist (LOOConcentration.datasetToEuclidean D)
        (LOOConcentration.datasetToEuclidean E) := hLip.dist_le_mul _ _
    _ = rate * LOOConcentration.datasetNorm (D - E) := by rw [hK, hDist]

/-- Consume the public beta theorem on the actual frozen Ridge estimator. The
resulting local-slope witness is on the frozen full paired-data carrier, and
the slope bound holds at every dataset, including clipping kinks. -/
theorem stabilizedLinearEstimator_actual_beta_frozen_dataset_local_slope_consumer
    (b δ : {t : ℝ // 0 < t}) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ,
      ∃ f : LOOConcentration.LocallyLipschitzDataFunction 0 0 r,
        (∀ D : LOOConcentration.DataCarrier 0 0 r,
          f.1 D =
            LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r D
                (fun _ : Fin 1 => 1) 0 -
              LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r D
                (fun _ : Fin 1 => 0) 0) ∧
        ∀ D : LOOConcentration.DataCarrier 0 0 r,
          LOOConcentration.datasetLocalSlope f D ≤
            C / Real.sqrt ((r + 1 : ℕ) : ℝ) := by
  obtain ⟨C, hC, hPrimary⟩ :=
    stabilizedLinearEstimator_actual_beta_uniform_lipschitz_gradient b δ
  refine ⟨C, hC, ?_⟩
  intro r
  let rate : ℝ := C / Real.sqrt ((r + 1 : ℕ) : ℝ)
  let K : NNReal := Real.toNNReal rate
  have hN : 0 < ((r + 1 : ℕ) : ℝ) := by positivity
  have hrate : 0 ≤ rate := div_nonneg hC.le (Real.sqrt_nonneg _)
  rcases hPrimary r with ⟨hLip, hK, _hLoc, _hGrad⟩
  let beta := stabilizedLinearEstimatorActualTrainingBeta b δ r
  let frozenBeta : LOOConcentration.DataCarrier 0 0 r → ℝ := fun D =>
    LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r D
        (fun _ : Fin 1 => 1) 0 -
      LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r D
        (fun _ : Fin 1 => 0) 0
  have hDatasetRoundTrip (D : LOOConcentration.DataCarrier 0 0 r) :
      LOOConcentration.Revision.datasetOfEuclidean
          (LOOConcentration.datasetToEuclidean D) = D := by
    funext i
    apply Prod.ext
    · funext j
      simp [LOOConcentration.datasetToEuclidean,
        LOOConcentration.Revision.datasetOfEuclidean]
    · funext j
      simp [LOOConcentration.datasetToEuclidean,
        LOOConcentration.Revision.datasetOfEuclidean]
  have hFrozenBeta (D : LOOConcentration.DataCarrier 0 0 r) :
      frozenBeta D = beta (LOOConcentration.datasetToEuclidean D) := by
    dsimp [frozenBeta, beta, stabilizedLinearEstimatorActualTrainingBeta,
      stabilizedLinearEstimatorActualTrainingPredictor]
    rw [hDatasetRoundTrip D]
  have hPair (D E : LOOConcentration.DataCarrier 0 0 r) :
      |frozenBeta D - frozenBeta E| ≤
        rate * LOOConcentration.datasetNorm (D - E) := by
    rw [hFrozenBeta D, hFrozenBeta E]
    exact ridgeBeta_actual_frozen_dataset_pair_bound b δ r rate K hK hLip D E
  let f : LOOConcentration.LocallyLipschitzDataFunction 0 0 r := ⟨
    frozenBeta, by
      intro D
      refine ⟨Set.univ, Filter.univ_mem, rate, hrate, ?_⟩
      intro E hE F hF
      exact hPair E F⟩
  refine ⟨f, ?_, ?_⟩
  · intro D
    change frozenBeta D = _
    exact hFrozenBeta D
  · intro D
    rw [LOOConcentration.datasetLocalSlope]
    apply Filter.limsup_le_of_le (LOOConcentration.datasetSlope_cobounded f D)
    filter_upwards [self_mem_nhdsWithin] with E hE
    have hne : E ≠ D := by change E ≠ D at hE; exact hE
    exact (div_le_iff₀ (LOOConcentration.datasetNorm_sub_pos hne)).2 (hPair E D)

end LOOConcentration.Manuscript.Internal
