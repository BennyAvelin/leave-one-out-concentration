import LOOConcentrationManuscript.Internal.RidgePredictorTrainingRegularityConsumer
import LOOConcentrationManuscript.Frozen.Bridges.ExpectedLossSegmentBound
import LOOConcentration.Geometry.SmoothLocalSlope
import LOOConcentration.Geometry.LocalSlopeFacts
import LOOConcentrationRevision.Geometry.CoordinateTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal
open Filter MeasureTheory
open scoped Topology

private theorem continuous_dataset_flatten {k m N : ℕ} :
    Continuous (LOOConcentration.datasetToEuclidean :
      LOOConcentration.Dataset (LOOConcentration.Observation k m) N →
        EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m N)) := by
  change Continuous (fun D : LOOConcentration.Dataset
      (LOOConcentration.Observation k m) N =>
    WithLp.toLp (2 : ENNReal) (fun q : LOOConcentration.DatasetCoordinate k m N =>
      Sum.elim (D q.1).1 (D q.1).2 q.2))
  exact (PiLp.continuous_toLp (p := (2 : ENNReal))
    (β := fun _ : LOOConcentration.DatasetCoordinate k m N => ℝ)).comp (by
    apply continuous_pi
    rintro ⟨i, j⟩
    cases j with
    | inl j => exact ((continuous_apply j).comp continuous_fst).comp (continuous_apply i)
    | inr j => exact ((continuous_apply j).comp continuous_snd).comp (continuous_apply i))

/-- Literal pullback of a locally Lipschitz Euclidean function to the frozen
unnormalized dataset carrier. -/
noncomputable def locallyLipschitzDatasetPullback {k m n : ℕ}
    (f : EuclideanSpace ℝ
      (LOOConcentration.DatasetCoordinate (k + 1) (m + 1) (n + 1)) → ℝ)
    (hLip : LocallyLipschitz f) : LOOConcentration.LocallyLipschitzDataFunction k m n := by
  let T : LOOConcentration.DataCarrier k m n → EuclideanSpace ℝ
      (LOOConcentration.DatasetCoordinate (k + 1) (m + 1) (n + 1)) :=
    LOOConcentration.datasetToEuclidean
  have hT : Continuous T := continuous_dataset_flatten
  refine ⟨fun D => f (T D), ?_⟩
  intro D
  obtain ⟨K, U, hU, hKU⟩ := hLip (T D)
  refine ⟨T ⁻¹' U, hT.continuousAt.preimage_mem_nhds hU, K, K.coe_nonneg, ?_⟩
  intro E hE G hG
  have hdist := hKU.dist_le_mul (T E) hE (T G) hG
  rw [Real.dist_eq, dist_eq_norm] at hdist
  simpa only [T, ← LOOConcentration.datasetToEuclidean_sub,
    ← LOOConcentration.datasetNorm_eq_euclidean] using hdist

/-- Integrating the ambient almost-everywhere gradient estimate over segments
and taking the endpoint limit gives the same bound for the frozen local slope
at every dataset. No absolute continuity of an observation law is needed. -/
theorem datasetLocalSlope_pullback_le_of_ae_gradient {k m n : ℕ}
    (f : EuclideanSpace ℝ
      (LOOConcentration.DatasetCoordinate (k + 1) (m + 1) (n + 1)) → ℝ)
    (hLip : LocallyLipschitz f) (c d : NNReal)
    (hGradient : ∀ᵐ E ∂(volume : Measure
      (EuclideanSpace ℝ
        (LOOConcentration.DatasetCoordinate (k + 1) (m + 1) (n + 1)))),
      ‖gradient f E‖ ≤ (c : ℝ) + (d : ℝ) * ‖E‖)
    (D : LOOConcentration.DataCarrier k m n) :
    LOOConcentration.datasetLocalSlope (locallyLipschitzDatasetPullback f hLip) D ≤
      (c : ℝ) + (d : ℝ) * LOOConcentration.datasetNorm D := by
  let g := locallyLipschitzDatasetPullback f hLip
  let F := 𝓝[≠] D
  let q := fun E : LOOConcentration.DataCarrier k m n =>
    |g.1 E - g.1 D| / LOOConcentration.datasetNorm (E - D)
  let upper := fun E : LOOConcentration.DataCarrier k m n =>
    (c : ℝ) + (d : ℝ) / 2 *
      (LOOConcentration.datasetNorm E + LOOConcentration.datasetNorm D)
  have hpoint : ∀ᶠ E in F, q E ≤ upper E := by
    filter_upwards [self_mem_nhdsWithin] with E hE
    have hne : E ≠ D := by simpa using hE
    have hpos := LOOConcentration.datasetNorm_sub_pos hne
    have hsegment := LOOConcentration.Manuscript.expected_loss_segment_bound
      f hLip c d hGradient (LOOConcentration.datasetToEuclidean E)
        (LOOConcentration.datasetToEuclidean D)
    rw [← LOOConcentration.datasetToEuclidean_sub,
      ← LOOConcentration.datasetNorm_eq_euclidean,
      ← LOOConcentration.datasetNorm_eq_euclidean,
      ← LOOConcentration.datasetNorm_eq_euclidean] at hsegment
    exact (div_le_iff₀ hpos).2 (by
      simpa only [q, upper, g, locallyLipschitzDatasetPullback, mul_comm] using hsegment)
  have hNorm : Continuous (fun E : LOOConcentration.DataCarrier k m n =>
      LOOConcentration.datasetNorm E) := by
    simpa only [LOOConcentration.datasetNorm_eq_euclidean] using
      continuous_dataset_flatten.norm
  have hUpper : Continuous upper := by
    exact continuous_const.add (continuous_const.mul (hNorm.add continuous_const))
  have hTendsto : Tendsto upper F
      (𝓝 ((c : ℝ) + (d : ℝ) * LOOConcentration.datasetNorm D)) := by
    have h : Tendsto upper F (𝓝 (upper D)) :=
      hUpper.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have heq : upper D = (c : ℝ) + (d : ℝ) * LOOConcentration.datasetNorm D := by
      dsimp [upper]
      ring
    rw [heq] at h
    exact h
  have hlim := limsup_le_limsup hpoint
    (LOOConcentration.datasetSlope_cobounded g D) hTendsto.isBoundedUnder_le
  rw [hTendsto.limsup_eq] at hlim
  exact hlim

/-- The literal Ridge predictor and its absolute fitted loss have the same
parameter-only local-slope bound, including clipping kinks and every endpoint. -/
theorem stabilizedLinearEstimator_actual_endpoint_local_slopes
    (b δ : {t : ℝ // 0 < t}) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℕ) (z : LOOConcentration.Observation 1 1),
      ∃ P L : LOOConcentration.LocallyLipschitzDataFunction 0 0 r,
        (∀ D, P.1 D = LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r
          D (fun _ : Fin 1 => z.1 0) 0) ∧
        (∀ D, L.1 D = LOOConcentration.fittedLoss
          (LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r)
          (fun u v : Fin 1 → ℝ => |u 0 - v 0|) D z) ∧
        (∀ D, LOOConcentration.datasetLocalSlope P D ≤
          C * (1 + |z.1 0|) / Real.sqrt ((r + 1 : ℕ) : ℝ) +
            C * LOOConcentration.datasetNorm D / ((r + 1 : ℕ) : ℝ)) ∧
        (∀ D, LOOConcentration.datasetLocalSlope L D ≤
          C * (1 + |z.1 0|) / Real.sqrt ((r + 1 : ℕ) : ℝ) +
            C * LOOConcentration.datasetNorm D / ((r + 1 : ℕ) : ℝ)) := by
  obtain ⟨C, hC, hJoint⟩ :=
    stabilizedLinearEstimator_actual_predictor_training_gradient_regular_consumer b δ
  refine ⟨C, hC, ?_⟩
  intro r z
  obtain ⟨hP, hL, hGrad⟩ := hJoint r z
  let c : NNReal := ⟨C * (1 + |z.1 0|) / Real.sqrt ((r + 1 : ℕ) : ℝ), by positivity⟩
  let d : NNReal := ⟨C / ((r + 1 : ℕ) : ℝ), by positivity⟩
  let P := locallyLipschitzDatasetPullback
    (stabilizedLinearEstimatorActualTrainingPredictor b δ r (z.1 0)) hP
  let L := locallyLipschitzDatasetPullback (stabilizedLinearEstimatorActualTrainingLoss b δ r z) hL
  have hGP : ∀ᵐ E ∂volume,
      ‖gradient (stabilizedLinearEstimatorActualTrainingPredictor b δ r (z.1 0)) E‖ ≤
        (c : ℝ) + (d : ℝ) * ‖E‖ := by
    filter_upwards [hGrad] with E hE
    change _ ≤ C * (1 + |z.1 0|) / Real.sqrt ((r + 1 : ℕ) : ℝ) +
      (C / ((r + 1 : ℕ) : ℝ)) * ‖E‖
    simpa only [div_mul_eq_mul_div] using hE.2.2.1
  have hGL : ∀ᵐ E ∂volume,
      ‖gradient (stabilizedLinearEstimatorActualTrainingLoss b δ r z) E‖ ≤
        (c : ℝ) + (d : ℝ) * ‖E‖ := by
    filter_upwards [hGrad] with E hE
    change _ ≤ C * (1 + |z.1 0|) / Real.sqrt ((r + 1 : ℕ) : ℝ) +
      (C / ((r + 1 : ℕ) : ℝ)) * ‖E‖
    simpa only [div_mul_eq_mul_div] using hE.2.2.2
  refine ⟨P, L, ?_, ?_, ?_, ?_⟩
  · intro D
    simp only [P, locallyLipschitzDatasetPullback,
      stabilizedLinearEstimatorActualTrainingPredictor,
      LOOConcentration.Revision.datasetOfEuclidean_datasetToEuclidean]
  · intro D
    simp only [L, locallyLipschitzDatasetPullback,
      stabilizedLinearEstimatorActualTrainingLoss,
      LOOConcentration.Revision.datasetOfEuclidean_datasetToEuclidean]
  · intro D
    have hb := datasetLocalSlope_pullback_le_of_ae_gradient _ hP c d hGP D
    change LOOConcentration.datasetLocalSlope P D ≤
      C * (1 + |z.1 0|) / Real.sqrt ((r + 1 : ℕ) : ℝ) +
        (C / ((r + 1 : ℕ) : ℝ)) * LOOConcentration.datasetNorm D at hb
    simpa only [div_mul_eq_mul_div] using hb
  · intro D
    have hb := datasetLocalSlope_pullback_le_of_ae_gradient _ hL c d hGL D
    change LOOConcentration.datasetLocalSlope L D ≤
      C * (1 + |z.1 0|) / Real.sqrt ((r + 1 : ℕ) : ℝ) +
        (C / ((r + 1 : ℕ) : ℝ)) * LOOConcentration.datasetNorm D at hb
    simpa only [div_mul_eq_mul_div] using hb

end LOOConcentration.Manuscript.Internal
