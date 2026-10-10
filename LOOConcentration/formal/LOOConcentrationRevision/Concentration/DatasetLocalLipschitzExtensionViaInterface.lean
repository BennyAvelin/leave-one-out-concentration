import LOOConcentrationRevision.Concentration.HerbstFromFiniteLsiInterface
import LOOConcentrationRevision.Probability.ConditionalMeanShift
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory

/-- One event-local extension consumes the source finite-LSI interface, which
internally produces its raw moment and MGF at the same observation constant. -/
theorem dataset_local_lipschitz_extension_mgf_via_finite_lsi_interface
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (hfinite : observationLogSobolevConstant μ < ⊤)
    (H : Dataset (Observation k m) (n + 2) → ℝ)
    (K : Set (Dataset (Observation k m) (n + 2))) (hK : MeasurableSet K)
    (hq : 0 < (Measure.pi fun _ : Fin (n + 2) => μ).real K)
    (L : NNReal)
    (hLip : ∀ D ∈ K, ∀ E ∈ K, |H D - H E| ≤ (L : ℝ) * datasetNorm (D - E)) :
    let P := Measure.pi fun _ : Fin (n + 2) => μ
    let ν := normalizedRestriction P K
    ∃ G : EuclideanSpace ℝ (DatasetCoordinate k m (n + 2)) → ℝ,
      LipschitzWith L G ∧
      (∀ D ∈ K, G (datasetToEuclidean D) = H D) ∧
      Integrable (fun D => G (datasetToEuclidean D)) P ∧
      Integrable H ν ∧
      ProbabilityTheory.HasSubgaussianMGF
        (fun D => G (datasetToEuclidean D) - ∫ E, G (datasetToEuclidean E) ∂P)
        (NNReal.mk ((observationLogSobolevConstant μ).toReal * (L : ℝ)^2)
          (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))) P ∧
      ((fun D => H D - ∫ E, H E ∂ν) =ᵐ[ν]
        (fun D => G (datasetToEuclidean D) - ∫ E, G (datasetToEuclidean E) ∂ν)) := by
  let P := Measure.pi fun _ : Fin (n + 2) => μ
  let ν := normalizedRestriction P K
  let F : EuclideanSpace ℝ (DatasetCoordinate k m (n + 2)) → ℝ :=
    fun x => H (datasetOfEuclidean x)
  let A : Set (EuclideanSpace ℝ (DatasetCoordinate k m (n + 2))) :=
    datasetOfEuclidean ⁻¹' K
  have hFA : LipschitzOnWith L F A := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have h := hLip (datasetOfEuclidean x) hx (datasetOfEuclidean y) hy
    have hn : datasetNorm (datasetOfEuclidean x - datasetOfEuclidean y) = ‖x-y‖ := by
      rw [← datasetNorm_datasetOfEuclidean (x-y)]
      rfl
    simpa only [F, Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, hn] using h
  obtain ⟨G, hG, hEq⟩ := hFA.extend_real
  have hEqRaw : ∀ D ∈ K, G (datasetToEuclidean D) = H D := by
    intro D hD
    have hD' : datasetToEuclidean D ∈ A := by
      simpa only [A, Set.mem_preimage, datasetOfEuclidean_datasetToEuclidean] using hD
    simpa only [F, datasetOfEuclidean_datasetToEuclidean] using (hEq hD').symm
  have hM2 := integrable_observationNormSq_of_finite_lsi μ hfinite
  have hSG := dataset_lipschitz_hasSubgaussianMGF_via_finite_lsi_interface μ hfinite G L hG
  let Q := datasetLawOfObservation (r := n + 2) μ
  let : IsProbabilityMeasure Q := datasetLawOfObservation_isProbabilityMeasure μ
  have hGInt : Integrable G Q := integrable_lipschitz_of_norm_sq Q
    (integrable_datasetLaw_norm_sq μ hM2) G L hG
  have hRawInt : Integrable (fun D => G (datasetToEuclidean D)) P :=
    (integrable_map_measure hG.continuous.aestronglyMeasurable
      measurable_datasetToEuclidean.aemeasurable).1 hGInt
  have hMean : (∫ x, G x ∂Q) = ∫ D, G (datasetToEuclidean D) ∂P :=
    integral_map measurable_datasetToEuclidean.aemeasurable hG.continuous.aestronglyMeasurable
  have hRawSG := ProbabilityTheory.HasSubgaussianMGF.of_map
    measurable_datasetToEuclidean.aemeasurable hSG
  have hSG' : ProbabilityTheory.HasSubgaussianMGF
      (fun D => G (datasetToEuclidean D) - ∫ E, G (datasetToEuclidean E) ∂P)
      (NNReal.mk ((observationLogSobolevConstant μ).toReal * (L : ℝ)^2)
        (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))) P := by
    change ProbabilityTheory.HasSubgaussianMGF
      (fun D => G (datasetToEuclidean D) - ∫ x, G x ∂Q) _ P at hRawSG
    rw [hMean] at hRawSG
    exact hRawSG
  have hK0 : P K ≠ 0 := by
    intro hzero
    have hz : P.real K = 0 := by simp [Measure.real, hzero]
    exact (ne_of_gt hq) hz
  have hGν : Integrable (fun D => G (datasetToEuclidean D)) ν :=
    hRawInt.restrict.smul_measure (ENNReal.inv_ne_top.mpr hK0)
  have hEqν : H =ᵐ[ν] fun D => G (datasetToEuclidean D) := by
    apply Measure.ae_smul_measure
    filter_upwards [ae_restrict_mem hK] with D hD
    exact (hEqRaw D hD).symm
  have hHν : Integrable H ν := (integrable_congr hEqν).mpr hGν
  have hMeanν : (∫ D, H D ∂ν) = ∫ D, G (datasetToEuclidean D) ∂ν :=
    integral_congr_ae hEqν
  refine ⟨G, hG, hEqRaw, hRawInt, hHν, hSG', ?_⟩
  filter_upwards [hEqν] with D hD
  rw [hD, hMeanν]

end LOOConcentration.Revision
