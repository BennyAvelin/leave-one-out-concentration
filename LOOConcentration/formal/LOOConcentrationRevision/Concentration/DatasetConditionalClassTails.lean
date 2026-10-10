import LOOConcentrationRevision.Concentration.DatasetRestrictedClassConstantViaInterface
import LOOConcentrationRevision.Concentration.DatasetLocalLipschitzExtensionViaInterface
import LOOConcentrationRevision.Concentration.DatasetLocalLipschitzExtension
import LOOConcentrationRevision.Probability.SubgaussianClassInfimumConsumer
import LOOConcentrationRevision.Probability.NormalizedRestrictionMap
import LOOConcentrationRevision.Concentration.CertifiedGaussianChernoff

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory

/-- The whole conditional class comparison is consumed at the actual event-local
observable, with one extension, the actual conditional mean and exact proxy. -/
theorem dataset_local_centered_normalizedRestriction_hasSubgaussianMGF_via_class_infimum_and_moment
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (hfinite : observationLogSobolevConstant μ < ⊤)
    (hM2 : Integrable observationNormSq μ)
    (H : Dataset (Observation k m) (n+2) → ℝ)
    (K : Set (Dataset (Observation k m) (n+2))) (hK : MeasurableSet K)
    (hq : 0 < (Measure.pi fun _ : Fin (n+2) => μ).real K)
    (L : NNReal)
    (hLip : ∀ D ∈ K, ∀ E ∈ K, |H D-H E| ≤ (L:ℝ)*datasetNorm (D-E)) :
    let P := Measure.pi fun _ : Fin (n+2) => μ
    let ν := normalizedRestriction P K
    Integrable H ν ∧ ProbabilityTheory.HasSubgaussianMGF
      (fun D => H D-∫ E, H E ∂ν)
      (Real.toNNReal ((3*(2:ℝ)^12*Real.exp 2)*(observationLogSobolevConstant μ).toReal*
        Real.log (Real.exp 1/P.real K)*(L:ℝ)^2)) ν := by
  let P := Measure.pi fun _ : Fin (n+2) => μ
  let Q := datasetLawOfObservation (r := n+2) μ
  let A := datasetOfEuclidean ⁻¹' K
  let ν := normalizedRestriction P K
  let ρ := normalizedRestriction Q A
  let : IsProbabilityMeasure Q := datasetLawOfObservation_isProbabilityMeasure μ
  let : IsProbabilityMeasure ν := normalizedRestriction_isProbability P K hq
  have hA : MeasurableSet A := hK.preimage measurable_datasetOfEuclidean
  have hPreimage : datasetToEuclidean ⁻¹' A = K := by
    ext D
    simp only [A, Set.mem_preimage, datasetOfEuclidean_datasetToEuclidean]
  have hqeq : Q.real A = P.real K := by
    unfold Measure.real
    change (P.map datasetToEuclidean A).toReal = _
    rw [Measure.map_apply measurable_datasetToEuclidean hA, hPreimage]
  have hqa : 0 < Q.real A := hqeq ▸ hq
  let : IsProbabilityMeasure ρ := normalizedRestriction_isProbability Q A hqa
  have hMap : ν.map datasetToEuclidean = ρ := by
    have h := normalizedRestriction_map P datasetToEuclidean measurable_datasetToEuclidean A hA
    rw [hPreimage] at h
    exact h
  obtain ⟨G, hG, _hEq, hRawInt, hHν, _hRawSG, hEqCenter⟩ :=
    dataset_local_lipschitz_extension_mgf μ hfinite hM2 H K hK hq L hLip
  have hGQ : Integrable G Q :=
    (integrable_map_measure hG.continuous.aestronglyMeasurable
      measurable_datasetToEuclidean.aemeasurable).2 hRawInt
  have hA0 : Q A ≠ 0 := by
    intro hz
    have : Q.real A = 0 := by simp [Measure.real, hz]
    exact hqa.ne' this
  have hGρ : Integrable G ρ := hGQ.restrict.smul_measure (ENNReal.inv_ne_top.mpr hA0)
  have hSupport : ∀ᵐ x ∂ρ, x ∈ A := by
    apply Measure.ae_smul_measure
    exact ae_restrict_mem hA
  let ℓ := Real.log (Real.exp 1/P.real K)
  have hℓ : 0 ≤ ℓ := by
    have hlog := Real.log_nonpos hq.le (measureReal_le_one (μ := P) (s := K))
    dsimp [ℓ]
    rw [Real.log_div (Real.exp_pos _).ne' hq.ne', Real.log_exp]
    linarith
  let a := (3*(2:ℝ)^12*Real.exp 2)*ℓ
  have ha : 0 ≤ a := by dsimp [a]; positivity
  let c := Real.toNNReal (a*(observationLogSobolevConstant μ).toReal)
  have hc : 0 ≤ a*(observationLogSobolevConstant μ).toReal := by positivity
  have hcENN : (c:ENNReal) = ENNReal.ofReal a*observationLogSobolevConstant μ := by
    dsimp [c]
    rw [← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ hc,
      ENNReal.ofReal_mul ha, ENNReal.ofReal_toReal hfinite.ne]
  have hInf := dataset_normalizedRestriction_subgaussian_class_infimum_le_via_finite_lsi_interface
    μ hfinite K hK hq
  rw [← hcENN] at hInf
  have hGlocal : ∀ x ∈ A, ∀ y ∈ A, |G x-G y| ≤ (L:ℝ)*‖x-y‖ := by
    intro x _ y _
    simpa only [Real.dist_eq, Real.norm_eq_abs, dist_eq_norm] using hG.dist_le_mul x y
  have hSGρ := local_lipschitz_hasSubgaussianMGF_scaled_of_class_infimum_le
    ρ A c hInf hSupport G hGρ L hGlocal
  have hSGmap : ProbabilityTheory.HasSubgaussianMGF
      (fun x => G x-∫ y, G y ∂ρ) (c*L^2) (ν.map datasetToEuclidean) := by
    rw [hMap]
    exact hSGρ
  have hSGRaw := ProbabilityTheory.HasSubgaussianMGF.of_map
    measurable_datasetToEuclidean.aemeasurable hSGmap
  have hMean : (∫ x, G x ∂ρ) = ∫ D, G (datasetToEuclidean D) ∂ν := by
    rw [← hMap]
    exact integral_map measurable_datasetToEuclidean.aemeasurable hG.continuous.aestronglyMeasurable
  change ProbabilityTheory.HasSubgaussianMGF
    (fun D => G (datasetToEuclidean D)-∫ x, G x ∂ρ) (c*L^2) ν at hSGRaw
  rw [hMean] at hSGRaw
  refine ⟨hHν, ?_⟩
  have hSGH := hSGRaw.congr hEqCenter.symm
  have hv : 0 ≤ (3*(2:ℝ)^12*Real.exp 2)*(observationLogSobolevConstant μ).toReal*ℓ*(L:ℝ)^2 := by
    positivity
  convert hSGH using 1
  apply NNReal.coe_injective
  rw [NNReal.coe_mul, NNReal.coe_pow, Real.coe_toNNReal _ hv, Real.coe_toNNReal _ hc]
  dsimp [a]
  ring

/-- Whole source producer: the raw observation moment is internally supplied. -/
theorem dataset_local_centered_normalizedRestriction_hasSubgaussianMGF_via_class_infimum
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (hfinite : observationLogSobolevConstant μ < ⊤)
    (H : Dataset (Observation k m) (n+2) → ℝ)
    (K : Set (Dataset (Observation k m) (n+2))) (hK : MeasurableSet K)
    (hq : 0 < (Measure.pi fun _ : Fin (n+2) => μ).real K)
    (L : NNReal)
    (hLip : ∀ D ∈ K, ∀ E ∈ K, |H D-H E| ≤ (L:ℝ)*datasetNorm (D-E)) :
    let P := Measure.pi fun _ : Fin (n+2) => μ
    let ν := normalizedRestriction P K
    Integrable H ν ∧ ProbabilityTheory.HasSubgaussianMGF
      (fun D => H D-∫ E, H E ∂ν)
      (Real.toNNReal ((3*(2:ℝ)^12*Real.exp 2)*(observationLogSobolevConstant μ).toReal*
        Real.log (Real.exp 1/P.real K)*(L:ℝ)^2)) ν := by
  exact dataset_local_centered_normalizedRestriction_hasSubgaussianMGF_via_class_infimum_and_moment
    μ hfinite (integrable_observationNormSq_of_finite_lsi μ hfinite) H K hK hq L hLip

/-- Both strict conditional tails use the whole source-class producer and the
certified sharp Gaussian Chernoff kernel, including the zero-proxy convention. -/
theorem dataset_local_centered_normalizedRestriction_strict_tails_le_via_class_infimum_and_moment
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (hfinite : observationLogSobolevConstant μ < ⊤)
    (hM2 : Integrable observationNormSq μ)
    (H : Dataset (Observation k m) (n+2) → ℝ)
    (K : Set (Dataset (Observation k m) (n+2))) (hK : MeasurableSet K)
    (hq : 0 < (Measure.pi fun _ : Fin (n+2) => μ).real K)
    (L : NNReal)
    (hLip : ∀ D ∈ K, ∀ E ∈ K, |H D-H E| ≤ (L:ℝ)*datasetNorm (D-E))
    (t : ℝ) (ht : 0 < t) :
    let P := Measure.pi fun _ : Fin (n+2) => μ
    let ν := normalizedRestriction P K
    let v := (3*(2:ℝ)^12*Real.exp 2)*(observationLogSobolevConstant μ).toReal*
      Real.log (Real.exp 1/P.real K)*(L:ℝ)^2
    (ν.real {D | H D-∫ E, H E ∂ν > t} ≤ if v=0 then 0 else Real.exp (-(t^2/(2*v)))) ∧
    (ν.real {D | -(H D-∫ E, H E ∂ν) > t} ≤ if v=0 then 0 else Real.exp (-(t^2/(2*v)))) := by
  let P := Measure.pi fun _ : Fin (n+2) => μ
  let ν := normalizedRestriction P K
  let : IsProbabilityMeasure ν := normalizedRestriction_isProbability P K hq
  let ℓ := Real.log (Real.exp 1/P.real K)
  have hℓ : 0 ≤ ℓ := by
    have hlog := Real.log_nonpos hq.le (measureReal_le_one (μ := P) (s := K))
    dsimp [ℓ]
    rw [Real.log_div (Real.exp_pos _).ne' hq.ne', Real.log_exp]
    linarith
  let v := (3*(2:ℝ)^12*Real.exp 2)*(observationLogSobolevConstant μ).toReal*ℓ*(L:ℝ)^2
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have h0 : Real.toNNReal v = 0 ↔ v=0 := by
    constructor
    · intro h
      have hc := congrArg (fun z : NNReal => (z:ℝ)) h
      simpa only [Real.coe_toNNReal _ hv, NNReal.coe_zero] using hc
    · intro h
      rw [h, Real.toNNReal_zero]
  have hSG := (dataset_local_centered_normalizedRestriction_hasSubgaussianMGF_via_class_infimum_and_moment
    μ hfinite hM2 H K hK hq L hLip).2
  have hT := strict_tails_le_of_subgaussianMGF_via_certified_chernoff ν
    (fun D => H D-∫ E, H E ∂ν) (Real.toNNReal v) hSG t ht
  simpa only [h0, Real.coe_toNNReal _ hv] using hT

/-- Whole source tail producer discharges the raw moment before application. -/
theorem dataset_local_centered_normalizedRestriction_strict_tails_le_via_class_infimum
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (hfinite : observationLogSobolevConstant μ < ⊤)
    (H : Dataset (Observation k m) (n+2) → ℝ)
    (K : Set (Dataset (Observation k m) (n+2))) (hK : MeasurableSet K)
    (hq : 0 < (Measure.pi fun _ : Fin (n+2) => μ).real K)
    (L : NNReal)
    (hLip : ∀ D ∈ K, ∀ E ∈ K, |H D-H E| ≤ (L:ℝ)*datasetNorm (D-E))
    (t : ℝ) (ht : 0 < t) :
    let P := Measure.pi fun _ : Fin (n+2) => μ
    let ν := normalizedRestriction P K
    let v := (3*(2:ℝ)^12*Real.exp 2)*(observationLogSobolevConstant μ).toReal*
      Real.log (Real.exp 1/P.real K)*(L:ℝ)^2
    (ν.real {D | H D-∫ E, H E ∂ν > t} ≤ if v=0 then 0 else Real.exp (-(t^2/(2*v)))) ∧
    (ν.real {D | -(H D-∫ E, H E ∂ν) > t} ≤ if v=0 then 0 else Real.exp (-(t^2/(2*v)))) := by
  exact dataset_local_centered_normalizedRestriction_strict_tails_le_via_class_infimum_and_moment
    μ hfinite (integrable_observationNormSq_of_finite_lsi μ hfinite) H K hK hq L hLip t ht

end LOOConcentration.Revision
