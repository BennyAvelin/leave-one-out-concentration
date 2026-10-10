import LOOConcentrationRevision.Concentration.LipschitzHerbst
import LOOConcentrationRevision.Probability.LipschitzIntegrability
import LOOConcentrationRevision.FunctionalInequalities.BoundedProductLSI
import LOOConcentrationRevision.Probability.ProductLawTransport
import LOOConcentrationRevision.Probability.ProductSecondMoment
import LOOConcentrationRevision.Frozen.Definitions.StandingAssumption
import LOOConcentrationRevision.Geometry.CoordinateTransport
import LOOConcentrationRevision.Frozen.Definitions.DatasetOfEuclidean
import LOOConcentrationRevision.Frozen.Definitions.ObservationOfEuclidean
import LOOConcentrationRevision.Frozen.Definitions.ObservationLogSobolevConstant

set_option autoImplicit false
namespace LOOConcentration.Revision

open MeasureTheory

/-- The approved product LSI and Lipschitz Herbst estimate for any positive
finite ordered sample, including a singleton sample. -/
private theorem dataset_lipschitz_hasSubgaussianMGF_succ
    {k m r : ℕ} (μ : Measure (LOOConcentration.Observation k m))
    [IsProbabilityMeasure μ]
    (hfinite : observationLogSobolevConstant μ < ⊤)
    (hM2 : Integrable LOOConcentration.observationNormSq μ)
    (F : EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (r + 1)) → ℝ)
    (L : NNReal) (hLip : LipschitzWith L F) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun x => F x - ∫ y, F y ∂datasetLawOfObservation (r := r + 1) μ)
      (NNReal.mk ((observationLogSobolevConstant μ).toReal * (L : ℝ)^2)
        (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)))
      (datasetLawOfObservation (r := r + 1) μ) := by
  let ν := datasetLawOfObservation (r := r + 1) μ
  let : IsProbabilityMeasure ν := datasetLawOfObservation_isProbabilityMeasure μ
  let μE := μ.map observationToEuclidean
  let : IsProbabilityMeasure μE :=
    Measure.isProbabilityMeasure_map measurable_observationToEuclidean.aemeasurable
  have hbase : logSobolevConstant μE < ⊤ := by
    change observationLogSobolevConstant μ < ⊤
    exact hfinite
  have hprod := logSobolevConstant_euclideanProductLaw_le r μE hbase
  have hLS : logSobolevConstant ν ≤ logSobolevConstant μE := by
    simpa only [ν, μE, euclideanProductLaw_observation_map_eq_datasetLaw μ] using hprod
  have hLC : logSobolevConstant ν ≤ ENNReal.ofReal (observationLogSobolevConstant μ).toReal := by
    rw [ENNReal.ofReal_toReal hfinite.ne]
    change logSobolevConstant ν ≤ logSobolevConstant μE
    exact hLS
  have hInt : Integrable F ν := integrable_lipschitz_of_norm_sq ν
    (integrable_datasetLaw_norm_sq μ hM2) F L hLip
  constructor
  · intro lam
    exact (lipschitz_centered_exp_integrable_and_mgf_le ν _ ENNReal.toReal_nonneg
      hLC F L hLip hInt lam).1
  · intro lam
    have h := (lipschitz_centered_exp_integrable_and_mgf_le ν _ ENNReal.toReal_nonneg
      hLC F L hLip hInt lam).2
    change (∫ x, Real.exp (lam * (F x - ∫ y, F y ∂ν)) ∂ν) ≤
      Real.exp (((observationLogSobolevConstant μ).toReal * (L : ℝ)^2) * lam^2 / 2)
    exact h.trans_eq (congrArg Real.exp (by ring))

/-- For almost every held-out observation, zero linear-growth remainder in the
source gradient bound makes the actual fitted loss globally Lipschitz in the
ordered deleted sample. Its MGF is centered at the literal source mean. -/
theorem standing_deleted_loss_hasSubgaussianMGF
    {k m n : ℕ} (μ : Measure (LOOConcentration.Observation k m))
    [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, LOOConcentration.Estimator k m (r + 1))
    (L : LOOConcentration.Responses m → LOOConcentration.Responses m → ℝ)
    (δ₁ δ₂ : ℕ → LOOConcentration.Observation k m → ℝ)
    (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)
    (hzero : ∀ z, δ₂ (n + 1) z = 0) :
    ∀ᵐ z ∂μ,
      ProbabilityTheory.HasSubgaussianMGF
        (fun D : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 1) =>
          LOOConcentration.fittedLoss (T n) L D z -
            meanFittedLoss μ (T n) L z (hSt.mean_integrable z))
        (NNReal.mk
          ((observationLogSobolevConstant μ).toReal * (δ₁ (n + 1) z)^2)
          (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)))
        (Measure.pi fun _ : Fin (n + 1) => μ) := by
  filter_upwards [hSt.stable.locallyLipschitz_loss n,
    hSt.stable.gradient_loss n] with z hloc hgrad
  let F : EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (n + 1)) → ℝ :=
    fun x => LOOConcentration.fittedLoss (T n) L (datasetOfEuclidean x) z
  let a : NNReal := ⟨δ₁ (n + 1) z, hSt.stable.delta₁_nonneg n z⟩
  have ha : (a : ℝ) = δ₁ (n + 1) z := rfl
  have hgrad0 : ∀ᵐ x ∂(volume : Measure
      (EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (n + 1)))),
      DifferentiableAt ℝ F x ∧
        ‖gradient F x‖ ≤ (a : ℝ) + (0 : NNReal) * ‖x‖ := by
    filter_upwards [hgrad] with x hx
    have hx' : DifferentiableAt ℝ F x ∧
        ‖gradient F x‖ ≤ δ₁ (n + 1) z := by
      simpa [F, hzero z] using hx
    refine ⟨hx'.1, ?_⟩
    simpa [ha] using hx'.2
  have hseg (x y : EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (n + 1))) :
      |F x - F y| ≤ ‖x - y‖ * (a : ℝ) := by
    simpa only [NNReal.coe_zero, zero_div, zero_mul, add_zero] using
      ae_gradient_segment_estimate F hloc a 0 hgrad0 x y
  have hLip : LipschitzWith a F := by
    apply lipschitzWith_iff_dist_le_mul.mpr
    intro x y
    simpa only [dist_eq_norm, Real.norm_eq_abs, mul_comm] using hseg x y
  let ν := datasetLawOfObservation (r := n + 1) μ
  let P : Measure (LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 1)) :=
    Measure.pi fun _ : Fin (n + 1) => μ
  have hmgf := dataset_lipschitz_hasSubgaussianMGF_succ
    μ hSt.lsi hSt.second_moment F a hLip
  have hmean :
      (∫ E, F (datasetToEuclidean E) ∂P) =
        meanFittedLoss μ (T n) L z (hSt.mean_integrable z) := by
    rw [meanFittedLoss]
    apply integral_congr_ae
    filter_upwards [] with E
    simp [F, datasetOfEuclidean_datasetToEuclidean]
  have hmapMean : (∫ x, F x ∂ν) = ∫ E, F (datasetToEuclidean E) ∂P := by
    rw [show ν = P.map datasetToEuclidean by rfl]
    exact integral_map measurable_datasetToEuclidean.aemeasurable
      hLip.continuous.aestronglyMeasurable
  have hRaw := ProbabilityTheory.HasSubgaussianMGF.of_map
    measurable_datasetToEuclidean.aemeasurable hmgf
  have hRaw' : ProbabilityTheory.HasSubgaussianMGF
      (fun D : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 1) =>
        F (datasetToEuclidean D) - ∫ E, F (datasetToEuclidean E) ∂P)
      (NNReal.mk ((observationLogSobolevConstant μ).toReal * (a : ℝ)^2)
        (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))) P := by
    change ProbabilityTheory.HasSubgaussianMGF
      (fun D => F (datasetToEuclidean D) - ∫ x, F x ∂ν) _ P at hRaw
    rw [hmapMean] at hRaw
    exact hRaw
  rw [hmean] at hRaw'
  simpa only [ha, F, datasetOfEuclidean_datasetToEuclidean] using hRaw'

end LOOConcentration.Revision
