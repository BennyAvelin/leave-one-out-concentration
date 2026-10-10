import LOOConcentrationRevision.Analysis.UnboundedCenteredWholeMomentSource
import LOOConcentrationRevision.Results.StandingLossDecomposition
import LOOConcentrationRevision.Concentration.StandingValidationAverageGradient
import LOOConcentrationRevision.Concentration.ExpectedRiskGradientConsumer
import LOOConcentrationRevision.Probability.ProductSecondMoment
import LOOConcentration.Probability.RiskRepresentative

set_option autoImplicit false

namespace LOOConcentration.Revision

open MeasureTheory
open scoped ENNReal

noncomputable def standingValidationAverageFullEuclidean
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ)
    (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d) :
    EuclideanSpace ℝ (DatasetCoordinate k m (n + 2)) → ℝ :=
  fun x => standingValidationAverage μ T L δ₁ δ₂ δ₃ c d hSt (datasetOfEuclidean x)

noncomputable def expectedFullRiskEuclidean
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ) :
    EuclideanSpace ℝ (DatasetCoordinate k m (n + 2)) → ℝ :=
  fun x => ∫ z, fittedLoss (T (n + 1)) L (datasetOfEuclidean x) z ∂μ

/-- The actual validation-average representative has the unconditional
centered moment bound on the Euclidean product-law carrier. -/
theorem standing_validation_average_actual_centered_moment
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ)
    (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)
    {p : ℝ} (hp : 2 ≤ p) :
    MemLp
        (fun x : EuclideanSpace ℝ (DatasetCoordinate k m (n + 2)) =>
          standingValidationAverageFullEuclidean μ T L δ₁ δ₂ δ₃ c d hSt x -
            ∫ y, standingValidationAverageFullEuclidean μ T L δ₁ δ₂ δ₃ c d hSt y
              ∂datasetLawOfObservation (r := n + 2) μ)
        (ENNReal.ofReal p) (datasetLawOfObservation (r := n + 2) μ) ∧
      eLpNorm
          (fun x : EuclideanSpace ℝ (DatasetCoordinate k m (n + 2)) =>
            standingValidationAverageFullEuclidean μ T L δ₁ δ₂ δ₃ c d hSt x -
              ∫ y, standingValidationAverageFullEuclidean μ T L δ₁ δ₂ δ₃ c d hSt y
                ∂datasetLawOfObservation (r := n + 2) μ)
          (ENNReal.ofReal p) (datasetLawOfObservation (r := n + 2) μ) ≤
        ENNReal.ofReal
          (Real.sqrt ((observationLogSobolevConstant μ).toReal * (p - 1)) *
            (c / Real.sqrt (n + 2 : ℝ) +
              d / (n + 2 : ℝ) *
                Real.sqrt ((n + 2 : ℝ) * ∫ z, observationNormSq z ∂μ +
                  (observationLogSobolevConstant μ).toReal * (p - 2)))) := by
  let F : EuclideanSpace ℝ (DatasetCoordinate k m (n + 2)) → ℝ := fun x =>
    standingValidationAverage μ T L δ₁ δ₂ δ₃ c d hSt (datasetOfEuclidean x)
  have hgrad := standing_validation_average_gradient μ T L δ₁ δ₂ δ₃ c d hSt
  have hN : 0 < (n + 2 : ℝ) := by positivity
  let a : NNReal := ⟨c / Real.sqrt (n + 2 : ℝ),
    div_nonneg hSt.c_nonneg (Real.sqrt_nonneg _)⟩
  let b : NNReal := ⟨d / (n + 2 : ℝ), div_nonneg hSt.d_nonneg hN.le⟩
  have ha : (a : ℝ) = c / Real.sqrt (n + 2 : ℝ) := rfl
  have hb : (b : ℝ) = d / (n + 2 : ℝ) := rfl
  have hgrad' : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (DatasetCoordinate k m (n + 2)))),
      ‖gradient F x‖ ≤ (a : ℝ) + (b : ℝ) * ‖x‖ := by
    filter_upwards [hgrad.2] with x hx
    simpa only [F, ha, hb] using hx.2
  have h := unbounded_centered_observation_product μ hSt.lsi hSt.second_moment
    F hgrad.1 a b hgrad' hp
  constructor
  · exact h.2.1
  · have hbound := h.2.2
    rw [ha, hb] at hbound
    have hnR : (↑(n + 1 + 1) : ℝ) = (↑n + 2) := by push_cast; ring
    rw [hnR] at hbound
    simpa [F, standingValidationAverageFullEuclidean] using hbound

/-- The literal expected full-sample loss has the same unconditional centered
moment bound, with its constants obtained by integrating the Standing fields. -/
theorem standing_expected_full_loss_actual_centered_moment
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ)
    (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)
    {p : ℝ} (hp : 2 ≤ p) :
    MemLp
        (fun x : EuclideanSpace ℝ (DatasetCoordinate k m (n + 2)) =>
          expectedFullRiskEuclidean μ T L x -
            ∫ y, expectedFullRiskEuclidean μ T L y
              ∂datasetLawOfObservation (r := n + 2) μ)
        (ENNReal.ofReal p) (datasetLawOfObservation (r := n + 2) μ) ∧
      eLpNorm
          (fun x : EuclideanSpace ℝ (DatasetCoordinate k m (n + 2)) =>
            expectedFullRiskEuclidean μ T L x -
              ∫ y, expectedFullRiskEuclidean μ T L y
                ∂datasetLawOfObservation (r := n + 2) μ)
          (ENNReal.ofReal p) (datasetLawOfObservation (r := n + 2) μ) ≤
        ENNReal.ofReal
          (Real.sqrt ((observationLogSobolevConstant μ).toReal * (p - 1)) *
            ((∫ z, δ₁ (n + 2) z ∂μ) +
              (∫ z, δ₂ (n + 2) z ∂μ) *
                Real.sqrt ((n + 2 : ℝ) * ∫ z, observationNormSq z ∂μ +
                  (observationLogSobolevConstant μ).toReal * (p - 2)))) := by
  let F : EuclideanSpace ℝ (DatasetCoordinate k m (n + 2)) → ℝ := fun x =>
    ∫ z, fittedLoss (T (n + 1)) L (datasetOfEuclidean x) z ∂μ
  have hgrad := standing_expected_full_loss_gradient μ T L δ₁ δ₂ δ₃ c d hSt
  have hδ₁ : ∀ᵐ z ∂μ, 0 ≤ δ₁ (n + 2) z :=
    Filter.Eventually.of_forall (fun z => hSt.stable.delta₁_nonneg (n + 1) z)
  have hδ₂ : ∀ᵐ z ∂μ, 0 ≤ δ₂ (n + 2) z :=
    Filter.Eventually.of_forall (fun z => hSt.stable.delta₂_nonneg (n + 1) z)
  have ha : 0 ≤ ∫ z, δ₁ (n + 2) z ∂μ := integral_nonneg_of_ae hδ₁
  have hb : 0 ≤ ∫ z, δ₂ (n + 2) z ∂μ := integral_nonneg_of_ae hδ₂
  let a : NNReal := ⟨∫ z, δ₁ (n + 2) z ∂μ, ha⟩
  let b : NNReal := ⟨∫ z, δ₂ (n + 2) z ∂μ, hb⟩
  have ha_coe : (a : ℝ) = ∫ z, δ₁ (n + 2) z ∂μ := rfl
  have hb_coe : (b : ℝ) = ∫ z, δ₂ (n + 2) z ∂μ := rfl
  have hgrad' : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (DatasetCoordinate k m (n + 2)))),
      ‖gradient F x‖ ≤ (a : ℝ) + (b : ℝ) * ‖x‖ := by
    filter_upwards [hgrad.2.2] with x hx
    simpa only [F, ha_coe, hb_coe] using hx.2
  have h := unbounded_centered_observation_product μ hSt.lsi hSt.second_moment
    F hgrad.2.1 a b hgrad' hp
  constructor
  · exact h.2.1
  · have hbound := h.2.2
    rw [ha_coe, hb_coe] at hbound
    have hnR : (↑(n + 1 + 1) : ℝ) = (↑n + 2) := by push_cast; ring
    rw [hnR] at hbound
    simpa [F, expectedFullRiskEuclidean] using hbound

end LOOConcentration.Revision
