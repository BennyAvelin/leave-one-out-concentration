import LOOConcentrationRevision.Concentration.ExpectedSegmentGradientAE
import LOOConcentrationRevision.Frozen.Definitions.StandingAssumption
import LOOConcentrationRevision.Geometry.CoordinateTransport

set_option autoImplicit false

namespace LOOConcentration.Revision
open MeasureTheory

/-- The literal full-sample expected test loss has the source gradient bound.
Both outer test-observation regularity inputs remain almost everywhere. -/
theorem standing_expected_full_loss_gradient
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d) :
    (∀ x : EuclideanSpace ℝ (DatasetCoordinate k m (n + 2)),
      Integrable (fun z => fittedLoss (T (n + 1)) L (datasetOfEuclidean x) z) μ) ∧
    LocallyLipschitz
      (fun x : EuclideanSpace ℝ (DatasetCoordinate k m (n + 2)) =>
        ∫ z, fittedLoss (T (n + 1)) L (datasetOfEuclidean x) z ∂μ) ∧
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (DatasetCoordinate k m (n + 2)))),
      let φ := fun y : EuclideanSpace ℝ (DatasetCoordinate k m (n + 2)) =>
        ∫ z, fittedLoss (T (n + 1)) L (datasetOfEuclidean y) z ∂μ
      DifferentiableAt ℝ φ x ∧ ‖gradient φ x‖ ≤
        (∫ z, δ₁ (n + 2) z ∂μ) + (∫ z, δ₂ (n + 2) z ∂μ) * ‖x‖ := by
  let F := fun z (x : EuclideanSpace ℝ (DatasetCoordinate k m (n + 2))) =>
    fittedLoss (T (n + 1)) L (datasetOfEuclidean x) z
  let A : Observation k m → NNReal := fun z =>
    ⟨δ₁ (n + 2) z, hSt.stable.delta₁_nonneg (n + 1) z⟩
  let B : Observation k m → NNReal := fun z =>
    ⟨δ₂ (n + 2) z, hSt.stable.delta₂_nonneg (n + 1) z⟩
  have hjoint : Measurable
      (fun p : Observation k m × EuclideanSpace ℝ (DatasetCoordinate k m (n + 2)) =>
        F p.1 p.2) :=
    (hSt.stable.measurable_loss (n + 1)).comp
      ((measurable_datasetOfEuclidean.comp measurable_snd).prodMk measurable_fst)
  have hzero : datasetOfEuclidean
      (0 : EuclideanSpace ℝ (DatasetCoordinate k m (n + 2))) = 0 := by
    rfl
  have h0 : Integrable (fun z => F z 0) μ := by
    simpa only [F, hzero] using hSt.zero_full_integrable
  have h := expected_segment_gradient_ae μ F hjoint
    (hSt.stable.locallyLipschitz_loss (n + 1)) A B
    hSt.delta₁_full_integrable hSt.delta₂_full_integrable h0
    (hSt.stable.gradient_loss (n + 1))
  exact ⟨h.1, h.2.2.1, h.2.2.2⟩

end LOOConcentration.Revision
