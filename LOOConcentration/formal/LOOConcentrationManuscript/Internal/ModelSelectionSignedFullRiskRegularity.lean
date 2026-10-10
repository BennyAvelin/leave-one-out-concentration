import LOOConcentrationRevision.Concentration.ExpectedSegmentGradientAE

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal

open MeasureTheory
open scoped Gradient

/-- Integrating a signed training section against the original test law gives
all test fibers and the expected-risk gradient bound on the whole original
Euclidean data carrier. -/
theorem modelSelection_signed_full_expected_risk_segment
    {k m n : ℕ} (μ : Measure (LOOConcentration.Observation k m))
    [IsProbabilityMeasure μ]
    (F : LOOConcentration.Observation k m →
      EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (n + 2)) → ℝ)
    (δ₁ δ₂ : ℕ → LOOConcentration.Observation k m → ℝ)
    (hjoint : Measurable (fun p : LOOConcentration.Observation k m ×
        EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (n + 2)) =>
        F p.1 p.2))
    (hloc : ∀ᵐ z ∂μ, LocallyLipschitz (F z))
    (hδ₁_nonneg : ∀ z, 0 ≤ δ₁ (n + 2) z)
    (hδ₂_nonneg : ∀ z, 0 ≤ δ₂ (n + 2) z)
    (hδ₁_int : Integrable (fun z => δ₁ (n + 2) z) μ)
    (hδ₂_int : Integrable (fun z => δ₂ (n + 2) z) μ)
    (hzero : Integrable (fun z => F z 0) μ)
    (hgrad : ∀ᵐ z ∂μ, ∀ᵐ x ∂(volume : Measure
        (EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (n + 2)))),
      DifferentiableAt ℝ (F z) x ∧
        ‖gradient (F z) x‖ ≤ δ₁ (n + 2) z + δ₂ (n + 2) z * ‖x‖) :
    (∀ x, Integrable (fun z => F z x) μ) ∧
      (∀ x y,
        |(∫ z, F z x ∂μ) - (∫ z, F z y ∂μ)| ≤
          ‖x - y‖ *
            ((∫ z, δ₁ (n + 2) z ∂μ) +
              (∫ z, δ₂ (n + 2) z ∂μ) / 2 * (‖x‖ + ‖y‖))) ∧
      LocallyLipschitz (fun x => ∫ z, F z x ∂μ) ∧
      ∀ᵐ x ∂(volume : Measure
          (EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (n + 2)))),
        DifferentiableAt ℝ (fun x => ∫ z, F z x ∂μ) x ∧
          ‖gradient (fun x => ∫ z, F z x ∂μ) x‖ ≤
            (∫ z, δ₁ (n + 2) z ∂μ) +
              (∫ z, δ₂ (n + 2) z ∂μ) * ‖x‖ := by
  let A : LOOConcentration.Observation k m → NNReal := fun z =>
    NNReal.mk (δ₁ (n + 2) z) (hδ₁_nonneg z)
  let B : LOOConcentration.Observation k m → NNReal := fun z =>
    NNReal.mk (δ₂ (n + 2) z) (hδ₂_nonneg z)
  have hA : Integrable (fun z => (A z : ℝ)) μ := by
    simpa [A, NNReal.coe_mk] using hδ₁_int
  have hB : Integrable (fun z => (B z : ℝ)) μ := by
    simpa [B, NNReal.coe_mk] using hδ₂_int
  have hgrad' : ∀ᵐ z ∂μ, ∀ᵐ x ∂(volume : Measure
      (EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (n + 2)))),
      DifferentiableAt ℝ (F z) x ∧
        ‖gradient (F z) x‖ ≤ (A z : ℝ) + (B z : ℝ) * ‖x‖ := by
    simpa [A, B, NNReal.coe_mk] using hgrad
  have h := LOOConcentration.Revision.expected_segment_gradient_ae
    μ F hjoint hloc A B hA hB hzero hgrad'
  simpa [A, B, NNReal.coe_mk] using h

/-- The signed full expected risk is locally Lipschitz and has the integrated
source gradient bound almost everywhere on the original carrier. -/
theorem modelSelection_signed_full_mean_regularity
    {k m n : ℕ} (μ : Measure (LOOConcentration.Observation k m))
    [IsProbabilityMeasure μ]
    (F : LOOConcentration.Observation k m →
      EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (n + 2)) → ℝ)
    (δ₁ δ₂ : ℕ → LOOConcentration.Observation k m → ℝ)
    (hjoint : Measurable (fun p : LOOConcentration.Observation k m ×
        EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (n + 2)) =>
        F p.1 p.2))
    (hloc : ∀ᵐ z ∂μ, LocallyLipschitz (F z))
    (hδ₁_nonneg : ∀ z, 0 ≤ δ₁ (n + 2) z)
    (hδ₂_nonneg : ∀ z, 0 ≤ δ₂ (n + 2) z)
    (hδ₁_int : Integrable (fun z => δ₁ (n + 2) z) μ)
    (hδ₂_int : Integrable (fun z => δ₂ (n + 2) z) μ)
    (hzero : Integrable (fun z => F z 0) μ)
    (hgrad : ∀ᵐ z ∂μ, ∀ᵐ x ∂(volume : Measure
        (EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (n + 2)))),
      DifferentiableAt ℝ (F z) x ∧
        ‖gradient (F z) x‖ ≤ δ₁ (n + 2) z + δ₂ (n + 2) z * ‖x‖) :
    (∀ x, Integrable (fun z => F z x) μ) ∧
      LocallyLipschitz (fun x => ∫ z, F z x ∂μ) ∧
      ∀ᵐ x ∂(volume : Measure
          (EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (n + 2)))),
        DifferentiableAt ℝ (fun x => ∫ z, F z x ∂μ) x ∧
          ‖gradient (fun x => ∫ z, F z x ∂μ) x‖ ≤
            (∫ z, δ₁ (n + 2) z ∂μ) +
              (∫ z, δ₂ (n + 2) z ∂μ) * ‖x‖ := by
  have h := modelSelection_signed_full_expected_risk_segment
    μ F δ₁ δ₂ hjoint hloc hδ₁_nonneg hδ₂_nonneg hδ₁_int hδ₂_int hzero hgrad
  exact ⟨h.1, h.2.2.1, h.2.2.2⟩

/-- If the second signed growth rate vanishes almost everywhere, the full
expected risk is globally Lipschitz with rate integral δ₁. -/
theorem modelSelection_signed_full_mean_lipschitz_of_zero_growth
    {k m n : ℕ} (μ : Measure (LOOConcentration.Observation k m))
    [IsProbabilityMeasure μ]
    (F : LOOConcentration.Observation k m →
      EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (n + 2)) → ℝ)
    (δ₁ δ₂ : ℕ → LOOConcentration.Observation k m → ℝ)
    (hjoint : Measurable (fun p : LOOConcentration.Observation k m ×
        EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (n + 2)) =>
        F p.1 p.2))
    (hloc : ∀ᵐ z ∂μ, LocallyLipschitz (F z))
    (hδ₁_nonneg : ∀ z, 0 ≤ δ₁ (n + 2) z)
    (hδ₂_nonneg : ∀ z, 0 ≤ δ₂ (n + 2) z)
    (hδ₁_int : Integrable (fun z => δ₁ (n + 2) z) μ)
    (hδ₂_int : Integrable (fun z => δ₂ (n + 2) z) μ)
    (hzero : Integrable (fun z => F z 0) μ)
    (hgrad : ∀ᵐ z ∂μ, ∀ᵐ x ∂(volume : Measure
        (EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (n + 2)))),
      DifferentiableAt ℝ (F z) x ∧
        ‖gradient (F z) x‖ ≤ δ₁ (n + 2) z + δ₂ (n + 2) z * ‖x‖)
    (hδ₂_zero : ∀ᵐ z ∂μ, δ₂ (n + 2) z = 0) :
    LipschitzWith
      (NNReal.mk (∫ z, δ₁ (n + 2) z ∂μ)
        (integral_nonneg (fun z => hδ₁_nonneg z)))
      (fun x => ∫ z, F z x ∂μ) := by
  have h := modelSelection_signed_full_expected_risk_segment
    μ F δ₁ δ₂ hjoint hloc hδ₁_nonneg hδ₂_nonneg hδ₁_int hδ₂_int hzero hgrad
  have hδ₂_integral : (∫ z, δ₂ (n + 2) z ∂μ) = 0 := by
    calc
      (∫ z, δ₂ (n + 2) z ∂μ) = ∫ z, (0 : ℝ) ∂μ :=
        integral_congr_ae hδ₂_zero
      _ = 0 := by simp
  have hsegment (x y : EuclideanSpace ℝ
      (LOOConcentration.DatasetCoordinate k m (n + 2))) :
      |(∫ z, F z x ∂μ) - (∫ z, F z y ∂μ)| ≤
        ‖x - y‖ * (∫ z, δ₁ (n + 2) z ∂μ) := by
    have hxy := h.2.1 x y
    simpa [hδ₂_integral] using hxy
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro x y
  rw [Real.dist_eq, dist_eq_norm]
  simpa only [Real.norm_eq_abs, NNReal.coe_mk, mul_comm] using hsegment x y

end LOOConcentration.Manuscript.Internal
