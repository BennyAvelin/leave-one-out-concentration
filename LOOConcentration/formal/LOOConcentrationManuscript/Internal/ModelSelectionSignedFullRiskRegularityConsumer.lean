import LOOConcentrationManuscript.Internal.ModelSelectionSignedFullRiskRegularity
import LOOConcentration.Frozen.Foundations.FittedLoss
import LOOConcentrationRevision.Frozen.Definitions.DatasetOfEuclidean
import LOOConcentrationRevision.Geometry.CoordinateTransport

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

/-- The actual signed full-fit expected risk has whole-carrier regularity.
Its zero-growth specialization is globally Lipschitz. The only integrability
input for regularity is the signed test loss at the zero training dataset. -/
theorem modelSelection_signed_full_mean_regularity_consumer
    {k m n : ℕ} (μ : Measure (LOOConcentration.Observation k m))
    [IsProbabilityMeasure μ]
    (T₀ T₁ : ∀ r : ℕ, LOOConcentration.Estimator k m (r + 1))
    (L : LOOConcentration.Responses m → LOOConcentration.Responses m → ℝ)
    (δ₁ δ₂ : ℕ → LOOConcentration.Observation k m → ℝ)
    (hSignedMeas : Measurable (fun p :
        LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 2) ×
          LOOConcentration.Observation k m =>
        LOOConcentration.fittedLoss (T₀ (n + 1)) L p.1 p.2 -
          LOOConcentration.fittedLoss (T₁ (n + 1)) L p.1 p.2))
    (hδ₁_nonneg : ∀ z, 0 ≤ δ₁ (n + 2) z)
    (hδ₂_nonneg : ∀ z, 0 ≤ δ₂ (n + 2) z)
    (hδ₁_int : Integrable (fun z => δ₁ (n + 2) z) μ)
    (hδ₂_int : Integrable (fun z => δ₂ (n + 2) z) μ)
    (hzero : Integrable
      (fun z =>
        LOOConcentration.fittedLoss (T₀ (n + 1)) L
            (0 : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 2)) z -
          LOOConcentration.fittedLoss (T₁ (n + 1)) L
            (0 : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 2)) z)
      μ)
    (hloc : ∀ᵐ z ∂μ,
      LocallyLipschitz
        (fun x : EuclideanSpace ℝ
            (LOOConcentration.DatasetCoordinate k m (n + 2)) =>
          LOOConcentration.fittedLoss (T₀ (n + 1)) L
              (LOOConcentration.Revision.datasetOfEuclidean x) z -
            LOOConcentration.fittedLoss (T₁ (n + 1)) L
              (LOOConcentration.Revision.datasetOfEuclidean x) z))
    (hgrad : ∀ᵐ z ∂μ, ∀ᵐ x ∂(volume : Measure
        (EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (n + 2)))),
      DifferentiableAt ℝ
          (fun y : EuclideanSpace ℝ
              (LOOConcentration.DatasetCoordinate k m (n + 2)) =>
            LOOConcentration.fittedLoss (T₀ (n + 1)) L
                (LOOConcentration.Revision.datasetOfEuclidean y) z -
              LOOConcentration.fittedLoss (T₁ (n + 1)) L
                (LOOConcentration.Revision.datasetOfEuclidean y) z) x ∧
        ‖gradient
            (fun y : EuclideanSpace ℝ
                (LOOConcentration.DatasetCoordinate k m (n + 2)) =>
              LOOConcentration.fittedLoss (T₀ (n + 1)) L
                  (LOOConcentration.Revision.datasetOfEuclidean y) z -
                LOOConcentration.fittedLoss (T₁ (n + 1)) L
                  (LOOConcentration.Revision.datasetOfEuclidean y) z) x‖ ≤
          δ₁ (n + 2) z + δ₂ (n + 2) z * ‖x‖) :
    let Ψ : EuclideanSpace ℝ
        (LOOConcentration.DatasetCoordinate k m (n + 2)) → ℝ :=
      fun x => ∫ z,
        (LOOConcentration.fittedLoss (T₀ (n + 1)) L
            (LOOConcentration.Revision.datasetOfEuclidean x) z -
          LOOConcentration.fittedLoss (T₁ (n + 1)) L
            (LOOConcentration.Revision.datasetOfEuclidean x) z) ∂μ
    (∀ x : EuclideanSpace ℝ
        (LOOConcentration.DatasetCoordinate k m (n + 2)),
      Integrable
        (fun z =>
          LOOConcentration.fittedLoss (T₀ (n + 1)) L
              (LOOConcentration.Revision.datasetOfEuclidean x) z -
            LOOConcentration.fittedLoss (T₁ (n + 1)) L
              (LOOConcentration.Revision.datasetOfEuclidean x) z)
        μ) ∧
      LocallyLipschitz Ψ ∧
      (∀ᵐ x ∂(volume : Measure
          (EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (n + 2)))),
        DifferentiableAt ℝ Ψ x ∧
          ‖gradient Ψ x‖ ≤
            (∫ z, δ₁ (n + 2) z ∂μ) +
              (∫ z, δ₂ (n + 2) z ∂μ) * ‖x‖) ∧
      ((∀ᵐ z ∂μ, δ₂ (n + 2) z = 0) →
        LipschitzWith
          (NNReal.mk (∫ z, δ₁ (n + 2) z ∂μ)
            (integral_nonneg (fun z => hδ₁_nonneg z))) Ψ) := by
  dsimp only
  let F : LOOConcentration.Observation k m →
      EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (n + 2)) → ℝ :=
    fun z x =>
      LOOConcentration.fittedLoss (T₀ (n + 1)) L
          (LOOConcentration.Revision.datasetOfEuclidean x) z -
        LOOConcentration.fittedLoss (T₁ (n + 1)) L
          (LOOConcentration.Revision.datasetOfEuclidean x) z
  have hjoint : Measurable (fun p :
      LOOConcentration.Observation k m ×
        EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (n + 2)) =>
      F p.1 p.2) :=
    hSignedMeas.comp
      ((LOOConcentration.Revision.measurable_datasetOfEuclidean.comp
        measurable_snd).prodMk measurable_fst)
  have hzero_map : LOOConcentration.Revision.datasetOfEuclidean
      (0 : EuclideanSpace ℝ
        (LOOConcentration.DatasetCoordinate k m (n + 2))) =
      (0 : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 2)) := by
    rfl
  have hzero' : Integrable (fun z => F z 0) μ := by
    simpa [F, hzero_map] using hzero
  have hloc' : ∀ᵐ z ∂μ, LocallyLipschitz (F z) := by
    simpa [F] using hloc
  have hgrad' : ∀ᵐ z ∂μ, ∀ᵐ x ∂(volume : Measure
      (EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (n + 2)))),
      DifferentiableAt ℝ (F z) x ∧
        ‖gradient (F z) x‖ ≤ δ₁ (n + 2) z + δ₂ (n + 2) z * ‖x‖ := by
    simpa [F] using hgrad
  have hregularity := modelSelection_signed_full_mean_regularity
    μ F δ₁ δ₂ hjoint hloc' hδ₁_nonneg hδ₂_nonneg hδ₁_int hδ₂_int hzero' hgrad'
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [F] using hregularity.1
  · simpa [F] using hregularity.2.1
  · simpa [F] using hregularity.2.2
  · intro hδ₂_zero
    have hlip := modelSelection_signed_full_mean_lipschitz_of_zero_growth
      μ F δ₁ δ₂ hjoint hloc' hδ₁_nonneg hδ₂_nonneg
      hδ₁_int hδ₂_int hzero' hgrad' hδ₂_zero
    simpa [F] using hlip

end LOOConcentration.Manuscript.Internal
