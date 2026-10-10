import LOOConcentrationManuscript.Internal.ModelSelectionSignedFullRiskRegularityConsumer
import LOOConcentrationManuscript.Internal.ModelSelectionDatasetConcentration
import LOOConcentrationManuscript.Internal.ModelSelectionRiskSubtractionAllDimensions
import Mathlib.Probability.Moments.SubGaussian

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

/-- Centered tails for the actual conditional-risk difference. The proof derives
its whole-data gradient bound from the signed zero-test section and integrated
source rates, then transfers the tails through the actual L¹ characterization.
The zero-growth branch retains the sharper Gaussian coefficient. -/
theorem modelSelection_actual_signed_risk_centered_tails
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
          δ₁ (n + 2) z + δ₂ (n + 2) z * ‖x‖)
    (hfinite : LOOConcentration.Revision.observationLogSobolevConstant μ ≠ ⊤)
    (hM₂ : Integrable LOOConcentration.observationNormSq μ)
    (hf₀ : Integrable
      (fun p : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 2) ×
          LOOConcentration.Observation k m =>
        LOOConcentration.fittedLoss (T₀ (n + 1)) L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ))
    (hf₁ : Integrable
      (fun p : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 2) ×
          LOOConcentration.Observation k m =>
        LOOConcentration.fittedLoss (T₁ (n + 1)) L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ))
    (t : ℝ) (ht : 0 < t) :
    let P : Measure (LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 2)) :=
      Measure.pi fun _ : Fin (n + 2) => μ
    let R : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 2) → ℝ :=
      fun D => LOOConcentration.Revision.looRiskL1 μ (T₀ (n + 1)) L hf₀ D -
        LOOConcentration.Revision.looRiskL1 μ (T₁ (n + 1)) L hf₁ D
    let C := (LOOConcentration.Revision.observationLogSobolevConstant μ).toReal
    let M₂ := ∫ z, LOOConcentration.observationNormSq z ∂μ
    let a := ∫ z, δ₁ (n + 2) z ∂μ
    let b := ∫ z, δ₂ (n + 2) z ∂μ
    let θ := LOOConcentration.Revision.thetaRate C M₂ ENNReal.toReal_nonneg
      (integral_nonneg LOOConcentration.observationNormSq_nonneg)
      (n + 2) (by omega) t ht a b
      (integral_nonneg hδ₁_nonneg) (integral_nonneg hδ₂_nonneg)
    let Γ := if b = 0 then
      (if C * a ^ 2 = 0 then 0 else Real.exp (-(t ^ 2 / (2 * C * a ^ 2)))) else θ
    P.real {D | R D - ∫ E, R E ∂P > t} ≤ Γ ∧
      P.real {D | ∫ E, R E ∂P - R D > t} ≤ Γ := by
  dsimp only
  let P : Measure (LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 2)) :=
    Measure.pi fun _ : Fin (n + 2) => μ
  let R : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 2) → ℝ :=
    fun D => LOOConcentration.Revision.looRiskL1 μ (T₀ (n + 1)) L hf₀ D -
      LOOConcentration.Revision.looRiskL1 μ (T₁ (n + 1)) L hf₁ D
  let Ψ : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 2) → ℝ :=
    fun D => ∫ z, (LOOConcentration.fittedLoss (T₀ (n + 1)) L D z -
      LOOConcentration.fittedLoss (T₁ (n + 1)) L D z) ∂μ
  have hregular := modelSelection_signed_full_mean_regularity_consumer
    μ T₀ T₁ L δ₁ δ₂ hSignedMeas hδ₁_nonneg hδ₂_nonneg hδ₁_int hδ₂_int hzero hloc hgrad
  have htails := LOOConcentration.Revision.original_dataset_signed_centered_tails
    μ (r := n + 2) (by omega) Ψ hfinite hM₂ hregular.2.1
    (∫ z, δ₁ (n + 2) z ∂μ) (∫ z, δ₂ (n + 2) z ∂μ)
    (integral_nonneg hδ₁_nonneg) (integral_nonneg hδ₂_nonneg) hregular.2.2.1 t ht
  have hAE : R =ᵐ[P] Ψ :=
    modelSelection_riskDifference_ae_eq_integral_all_dimensions μ T₀ T₁ L hf₀ hf₁
  have hMean : (∫ D, R D ∂P) = ∫ D, Ψ D ∂P := integral_congr_ae hAE
  have hPlus : P.real {D | R D - ∫ E, R E ∂P > t} =
      P.real {D | Ψ D - ∫ E, Ψ E ∂P > t} := by
    apply measureReal_congr
    filter_upwards [hAE] with D hD
    change (R D - ∫ E, R E ∂P > t) = (Ψ D - ∫ E, Ψ E ∂P > t)
    rw [hD, hMean]
  have hMinus : P.real {D | ∫ E, R E ∂P - R D > t} =
      P.real {D | ∫ E, Ψ E ∂P - Ψ D > t} := by
    apply measureReal_congr
    filter_upwards [hAE] with D hD
    change (∫ E, R E ∂P - R D > t) = (∫ E, Ψ E ∂P - Ψ D > t)
    rw [hD, hMean]
  exact ⟨hPlus.trans_le htails.1, hMinus.trans_le htails.2⟩

/-- With zero second growth rate almost everywhere, the actual conditional-risk
difference has the sharp subgaussian proxy C times the square of the integrated
first rate. No independence between error terms is asserted. -/
theorem modelSelection_actual_signed_risk_hasSubgaussianMGF
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
          δ₁ (n + 2) z + δ₂ (n + 2) z * ‖x‖)
    (hfinite : LOOConcentration.Revision.observationLogSobolevConstant μ ≠ ⊤)
    (hM₂ : Integrable LOOConcentration.observationNormSq μ)
    (hf₀ : Integrable
      (fun p : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 2) ×
          LOOConcentration.Observation k m =>
        LOOConcentration.fittedLoss (T₀ (n + 1)) L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ))
    (hf₁ : Integrable
      (fun p : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 2) ×
          LOOConcentration.Observation k m =>
        LOOConcentration.fittedLoss (T₁ (n + 1)) L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ))
    (hδ₂_zero : ∀ᵐ z ∂μ, δ₂ (n + 2) z = 0) :
    let P : Measure (LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 2)) :=
      Measure.pi fun _ : Fin (n + 2) => μ
    let R : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 2) → ℝ :=
      fun D => LOOConcentration.Revision.looRiskL1 μ (T₀ (n + 1)) L hf₀ D -
        LOOConcentration.Revision.looRiskL1 μ (T₁ (n + 1)) L hf₁ D
    let C := (LOOConcentration.Revision.observationLogSobolevConstant μ).toReal
    let a := ∫ z, δ₁ (n + 2) z ∂μ
    ProbabilityTheory.HasSubgaussianMGF (fun D => R D - ∫ E, R E ∂P)
      (NNReal.mk (C * a ^ 2) (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))) P := by
  dsimp only
  let P : Measure (LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 2)) :=
    Measure.pi fun _ : Fin (n + 2) => μ
  let R : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 2) → ℝ :=
    fun D => LOOConcentration.Revision.looRiskL1 μ (T₀ (n + 1)) L hf₀ D -
      LOOConcentration.Revision.looRiskL1 μ (T₁ (n + 1)) L hf₁ D
  let Ψ : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 2) → ℝ :=
    fun D => ∫ z, (LOOConcentration.fittedLoss (T₀ (n + 1)) L D z -
      LOOConcentration.fittedLoss (T₁ (n + 1)) L D z) ∂μ
  let C := (LOOConcentration.Revision.observationLogSobolevConstant μ).toReal
  let a := ∫ z, δ₁ (n + 2) z ∂μ
  let proxy : NNReal := ⟨C * a ^ 2, mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)⟩
  have hregular := modelSelection_signed_full_mean_regularity_consumer
    μ T₀ T₁ L δ₁ δ₂ hSignedMeas hδ₁_nonneg hδ₂_nonneg hδ₁_int hδ₂_int hzero hloc hgrad
  have hb : (∫ z, δ₂ (n + 2) z ∂μ) = 0 :=
    (integral_congr_ae hδ₂_zero).trans (integral_zero _ _)
  have hGradBound : ∀ᵐ x ∂(volume : Measure
      (EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (n + 2)))),
      DifferentiableAt ℝ
        (fun y => Ψ (LOOConcentration.Revision.datasetOfEuclidean y)) x ∧
      ‖gradient (fun y => Ψ (LOOConcentration.Revision.datasetOfEuclidean y)) x‖ ≤ a := by
    filter_upwards [hregular.2.2.1] with x hx
    simpa only [hb, zero_mul, add_zero] using hx
  have hmgf (s : ℝ) := LOOConcentration.Revision.original_dataset_signed_centered_mgf_bounded_gradient
    μ Ψ hfinite hM₂ hregular.2.1 a (integral_nonneg hδ₁_nonneg) hGradBound s
  have hΨ : ProbabilityTheory.HasSubgaussianMGF
      (fun D => Ψ D - ∫ E, Ψ E ∂P) proxy P := by
    constructor
    · intro s
      exact (hmgf s).2.1
    · intro s
      change (∫ D, Real.exp (s * (Ψ D - ∫ E, Ψ E ∂P)) ∂P) ≤
        Real.exp ((proxy : ℝ) * s ^ 2 / 2)
      have h := (hmgf s).2.2.1
      have hcoef : (C * a ^ 2 / 2) * s ^ 2 = (proxy : ℝ) * s ^ 2 / 2 := by
        change (C * a ^ 2 / 2) * s ^ 2 = (C * a ^ 2) * s ^ 2 / 2
        ring
      exact h.trans_eq (congrArg Real.exp hcoef)
  have hAE : R =ᵐ[P] Ψ :=
    modelSelection_riskDifference_ae_eq_integral_all_dimensions μ T₀ T₁ L hf₀ hf₁
  have hMean : (∫ D, R D ∂P) = ∫ D, Ψ D ∂P := integral_congr_ae hAE
  have hCenter : (fun D => Ψ D - ∫ E, Ψ E ∂P) =ᵐ[P]
      (fun D => R D - ∫ E, R E ∂P) := by
    filter_upwards [hAE] with D hD
    rw [hD, hMean]
  exact hΨ.congr hCenter

end LOOConcentration.Manuscript.Internal
