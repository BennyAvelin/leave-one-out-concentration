import LOOConcentrationManuscript.Internal.ModelSelectionSignedValidationAverageRegularity
import LOOConcentrationManuscript.Internal.ModelSelectionDatasetConcentration
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal

open MeasureTheory Filter
open scoped Gradient

/-- The two strict centered tails for a validation statistic on the original
observation product law, given the regularity produced by the query-average
lemma. -/
theorem original_dataset_signed_validation_average_centered_tails_of_regular
    {k m N : ℕ} (μ : Measure (LOOConcentration.Observation k m))
    [IsProbabilityMeasure μ]
    (G : LOOConcentration.Dataset (LOOConcentration.Observation k m) N → ℝ)
    (hfinite : LOOConcentration.Revision.observationLogSobolevConstant μ ≠ ⊤)
    (hM₂ : Integrable LOOConcentration.observationNormSq μ)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hregular : LocallyLipschitz (fun x : EuclideanSpace ℝ
      (LOOConcentration.DatasetCoordinate k m N) =>
        G (LOOConcentration.Revision.datasetOfEuclidean x)) ∧
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ
        (LOOConcentration.DatasetCoordinate k m N))),
        DifferentiableAt ℝ (fun x : EuclideanSpace ℝ
          (LOOConcentration.DatasetCoordinate k m N) =>
            G (LOOConcentration.Revision.datasetOfEuclidean x)) x ∧
        ‖gradient (fun x : EuclideanSpace ℝ
          (LOOConcentration.DatasetCoordinate k m N) =>
            G (LOOConcentration.Revision.datasetOfEuclidean x)) x‖ ≤ a+b*‖x‖)
    (hN : 1 ≤ N) (t : ℝ) (ht : 0 < t) :
    let P : Measure (LOOConcentration.Dataset (LOOConcentration.Observation k m) N) :=
      Measure.pi fun _ : Fin N => μ
    let C : ℝ := (LOOConcentration.Revision.observationLogSobolevConstant μ).toReal
    let M₂ : ℝ := ∫ y, LOOConcentration.observationNormSq y ∂μ
    let θ := LOOConcentration.Revision.thetaRate C M₂ ENNReal.toReal_nonneg
      (integral_nonneg LOOConcentration.observationNormSq_nonneg) N hN t ht a b ha hb
    P.real {D | G D-∫ D', G D' ∂P > t} ≤
        (if b = 0 then
          (if C*a^2 = 0 then 0 else Real.exp (-(t^2/(2*C*a^2)))) else θ) ∧
      P.real {D | ∫ D', G D' ∂P-G D > t} ≤
        (if b = 0 then
          (if C*a^2 = 0 then 0 else Real.exp (-(t^2/(2*C*a^2)))) else θ) := by
  dsimp only
  let P : Measure (LOOConcentration.Dataset (LOOConcentration.Observation k m) N) :=
    Measure.pi fun _ : Fin N => μ
  let C : ℝ := (LOOConcentration.Revision.observationLogSobolevConstant μ).toReal
  let M₂ : ℝ := ∫ y, LOOConcentration.observationNormSq y ∂μ
  let θ := LOOConcentration.Revision.thetaRate C M₂ ENNReal.toReal_nonneg
    (integral_nonneg LOOConcentration.observationNormSq_nonneg) N hN t ht a b ha hb
  have htails := LOOConcentration.Revision.original_dataset_signed_centered_tails
    μ hN G hfinite hM₂ hregular.1 a b ha hb hregular.2 t ht
  dsimp only at htails
  simpa only [P, C, M₂, θ] using htails

/-- A bounded-gradient validation statistic has the sharp zero-growth
subgaussian MGF on the original product law. -/
theorem original_dataset_signed_validation_average_hasSubgaussianMGF_of_bounded_gradient
    {k m N : ℕ} (μ : Measure (LOOConcentration.Observation k m))
    [IsProbabilityMeasure μ]
    (G : LOOConcentration.Dataset (LOOConcentration.Observation k m) N → ℝ)
    (hfinite : LOOConcentration.Revision.observationLogSobolevConstant μ ≠ ⊤)
    (hM₂ : Integrable LOOConcentration.observationNormSq μ)
    (a : ℝ) (ha : 0 ≤ a)
    (hregular : LocallyLipschitz (fun x : EuclideanSpace ℝ
      (LOOConcentration.DatasetCoordinate k m N) =>
        G (LOOConcentration.Revision.datasetOfEuclidean x)) ∧
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ
        (LOOConcentration.DatasetCoordinate k m N))),
        DifferentiableAt ℝ (fun x : EuclideanSpace ℝ
          (LOOConcentration.DatasetCoordinate k m N) =>
            G (LOOConcentration.Revision.datasetOfEuclidean x)) x ∧
        ‖gradient (fun x : EuclideanSpace ℝ
          (LOOConcentration.DatasetCoordinate k m N) =>
            G (LOOConcentration.Revision.datasetOfEuclidean x)) x‖ ≤ a) :
    let P : Measure (LOOConcentration.Dataset (LOOConcentration.Observation k m) N) :=
      Measure.pi fun _ : Fin N => μ
    let C : ℝ := (LOOConcentration.Revision.observationLogSobolevConstant μ).toReal
    ProbabilityTheory.HasSubgaussianMGF
      (fun D => G D-∫ E, G E ∂P)
      (NNReal.mk (C*a^2) (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg a))) P := by
  dsimp only
  let P : Measure (LOOConcentration.Dataset (LOOConcentration.Observation k m) N) :=
    Measure.pi fun _ : Fin N => μ
  let C : ℝ := (LOOConcentration.Revision.observationLogSobolevConstant μ).toReal
  let proxy : NNReal := ⟨C*a^2, mul_nonneg ENNReal.toReal_nonneg (sq_nonneg a)⟩
  have hmgf s := LOOConcentration.Revision.original_dataset_signed_centered_mgf_bounded_gradient
    μ G hfinite hM₂ hregular.1 a ha hregular.2 s
  have hresult : ProbabilityTheory.HasSubgaussianMGF
      (fun D => G D-∫ E, G E ∂P) proxy P := by
    constructor
    · intro s
      exact (hmgf s).2.1
    · intro s
      change (∫ D, Real.exp (s*(G D-∫ E, G E ∂P)) ∂P) ≤
        Real.exp ((proxy : ℝ)*s^2/2)
      have h := (hmgf s).2.2.1
      have hcoef : (C*a^2/2)*s^2 = (proxy : ℝ)*s^2/2 := by
        change (C*a^2/2)*s^2 = (C*a^2)*s^2/2
        ring
      exact h.trans_eq (congrArg Real.exp hcoef)
  exact hresult

/-- A positive-growth validation statistic has the exact cutoff and MGF
exponent supplied by the original-dataset source theorem. -/
theorem original_dataset_signed_validation_average_positive_growth_mgf
    {k m N : ℕ} (μ : Measure (LOOConcentration.Observation k m))
    [IsProbabilityMeasure μ]
    (G : LOOConcentration.Dataset (LOOConcentration.Observation k m) N → ℝ)
    (hfinite : LOOConcentration.Revision.observationLogSobolevConstant μ ≠ ⊤)
    (hM₂ : Integrable LOOConcentration.observationNormSq μ)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hbpos : 0 < b)
    (hregular : LocallyLipschitz (fun x : EuclideanSpace ℝ
      (LOOConcentration.DatasetCoordinate k m N) =>
        G (LOOConcentration.Revision.datasetOfEuclidean x)) ∧
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ
        (LOOConcentration.DatasetCoordinate k m N))),
        DifferentiableAt ℝ (fun x : EuclideanSpace ℝ
          (LOOConcentration.DatasetCoordinate k m N) =>
            G (LOOConcentration.Revision.datasetOfEuclidean x)) x ∧
        ‖gradient (fun x : EuclideanSpace ℝ
          (LOOConcentration.DatasetCoordinate k m N) =>
            G (LOOConcentration.Revision.datasetOfEuclidean x)) x‖ ≤ a+b*‖x‖)
    (s : ℝ) (hcut : |s| ≤ 1 /
      (4*(LOOConcentration.Revision.observationLogSobolevConstant μ).toReal*b)) :
    let P : Measure (LOOConcentration.Dataset (LOOConcentration.Observation k m) N) :=
      Measure.pi fun _ : Fin N => μ
    let C : ℝ := (LOOConcentration.Revision.observationLogSobolevConstant μ).toReal
    let M₂ : ℝ := ∫ y, LOOConcentration.observationNormSq y ∂μ
    Integrable G P ∧
    Integrable (fun D => Real.exp (s*(G D-∫ D', G D' ∂P))) P ∧
    (∫ D, Real.exp (s*(G D-∫ D', G D' ∂P)) ∂P) ≤
      Real.exp ((2*C*(a^2+2*b^2*(N:ℝ)*M₂))*s^2) ∧
    Real.log (∫ D, Real.exp (s*(G D-∫ D', G D' ∂P)) ∂P) ≤
      (2*C*(a^2+2*b^2*(N:ℝ)*M₂))*s^2 := by
  dsimp only
  let P : Measure (LOOConcentration.Dataset (LOOConcentration.Observation k m) N) :=
    Measure.pi fun _ : Fin N => μ
  let C : ℝ := (LOOConcentration.Revision.observationLogSobolevConstant μ).toReal
  let M₂ : ℝ := ∫ y, LOOConcentration.observationNormSq y ∂μ
  exact LOOConcentration.Revision.original_dataset_signed_centered_mgf_positive_growth
    μ G hfinite hM₂ hregular.1 a b ha hb hbpos hregular.2 s hcut

end LOOConcentration.Manuscript.Internal
