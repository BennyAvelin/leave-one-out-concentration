import LOOConcentrationManuscript.Internal.ModelSelectionSignedValidationAverageRegularityConsumer
import LOOConcentrationManuscript.Internal.ModelSelectionSignedValidationConcentration
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
open LOOConcentration
open scoped Gradient

/-- Actual signed fitted-loss I₂ tails at full validation size `n+2`. The
query regularity premises concern the genuine signed expected short-loss mean;
the full validation-average regularity is derived in the proof. -/
theorem modelSelection_signed_validation_average_centered_tails
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T₀ T₁ : ∀ r : ℕ, Estimator k m (r+1))
    (L : Responses m → Responses m → ℝ)
    (hI : ∀ z : Observation k m,
      Integrable (fun D : Dataset (Observation k m) (n+1) =>
        fittedLoss (T₀ n) L D z-fittedLoss (T₁ n) L D z)
        (Measure.pi fun _ : Fin (n+1) => μ))
    (c d : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hfinite : Revision.observationLogSobolevConstant μ ≠ ⊤)
    (hM₂ : Integrable observationNormSq μ)
    (hlocal : LocallyLipschitz (modelSelectionSignedExpectedMeanQuery μ T₀ T₁ L hI))
    (hgrad : ∀ᵐ z ∂(volume : Measure
      (EuclideanSpace ℝ (ObservationCoordinate k m))),
      DifferentiableAt ℝ (modelSelectionSignedExpectedMeanQuery μ T₀ T₁ L hI) z ∧
      ‖gradient (modelSelectionSignedExpectedMeanQuery μ T₀ T₁ L hI) z‖ ≤ c+d*‖z‖)
    (t : ℝ) (ht : 0 < t) :
    let P : Measure (Dataset (Observation k m) (n+2)) :=
      Measure.pi fun _ : Fin (n+2) => μ
    let G : Dataset (Observation k m) (n+2) → ℝ := fun D =>
      modelSelectionSignedExpectedValidationAverage μ T₀ T₁ L hI D
    let C : ℝ := (Revision.observationLogSobolevConstant μ).toReal
    let M₂ : ℝ := ∫ y, observationNormSq y ∂μ
    let a := c/Real.sqrt (n+2:ℝ)
    let b := d/(n+2:ℝ)
    let θ := Revision.thetaRate C M₂ ENNReal.toReal_nonneg
      (integral_nonneg observationNormSq_nonneg) (n+2) (by omega) t ht a b
      (div_nonneg hc (Real.sqrt_nonneg _)) (div_nonneg hd (by positivity))
    P.real {D | G D-∫ E, G E ∂P > t} ≤
      (if b=0 then (if C*a^2=0 then 0 else Real.exp (-(t^2/(2*C*a^2)))) else θ) ∧
    P.real {D | ∫ E, G E ∂P-G D > t} ≤
      (if b=0 then (if C*a^2=0 then 0 else Real.exp (-(t^2/(2*C*a^2)))) else θ) := by
  dsimp only
  let P : Measure (Dataset (Observation k m) (n+2)) :=
    Measure.pi fun _ : Fin (n+2) => μ
  let G : Dataset (Observation k m) (n+2) → ℝ := fun D =>
    modelSelectionSignedExpectedValidationAverage μ T₀ T₁ L hI D
  let C : ℝ := (Revision.observationLogSobolevConstant μ).toReal
  let M₂ : ℝ := ∫ y, observationNormSq y ∂μ
  let a := c/Real.sqrt (n+2:ℝ)
  let b := d/(n+2:ℝ)
  let θ := Revision.thetaRate C M₂ ENNReal.toReal_nonneg
    (integral_nonneg observationNormSq_nonneg) (n+2) (by omega) t ht a b
    (div_nonneg hc (Real.sqrt_nonneg _)) (div_nonneg hd (by positivity))
  have hregular := modelSelectionSignedExpectedValidationAverage_regular
    μ T₀ T₁ L hI c d hc hd hlocal hgrad
  have hregular' : LocallyLipschitz (fun x : EuclideanSpace ℝ
      (DatasetCoordinate k m (n+2)) => G (Revision.datasetOfEuclidean x)) ∧
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (DatasetCoordinate k m (n+2)))),
        DifferentiableAt ℝ (fun x : EuclideanSpace ℝ
          (DatasetCoordinate k m (n+2)) => G (Revision.datasetOfEuclidean x)) x ∧
        ‖gradient (fun x : EuclideanSpace ℝ
          (DatasetCoordinate k m (n+2)) => G (Revision.datasetOfEuclidean x)) x‖ ≤ a+b*‖x‖ := by
    simpa only [G, modelSelectionSignedExpectedValidationAverage, a, b] using hregular
  have htails := original_dataset_signed_validation_average_centered_tails_of_regular
    μ G hfinite hM₂ a b (div_nonneg hc (Real.sqrt_nonneg _))
    (div_nonneg hd (by positivity)) hregular' (by omega) t ht
  dsimp only at htails
  simpa only [G, modelSelectionSignedExpectedValidationAverage, P, C, M₂, a, b, θ] using htails

/-- Actual signed fitted-loss I₂ has the sharp all-real subgaussian MGF when
the expected-query growth rate vanishes. -/
theorem modelSelection_signed_validation_average_hasSubgaussianMGF_of_zero_growth
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T₀ T₁ : ∀ r : ℕ, Estimator k m (r+1))
    (L : Responses m → Responses m → ℝ)
    (hI : ∀ z : Observation k m,
      Integrable (fun D : Dataset (Observation k m) (n+1) =>
        fittedLoss (T₀ n) L D z-fittedLoss (T₁ n) L D z)
        (Measure.pi fun _ : Fin (n+1) => μ))
    (c d : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) (hdzero : d=0)
    (hfinite : Revision.observationLogSobolevConstant μ ≠ ⊤)
    (hM₂ : Integrable observationNormSq μ)
    (hlocal : LocallyLipschitz (modelSelectionSignedExpectedMeanQuery μ T₀ T₁ L hI))
    (hgrad : ∀ᵐ z ∂(volume : Measure
      (EuclideanSpace ℝ (ObservationCoordinate k m))),
      DifferentiableAt ℝ (modelSelectionSignedExpectedMeanQuery μ T₀ T₁ L hI) z ∧
      ‖gradient (modelSelectionSignedExpectedMeanQuery μ T₀ T₁ L hI) z‖ ≤ c+d*‖z‖) :
    let P : Measure (Dataset (Observation k m) (n+2)) :=
      Measure.pi fun _ : Fin (n+2) => μ
    let G : Dataset (Observation k m) (n+2) → ℝ := fun D =>
      modelSelectionSignedExpectedValidationAverage μ T₀ T₁ L hI D
    let C : ℝ := (Revision.observationLogSobolevConstant μ).toReal
    ProbabilityTheory.HasSubgaussianMGF
      (fun D => G D-∫ E, G E ∂P)
      (NNReal.mk (C*(c/Real.sqrt (n+2:ℝ))^2)
        (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))) P := by
  dsimp only
  let P : Measure (Dataset (Observation k m) (n+2)) :=
    Measure.pi fun _ : Fin (n+2) => μ
  let G : Dataset (Observation k m) (n+2) → ℝ := fun D =>
    modelSelectionSignedExpectedValidationAverage μ T₀ T₁ L hI D
  let C : ℝ := (Revision.observationLogSobolevConstant μ).toReal
  let a := c/Real.sqrt (n+2:ℝ)
  have hregular := modelSelectionSignedExpectedValidationAverage_regular
    μ T₀ T₁ L hI c d hc hd hlocal hgrad
  have hregular' : LocallyLipschitz (fun x : EuclideanSpace ℝ
      (DatasetCoordinate k m (n+2)) => G (Revision.datasetOfEuclidean x)) ∧
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (DatasetCoordinate k m (n+2)))),
        DifferentiableAt ℝ (fun x : EuclideanSpace ℝ
          (DatasetCoordinate k m (n+2)) => G (Revision.datasetOfEuclidean x)) x ∧
        ‖gradient (fun x : EuclideanSpace ℝ
          (DatasetCoordinate k m (n+2)) => G (Revision.datasetOfEuclidean x)) x‖ ≤ a := by
    refine ⟨?_, ?_⟩
    · simpa only [G, modelSelectionSignedExpectedValidationAverage] using hregular.1
    · filter_upwards [hregular.2] with x hx
      refine ⟨hx.1, ?_⟩
      have hdN : d/(n+2:ℝ)=0 := by rw [hdzero]; simp
      simpa only [G, modelSelectionSignedExpectedValidationAverage, a, hdN,
        zero_mul, add_zero] using hx.2
  exact original_dataset_signed_validation_average_hasSubgaussianMGF_of_bounded_gradient
    μ G hfinite hM₂ a (div_nonneg hc (Real.sqrt_nonneg _)) hregular'

/-- Actual signed fitted-loss I₂ has the positive-growth MGF with the source
cutoff and exponent, after deriving full-average regularity from the query
mean assumptions. -/
theorem modelSelection_signed_validation_average_positive_growth_mgf
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T₀ T₁ : ∀ r : ℕ, Estimator k m (r+1))
    (L : Responses m → Responses m → ℝ)
    (hI : ∀ z : Observation k m,
      Integrable (fun D : Dataset (Observation k m) (n+1) =>
        fittedLoss (T₀ n) L D z-fittedLoss (T₁ n) L D z)
        (Measure.pi fun _ : Fin (n+1) => μ))
    (c d : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) (hdpos : 0<d)
    (hfinite : Revision.observationLogSobolevConstant μ ≠ ⊤)
    (hM₂ : Integrable observationNormSq μ)
    (hlocal : LocallyLipschitz (modelSelectionSignedExpectedMeanQuery μ T₀ T₁ L hI))
    (hgrad : ∀ᵐ z ∂(volume : Measure
      (EuclideanSpace ℝ (ObservationCoordinate k m))),
      DifferentiableAt ℝ (modelSelectionSignedExpectedMeanQuery μ T₀ T₁ L hI) z ∧
      ‖gradient (modelSelectionSignedExpectedMeanQuery μ T₀ T₁ L hI) z‖ ≤ c+d*‖z‖)
    (s : ℝ)
    (hcut : |s| ≤ 1 /
      (4*(Revision.observationLogSobolevConstant μ).toReal*(d/(n+2:ℝ)))) :
    let P : Measure (Dataset (Observation k m) (n+2)) :=
      Measure.pi fun _ : Fin (n+2) => μ
    let G : Dataset (Observation k m) (n+2) → ℝ := fun D =>
      modelSelectionSignedExpectedValidationAverage μ T₀ T₁ L hI D
    let C : ℝ := (Revision.observationLogSobolevConstant μ).toReal
    let M₂ : ℝ := ∫ y, observationNormSq y ∂μ
    let a := c/Real.sqrt (n+2:ℝ)
    let b := d/(n+2:ℝ)
    Integrable G P ∧
    Integrable (fun D => Real.exp (s*(G D-∫ E, G E ∂P))) P ∧
    (∫ D, Real.exp (s*(G D-∫ E, G E ∂P)) ∂P) ≤
      Real.exp ((2*C*(a^2+2*b^2*(n+2:ℝ)*M₂))*s^2) ∧
    Real.log (∫ D, Real.exp (s*(G D-∫ E, G E ∂P)) ∂P) ≤
      (2*C*(a^2+2*b^2*(n+2:ℝ)*M₂))*s^2 := by
  dsimp only
  let P : Measure (Dataset (Observation k m) (n+2)) :=
    Measure.pi fun _ : Fin (n+2) => μ
  let G : Dataset (Observation k m) (n+2) → ℝ := fun D =>
    modelSelectionSignedExpectedValidationAverage μ T₀ T₁ L hI D
  let C : ℝ := (Revision.observationLogSobolevConstant μ).toReal
  let M₂ : ℝ := ∫ y, observationNormSq y ∂μ
  let a := c/Real.sqrt (n+2:ℝ)
  let b := d/(n+2:ℝ)
  have hregular := modelSelectionSignedExpectedValidationAverage_regular
    μ T₀ T₁ L hI c d hc hd hlocal hgrad
  have hregular' : LocallyLipschitz (fun x : EuclideanSpace ℝ
      (DatasetCoordinate k m (n+2)) => G (Revision.datasetOfEuclidean x)) ∧
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (DatasetCoordinate k m (n+2)))),
        DifferentiableAt ℝ (fun x : EuclideanSpace ℝ
          (DatasetCoordinate k m (n+2)) => G (Revision.datasetOfEuclidean x)) x ∧
        ‖gradient (fun x : EuclideanSpace ℝ
          (DatasetCoordinate k m (n+2)) => G (Revision.datasetOfEuclidean x)) x‖ ≤ a+b*‖x‖ := by
    simpa only [G, modelSelectionSignedExpectedValidationAverage, a, b] using hregular
  simpa only [Nat.cast_add, Nat.cast_ofNat] using
    (original_dataset_signed_validation_average_positive_growth_mgf
      μ G hfinite hM₂ a b (div_nonneg hc (Real.sqrt_nonneg _))
      (div_nonneg hd (by positivity)) (by positivity) hregular' s hcut)

end LOOConcentration.Manuscript.Internal
