import LOOConcentrationManuscript.Internal.ModelSelectionSignedI1Mixture
import LOOConcentrationManuscript.Internal.ModelSelectionSignedI1UniformThetaTails
import LOOConcentrationManuscript.Internal.ModelSelectionSignedActualTailSplit
import LOOConcentrationManuscript.Internal.ModelSelectionSignedRiskConcentration
import LOOConcentrationManuscript.Internal.ModelSelectionSignedValidationConcentrationConsumer

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal
open MeasureTheory
open LOOConcentration.Revision
open scoped Gradient

private theorem signed_main_centered_rate_le_theta
    (C M₂ : ℝ) (hC : 0 ≤ C) (hM₂ : 0 ≤ M₂)
    (r : ℕ) (hr : 1 ≤ r) (t : ℝ) (ht : 0 < t)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (if b = 0 then
      (if C * a ^ 2 = 0 then 0 else Real.exp (-(t ^ 2 / (2 * C * a ^ 2))))
     else Revision.thetaRate C M₂ hC hM₂ r hr t ht a b ha hb) ≤
      Revision.thetaRate C M₂ hC hM₂ r hr t ht a b ha hb := by
  by_cases hz : b = 0
  · subst b
    simpa only [if_pos rfl, if_true] using signedI1_gaussian_le_thetaRate C M₂ hC hM₂ r hr t ht a ha
  · simp only [if_neg hz, le_refl]

/-- Both uniform main bounds for the actual signed model-selection error.
All intermediate centering, joint L¹, mean regularity and tail inputs are produced
inside the proof from the selected source fields. -/
theorem modelSelection_actual_signed_main_uniform_tails
    {k m n : ℕ} (μ : Measure (Observation k m))
    [IsProbabilityMeasure μ]
    (T₀ T₁ : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ)
    (hSignedMeas : Measurable (fun p :
        Dataset (Observation k m) (n + 2) ×
          Observation k m =>
        fittedLoss (T₀ (n + 1)) L p.1 p.2 -
          fittedLoss (T₁ (n + 1)) L p.1 p.2))
    (hδ₁_nonneg : ∀ z, 0 ≤ δ₁ (n + 2) z)
    (hδ₂_nonneg : ∀ z, 0 ≤ δ₂ (n + 2) z)
    (hδ₁_int : Integrable (fun z => δ₁ (n + 2) z) μ)
    (hδ₂_int : Integrable (fun z => δ₂ (n + 2) z) μ)
    (hzero : Integrable
      (fun z =>
        fittedLoss (T₀ (n + 1)) L
            (0 : Dataset (Observation k m) (n + 2)) z -
          fittedLoss (T₁ (n + 1)) L
            (0 : Dataset (Observation k m) (n + 2)) z)
      μ)
    (hloc : ∀ᵐ z ∂μ,
      LocallyLipschitz
        (fun x : EuclideanSpace ℝ
            (DatasetCoordinate k m (n + 2)) =>
          fittedLoss (T₀ (n + 1)) L
              (Revision.datasetOfEuclidean x) z -
            fittedLoss (T₁ (n + 1)) L
              (Revision.datasetOfEuclidean x) z))
    (hgrad : ∀ᵐ z ∂μ, ∀ᵐ x ∂(volume : Measure
        (EuclideanSpace ℝ (DatasetCoordinate k m (n + 2)))),
      DifferentiableAt ℝ
          (fun y : EuclideanSpace ℝ
              (DatasetCoordinate k m (n + 2)) =>
            fittedLoss (T₀ (n + 1)) L
                (Revision.datasetOfEuclidean y) z -
              fittedLoss (T₁ (n + 1)) L
                (Revision.datasetOfEuclidean y) z) x ∧
        ‖gradient
            (fun y : EuclideanSpace ℝ
                (DatasetCoordinate k m (n + 2)) =>
              fittedLoss (T₀ (n + 1)) L
                  (Revision.datasetOfEuclidean y) z -
                fittedLoss (T₁ (n + 1)) L
                  (Revision.datasetOfEuclidean y) z) x‖ ≤
          δ₁ (n + 2) z + δ₂ (n + 2) z * ‖x‖)
    (hfinite : Revision.observationLogSobolevConstant μ ≠ ⊤)
    (hM₂ : Integrable observationNormSq μ)
    (hf₀ : Integrable
      (fun p : Dataset (Observation k m) (n + 2) ×
          Observation k m =>
        fittedLoss (T₀ (n + 1)) L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ))
    (hf₁ : Integrable
      (fun p : Dataset (Observation k m) (n + 2) ×
          Observation k m =>
        fittedLoss (T₁ (n + 1)) L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ))
    (hShortMeas : Measurable (fun p : Dataset (Observation k m) (n + 1) × Observation k m =>
      fittedLoss (T₀ n) L p.1 p.2 - fittedLoss (T₁ n) L p.1 p.2))
    (hδ₂_short_nonneg : ∀ z, 0 ≤ δ₂ (n + 1) z)
    (hShortLoc : ∀ᵐ z ∂μ, LocallyLipschitz (fun x : EuclideanSpace ℝ
      (DatasetCoordinate k m (n + 1)) =>
        fittedLoss (T₀ n) L (datasetOfEuclidean x) z -
          fittedLoss (T₁ n) L (datasetOfEuclidean x) z))
    (hShortGrad : ∀ᵐ z ∂μ, ∀ᵐ x ∂(volume : Measure
      (EuclideanSpace ℝ (DatasetCoordinate k m (n + 1)))),
        DifferentiableAt ℝ (fun y : EuclideanSpace ℝ
          (DatasetCoordinate k m (n + 1)) =>
            fittedLoss (T₀ n) L (datasetOfEuclidean y) z -
              fittedLoss (T₁ n) L (datasetOfEuclidean y) z) x ∧
        ‖gradient (fun y : EuclideanSpace ℝ
          (DatasetCoordinate k m (n + 1)) =>
            fittedLoss (T₀ n) L (datasetOfEuclidean y) z -
              fittedLoss (T₁ n) L (datasetOfEuclidean y) z) x‖ ≤
          δ₁ (n + 1) z + δ₂ (n + 1) z * ‖x‖)
    (hMeanLoc : LocallyLipschitz
      (fun x : EuclideanSpace ℝ (ObservationCoordinate k m) =>
        ∫ D : Dataset (Observation k m) (n + 1),
          (fittedLoss (T₀ n) L D (observationOfEuclidean x) -
            fittedLoss (T₁ n) L D (observationOfEuclidean x)) ∂
              (Measure.pi fun _ : Fin (n + 1) => μ)))

    (hHeld : ∀ i : Fin (n + 2),
      Integrable (fun D : Dataset (Observation k m) (n + 2) =>
        fittedLoss (T₀ n) L (deleteAt D i) (D i) -
          fittedLoss (T₁ n) L (deleteAt D i) (D i))
        (Measure.pi fun _ : Fin (n + 2) => μ))
    (δ₃ : ℝ) (hδ₃_nonneg : 0 ≤ δ₃)
    (hBias : ∀ i : Fin (n + 2),
      |(∫ D : Dataset (Observation k m) (n + 2),
          (fittedLoss (T₀ n) L (deleteAt D i) (D i) -
            fittedLoss (T₁ n) L (deleteAt D i) (D i))
          ∂Measure.pi fun _ : Fin (n + 2) => μ) -
        (∫ p : Dataset (Observation k m) (n + 2) × Observation k m,
          (fittedLoss (T₀ (n + 1)) L p.1 p.2 -
            fittedLoss (T₁ (n + 1)) L p.1 p.2)
          ∂(Measure.pi fun _ : Fin (n + 2) => μ).prod μ)| ≤ δ₃)
    (hQueryInt : ∀ z : Observation k m,
      Integrable (fun D : Dataset (Observation k m) (n + 1) =>
        fittedLoss (T₀ n) L D z - fittedLoss (T₁ n) L D z)
        (Measure.pi fun _ : Fin (n + 1) => μ))
    (c d : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hQueryGrad : ∀ᵐ x ∂(volume : Measure
      (EuclideanSpace ℝ (ObservationCoordinate k m))),
      DifferentiableAt ℝ (modelSelectionSignedExpectedMeanQuery μ T₀ T₁ L hQueryInt) x ∧
      ‖gradient (modelSelectionSignedExpectedMeanQuery μ T₀ T₁ L hQueryInt) x‖ ≤
        c + d * ‖x‖)
    (a b : NNReal)
    (hBound : ∀ᵐ z ∂μ, δ₁ (n + 1) z ≤ (a : ℝ) ∧ δ₂ (n + 1) z ≤ (b : ℝ))
    (ε : ℝ) (hε : 3 * δ₃ < ε) :
    let P : Measure (Dataset (Observation k m) (n + 2)) :=
      Measure.pi fun _ : Fin (n + 2) => μ
    let R : Dataset (Observation k m) (n + 2) → ℝ := fun D =>
      Revision.looRiskL1 μ (T₀ (n + 1)) L hf₀ D -
        Revision.looRiskL1 μ (T₁ (n + 1)) L hf₁ D
    let E : Dataset (Observation k m) (n + 2) → ℝ := fun D =>
      looEstimate (T₀ n) L D - looEstimate (T₁ n) L D
    let C := (observationLogSobolevConstant μ).toReal
    let M₂ := ∫ z, observationNormSq z ∂μ
    let u := ε / 3
    let w := ε / 3 - δ₃
    let hu : 0 < u := by dsimp [u]; linarith
    let hw : 0 < w := by dsimp [w]; linarith
    let θ₁ := Revision.thetaRate C M₂ ENNReal.toReal_nonneg
      (integral_nonneg observationNormSq_nonneg) (n + 1) (by omega) u hu
      a b a.property b.property
    let θ₂ := Revision.thetaRate C M₂ ENNReal.toReal_nonneg
      (integral_nonneg observationNormSq_nonneg) (n + 2) (by omega) u hu
      (c / Real.sqrt (n + 2 : ℝ)) (d / (n + 2 : ℝ))
      (div_nonneg hc (Real.sqrt_nonneg _)) (div_nonneg hd (by positivity))
    let θ₃ := Revision.thetaRate C M₂ ENNReal.toReal_nonneg
      (integral_nonneg observationNormSq_nonneg) (n + 2) (by omega) w hw
      (∫ z, δ₁ (n + 2) z ∂μ) (∫ z, δ₂ (n + 2) z ∂μ)
      (integral_nonneg hδ₁_nonneg) (integral_nonneg hδ₂_nonneg)
    P.real {D | R D - E D > ε} ≤ θ₁ + θ₂ + θ₃ ∧
      P.real {D | E D - R D > ε} ≤ θ₁ + θ₂ + θ₃ := by
  dsimp only
  let P : Measure (Dataset (Observation k m) (n + 2)) := Measure.pi fun _ => μ
  let Q : Measure (Dataset (Observation k m) (n + 1)) := Measure.pi fun _ => μ
  let f : Observation k m → ℝ := fun z => ∫ D,
    (fittedLoss (T₀ n) L D z - fittedLoss (T₁ n) L D z) ∂Q
  let V : Dataset (Observation k m) (n + 2) → ℝ := fun D =>
    (∑ i : Fin (n + 2), f (D i)) / (n + 2 : ℝ)
  let E : Dataset (Observation k m) (n + 2) → ℝ := fun D =>
    looEstimate (T₀ n) L D - looEstimate (T₁ n) L D
  let R : Dataset (Observation k m) (n + 2) → ℝ := fun D =>
    Revision.looRiskL1 μ (T₀ (n + 1)) L hf₀ D -
      Revision.looRiskL1 μ (T₁ (n + 1)) L hf₁ D
  let C := (observationLogSobolevConstant μ).toReal
  let M₂ := ∫ z, observationNormSq z ∂μ
  let u := ε / 3
  let w := ε / 3 - δ₃
  have hu : 0 < u := by dsimp [u]; linarith
  have hw : 0 < w := by dsimp [w]; linarith
  have hI₁ := modelSelection_actual_signed_i1_uniform_theta_tails μ T₀ T₁ L δ₁ δ₂
    hfinite hM₂ hShortMeas hHeld hMeanLoc hShortLoc hShortGrad hδ₂_short_nonneg
    a b hBound u hu
  have hMeanLoc' : LocallyLipschitz
      (modelSelectionSignedExpectedMeanQuery μ T₀ T₁ L hQueryInt) := hMeanLoc
  have hI₂ := modelSelection_signed_validation_average_centered_tails
    μ T₀ T₁ L hQueryInt c d hc hd hfinite hM₂ hMeanLoc' hQueryGrad u hu
  have hI₃ := modelSelection_actual_signed_risk_centered_tails μ T₀ T₁ L δ₁ δ₂
    hSignedMeas hδ₁_nonneg hδ₂_nonneg hδ₁_int hδ₂_int hzero hloc hgrad
    hfinite hM₂ hf₀ hf₁ w hw
  have hΓ₂ := signed_main_centered_rate_le_theta C M₂ ENNReal.toReal_nonneg
    (integral_nonneg observationNormSq_nonneg) (n + 2) (by omega) u hu
    (c / Real.sqrt (n + 2 : ℝ)) (d / (n + 2 : ℝ))
    (div_nonneg hc (Real.sqrt_nonneg _)) (div_nonneg hd (by positivity))
  have hΓ₃ := signed_main_centered_rate_le_theta C M₂ ENNReal.toReal_nonneg
    (integral_nonneg observationNormSq_nonneg) (n + 2) (by omega) w hw
    (∫ z, δ₁ (n + 2) z ∂μ) (∫ z, δ₂ (n + 2) z ∂μ)
    (integral_nonneg hδ₁_nonneg) (integral_nonneg hδ₂_nonneg)
  have hSplit := modelSelection_actual_signed_main_and_simplified_tail_split
    μ T₀ T₁ L hf₀ hf₁ hShortMeas hHeld δ₃ hBias ε
  have hVG (D : Dataset (Observation k m) (n + 2)) :
      modelSelectionSignedExpectedValidationAverage μ T₀ T₁ L hQueryInt D = V D := by
    dsimp only [modelSelectionSignedExpectedValidationAverage, originalQueryValidationAverage,
      modelSelectionSignedExpectedMean, V, f, Q]
    simp only [Nat.cast_add, Nat.cast_ofNat, div_eq_mul_inv, one_mul, mul_comm]
  dsimp only at hI₁ hI₂ hI₃ hSplit
  simp only [hVG] at hI₂
  let θ₂ := Revision.thetaRate C M₂ ENNReal.toReal_nonneg
    (integral_nonneg observationNormSq_nonneg) (n + 2) (by omega) u hu
    (c / Real.sqrt (n + 2 : ℝ)) (d / (n + 2 : ℝ))
    (div_nonneg hc (Real.sqrt_nonneg _)) (div_nonneg hd (by positivity))
  let θ₃ := Revision.thetaRate C M₂ ENNReal.toReal_nonneg
    (integral_nonneg observationNormSq_nonneg) (n + 2) (by omega) w hw
    (∫ z, δ₁ (n + 2) z ∂μ) (∫ z, δ₂ (n + 2) z ∂μ)
    (integral_nonneg hδ₁_nonneg) (integral_nonneg hδ₂_nonneg)
  have hMinus₂ : P.real {D | V D - ∫ E, V E ∂P > u} ≤ θ₂ := hI₂.1.trans hΓ₂
  have hPlus₂ : P.real {D | (∫ E, V E ∂P) - V D > u} ≤ θ₂ := hI₂.2.trans hΓ₂
  have hPlus₃ := hI₃.1.trans hΓ₃
  have hMinus₃ := hI₃.2.trans hΓ₃
  constructor
  · exact hSplit.1.1.trans (add_le_add (add_le_add hI₁.1 hPlus₂) hPlus₃)
  · have hMinus₂' : P.real {D | -((∫ E, V E ∂P) - V D) > u} ≤ θ₂ := by
      simpa only [neg_sub] using hMinus₂
    have hMinus₃' : P.real {D | -(R D - ∫ E, R E ∂P) > w} ≤ θ₃ := by
      simpa only [neg_sub] using hMinus₃
    exact hSplit.1.2.trans (add_le_add (add_le_add hI₁.2 hMinus₂') hMinus₃')

end LOOConcentration.Manuscript.Internal
