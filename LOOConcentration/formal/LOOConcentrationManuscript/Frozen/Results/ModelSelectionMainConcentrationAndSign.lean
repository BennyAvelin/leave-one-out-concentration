import LOOConcentrationManuscript.Internal.ModelSelectionSignedMainJoint

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript
open MeasureTheory Filter
open LOOConcentration.Revision LOOConcentration.Manuscript.Internal
open scoped Gradient Topology ENNReal

theorem modelSelection_main_concentration_and_sign
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
    (hδ₁_short_nonneg : ∀ z, 0 ≤ δ₁ (n + 1) z)
    (hδ₂_short_nonneg : ∀ z, 0 ≤ δ₂ (n + 1) z)
    (hδ₁_short_int : Integrable (fun z => δ₁ (n + 1) z) μ)
    (hδ₂_short_int : Integrable (fun z => δ₂ (n + 1) z) μ)
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
    let θ₁ := (n + 2 : ℝ) * ∫ z,
      Revision.thetaRate C M₂ ENNReal.toReal_nonneg
        (integral_nonneg observationNormSq_nonneg) (n + 1) (by omega) u hu
        (δ₁ (n + 1) z) (δ₂ (n + 1) z)
        (hδ₁_short_nonneg z) (hδ₂_short_nonneg z) ∂μ
    let θ₂ := Revision.thetaRate C M₂ ENNReal.toReal_nonneg
      (integral_nonneg observationNormSq_nonneg) (n + 2) (by omega) u hu
      (c / Real.sqrt (n + 2 : ℝ)) (d / (n + 2 : ℝ))
      (div_nonneg hc (Real.sqrt_nonneg _)) (div_nonneg hd (by positivity))
    let θ₃ := Revision.thetaRate C M₂ ENNReal.toReal_nonneg
      (integral_nonneg observationNormSq_nonneg) (n + 2) (by omega) w hw
      (∫ z, δ₁ (n + 2) z ∂μ) (∫ z, δ₂ (n + 2) z ∂μ)
      (integral_nonneg hδ₁_nonneg) (integral_nonneg hδ₂_nonneg)
    let Mix := θ₁ + θ₂ + θ₃
    P.real {D | R D - E D > ε} ≤ Mix ∧
      P.real {D | E D - R D > ε} ≤ Mix ∧
      P.real {D | |R D - E D| > ε} ≤ 2 * Mix ∧
      P.real {D | ε < |R D| ∧ E D * R D ≤ 0} ≤ 2 * Mix ∧
      ∀ a b : NNReal,
        (∀ᵐ z ∂μ, δ₁ (n + 1) z ≤ (a : ℝ) ∧ δ₂ (n + 1) z ≤ (b : ℝ)) →
        let θUni := Revision.thetaRate C M₂ ENNReal.toReal_nonneg
          (integral_nonneg observationNormSq_nonneg) (n + 1) (by omega) u hu
          (a : ℝ) (b : ℝ) a.property b.property
        P.real {D | R D - E D > ε} ≤ θUni + θ₂ + θ₃ ∧
          P.real {D | E D - R D > ε} ≤ θUni + θ₂ + θ₃ ∧
          P.real {D | |R D - E D| > ε} ≤ 2 * (θUni + θ₂ + θ₃) ∧
          P.real {D | ε < |R D| ∧ E D * R D ≤ 0} ≤
            2 * (θUni + θ₂ + θ₃) := by
  exact @LOOConcentration.Manuscript.Internal.modelSelection_actual_signed_main_joint_tails_and_sign
    k m n μ (inferInstance : IsProbabilityMeasure μ) T₀ T₁ L δ₁ δ₂ hSignedMeas hδ₁_nonneg hδ₂_nonneg hδ₁_int hδ₂_int hzero hloc hgrad hfinite hM₂ hf₀ hf₁ hShortMeas hδ₁_short_nonneg hδ₂_short_nonneg hδ₁_short_int hδ₂_short_int hShortLoc hShortGrad hMeanLoc hHeld δ₃ hδ₃_nonneg hBias hQueryInt c d hc hd hQueryGrad ε hε

end LOOConcentration.Manuscript
