import LOOConcentrationManuscript.Internal.ModelSelectionMargin
import LOOConcentrationManuscript.Internal.ModelSelectionRiskSubtractionAllDimensionsConsumer
import LOOConcentrationManuscript.Internal.ModelSelectionSignedMainNonuniform
import LOOConcentrationManuscript.Internal.ModelSelectionSignedMainUniform

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

/-- The actual wrong-sign-or-tie event at a strict conditional-risk margin is bounded using both nonuniform main tails. -/
theorem modelSelection_actual_wrong_sign_nonuniform_bound
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
        (δ₁ (n + 1) z) (δ₂ (n + 1) z) (hδ₁_short_nonneg z) (hδ₂_short_nonneg z) ∂μ
    let θ₂ := Revision.thetaRate C M₂ ENNReal.toReal_nonneg
      (integral_nonneg observationNormSq_nonneg) (n + 2) (by omega) u hu
      (c / Real.sqrt (n + 2 : ℝ)) (d / (n + 2 : ℝ))
      (div_nonneg hc (Real.sqrt_nonneg _)) (div_nonneg hd (by positivity))
    let θ₃ := Revision.thetaRate C M₂ ENNReal.toReal_nonneg
      (integral_nonneg observationNormSq_nonneg) (n + 2) (by omega) w hw
      (∫ z, δ₁ (n + 2) z ∂μ) (∫ z, δ₂ (n + 2) z ∂μ)
      (integral_nonneg hδ₁_nonneg) (integral_nonneg hδ₂_nonneg)
    P.real {D | ε < |R D| ∧ E D * R D ≤ 0} ≤ 2 * (θ₁ + θ₂ + θ₃) := by
  dsimp only
  let P : Measure (Dataset (Observation k m) (n + 2)) := Measure.pi fun _ => μ
  let R : Dataset (Observation k m) (n + 2) → ℝ := fun D =>
    Revision.looRiskL1 μ (T₀ (n + 1)) L hf₀ D -
      Revision.looRiskL1 μ (T₁ (n + 1)) L hf₁ D
  let E : Dataset (Observation k m) (n + 2) → ℝ := fun D =>
    looEstimate (T₀ n) L D - looEstimate (T₁ n) L D
  let C := (observationLogSobolevConstant μ).toReal
  let M₂ := ∫ z, observationNormSq z ∂μ
  let u := ε / 3
  let w := ε / 3 - δ₃
  have hu : 0 < u := by dsimp [u]; linarith
  have hw : 0 < w := by dsimp [w]; linarith
  let θ₁ := (n + 2 : ℝ) * ∫ z,
    Revision.thetaRate C M₂ ENNReal.toReal_nonneg
      (integral_nonneg observationNormSq_nonneg) (n + 1) (by omega) u hu
      (δ₁ (n + 1) z) (δ₂ (n + 1) z) (hδ₁_short_nonneg z) (hδ₂_short_nonneg z) ∂μ
  let θ₂ := Revision.thetaRate C M₂ ENNReal.toReal_nonneg
    (integral_nonneg observationNormSq_nonneg) (n + 2) (by omega) u hu
    (c / Real.sqrt (n + 2 : ℝ)) (d / (n + 2 : ℝ))
    (div_nonneg hc (Real.sqrt_nonneg _)) (div_nonneg hd (by positivity))
  let θ₃ := Revision.thetaRate C M₂ ENNReal.toReal_nonneg
    (integral_nonneg observationNormSq_nonneg) (n + 2) (by omega) w hw
    (∫ z, δ₁ (n + 2) z ∂μ) (∫ z, δ₂ (n + 2) z ∂μ)
    (integral_nonneg hδ₁_nonneg) (integral_nonneg hδ₂_nonneg)
  have hTails := modelSelection_actual_signed_main_nonuniform_tails
    (n := n) μ T₀ T₁ L δ₁ δ₂ hSignedMeas hδ₁_nonneg hδ₂_nonneg
    hδ₁_int hδ₂_int hzero hloc hgrad hfinite hM₂ hf₀ hf₁ hShortMeas
    hδ₁_short_nonneg hδ₂_short_nonneg hδ₁_short_int hδ₂_short_int
    hShortLoc hShortGrad hMeanLoc hHeld δ₃ hδ₃_nonneg hBias hQueryInt
    c d hc hd hQueryGrad ε hε
  dsimp only at hTails
  have hMargin := modelSelection_actual_wrongSign_margin_event_subset_all_dimensions
    μ T₀ T₁ L hf₀ hf₁ ε
  change {D | ε < |R D| ∧ E D * R D ≤ 0} ⊆
    {D | ε < |R D - E D|} at hMargin
  have hDeviation : {D | ε < |R D - E D|} ⊆
      {D | R D - E D > ε} ∪ {D | E D - R D > ε} := by
    intro D hD
    change ε < |R D - E D| at hD
    by_cases hPlus : R D - E D > ε
    · exact Or.inl hPlus
    · right
      by_contra hMinus
      have hPlusLe : R D - E D ≤ ε := le_of_not_gt hPlus
      have hMinusLe : E D - R D ≤ ε := le_of_not_gt hMinus
      have hAbsLe : |R D - E D| ≤ ε :=
        (abs_le).2 ⟨by linarith, hPlusLe⟩
      exact (not_lt_of_ge hAbsLe) hD
  have hSubset := hMargin.trans hDeviation
  change P.real {D | ε < |R D| ∧ E D * R D ≤ 0} ≤
    2 * (θ₁ + θ₂ + θ₃)
  calc
    P.real {D | ε < |R D| ∧ E D * R D ≤ 0} ≤
        P.real ({D | R D - E D > ε} ∪ {D | E D - R D > ε}) :=
      measureReal_mono hSubset (measure_ne_top P _)
    _ ≤ P.real {D | R D - E D > ε} + P.real {D | E D - R D > ε} :=
      measureReal_union_le _ _
    _ ≤ (θ₁ + θ₂ + θ₃) + (θ₁ + θ₂ + θ₃) :=
      add_le_add hTails.1 hTails.2
    _ = 2 * (θ₁ + θ₂ + θ₃) := by ring


/-- The actual wrong-sign-or-tie event at a strict conditional-risk margin is bounded using both uniform main tails. -/
theorem modelSelection_actual_wrong_sign_uniform_bound
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
    P.real {D | ε < |R D| ∧ E D * R D ≤ 0} ≤ 2 * (θ₁ + θ₂ + θ₃) := by
  dsimp only
  let P : Measure (Dataset (Observation k m) (n + 2)) := Measure.pi fun _ => μ
  let R : Dataset (Observation k m) (n + 2) → ℝ := fun D =>
    Revision.looRiskL1 μ (T₀ (n + 1)) L hf₀ D -
      Revision.looRiskL1 μ (T₁ (n + 1)) L hf₁ D
  let E : Dataset (Observation k m) (n + 2) → ℝ := fun D =>
    looEstimate (T₀ n) L D - looEstimate (T₁ n) L D
  let C := (observationLogSobolevConstant μ).toReal
  let M₂ := ∫ z, observationNormSq z ∂μ
  let u := ε / 3
  let w := ε / 3 - δ₃
  have hu : 0 < u := by dsimp [u]; linarith
  have hw : 0 < w := by dsimp [w]; linarith
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
  have hTails := modelSelection_actual_signed_main_uniform_tails
    (n := n) μ T₀ T₁ L δ₁ δ₂ hSignedMeas hδ₁_nonneg hδ₂_nonneg
    hδ₁_int hδ₂_int hzero hloc hgrad hfinite hM₂ hf₀ hf₁ hShortMeas
    hδ₂_short_nonneg hShortLoc hShortGrad hMeanLoc hHeld δ₃ hδ₃_nonneg hBias
    hQueryInt c d hc hd hQueryGrad a b hBound ε hε
  dsimp only at hTails
  have hMargin := modelSelection_actual_wrongSign_margin_event_subset_all_dimensions
    μ T₀ T₁ L hf₀ hf₁ ε
  change {D | ε < |R D| ∧ E D * R D ≤ 0} ⊆
    {D | ε < |R D - E D|} at hMargin
  have hDeviation : {D | ε < |R D - E D|} ⊆
      {D | R D - E D > ε} ∪ {D | E D - R D > ε} := by
    intro D hD
    change ε < |R D - E D| at hD
    by_cases hPlus : R D - E D > ε
    · exact Or.inl hPlus
    · right
      by_contra hMinus
      have hPlusLe : R D - E D ≤ ε := le_of_not_gt hPlus
      have hMinusLe : E D - R D ≤ ε := le_of_not_gt hMinus
      have hAbsLe : |R D - E D| ≤ ε :=
        (abs_le).2 ⟨by linarith, hPlusLe⟩
      exact (not_lt_of_ge hAbsLe) hD
  have hSubset := hMargin.trans hDeviation
  change P.real {D | ε < |R D| ∧ E D * R D ≤ 0} ≤
    2 * (θ₁ + θ₂ + θ₃)
  calc
    P.real {D | ε < |R D| ∧ E D * R D ≤ 0} ≤
        P.real ({D | R D - E D > ε} ∪ {D | E D - R D > ε}) :=
      measureReal_mono hSubset (measure_ne_top P _)
    _ ≤ P.real {D | R D - E D > ε} + P.real {D | E D - R D > ε} :=
      measureReal_union_le _ _
    _ ≤ (θ₁ + θ₂ + θ₃) + (θ₁ + θ₂ + θ₃) :=
      add_le_add hTails.1 hTails.2
    _ = 2 * (θ₁ + θ₂ + θ₃) := by ring


end LOOConcentration.Manuscript.Internal
