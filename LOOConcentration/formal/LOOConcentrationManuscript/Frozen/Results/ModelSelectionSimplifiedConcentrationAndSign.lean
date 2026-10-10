import LOOConcentrationManuscript.Internal.ModelSelectionSignedSimplifiedJoint

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript
open MeasureTheory Filter
open LOOConcentration.Revision LOOConcentration.Manuscript.Internal
open scoped Gradient Topology ENNReal

theorem modelSelection_simplified_concentration_and_sign
    {k m n : ℕ}
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T₀ T₁ : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℝ)
    (hδ₃_nonneg : 0 ≤ δ₃)
    (hFullMeas : Measurable (fun p : Dataset (Observation k m) (n + 2) ×
  Observation k m => fittedLoss (T₀ (n + 1)) L p.1 p.2 -
    fittedLoss (T₁ (n + 1)) L p.1 p.2))
    (hδ₁_full_nonneg : ∀ z, 0 ≤ δ₁ (n + 2) z)
    (hδ₂_full_nonneg : ∀ z, 0 ≤ δ₂ (n + 2) z)
    (hδ₁_full_int : Integrable (fun z => δ₁ (n + 2) z) μ)
    (hδ₂_full_int : Integrable (fun z => δ₂ (n + 2) z) μ)
    (hzero : Integrable (fun z =>
  fittedLoss (T₀ (n + 1)) L (0 : Dataset (Observation k m) (n + 2)) z -
    fittedLoss (T₁ (n + 1)) L (0 : Dataset (Observation k m) (n + 2)) z) μ)
    (hFullLoc : ∀ᵐ z ∂μ, LocallyLipschitz (fun x : EuclideanSpace ℝ
  (DatasetCoordinate k m (n + 2)) =>
    fittedLoss (T₀ (n + 1)) L (Revision.datasetOfEuclidean x) z -
      fittedLoss (T₁ (n + 1)) L (Revision.datasetOfEuclidean x) z))
    (hFullGrad : ∀ᵐ z ∂μ, ∀ᵐ x ∂(volume : Measure
  (EuclideanSpace ℝ (DatasetCoordinate k m (n + 2)))),
  DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (DatasetCoordinate k m (n + 2)) =>
    fittedLoss (T₀ (n + 1)) L (Revision.datasetOfEuclidean y) z -
      fittedLoss (T₁ (n + 1)) L (Revision.datasetOfEuclidean y) z) x ∧
  ‖gradient (fun y : EuclideanSpace ℝ (DatasetCoordinate k m (n + 2)) =>
    fittedLoss (T₀ (n + 1)) L (Revision.datasetOfEuclidean y) z -
      fittedLoss (T₁ (n + 1)) L (Revision.datasetOfEuclidean y) z) x‖ ≤
    δ₁ (n + 2) z + δ₂ (n + 2) z * ‖x‖)
    (hfinite : observationLogSobolevConstant μ ≠ ⊤)
    (hM₂ : Integrable observationNormSq μ)
    (hf₀ : Integrable (fun p : Dataset (Observation k m) (n + 2) ×
  Observation k m => fittedLoss (T₀ (n + 1)) L p.1 p.2)
  ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ))
    (hf₁ : Integrable (fun p : Dataset (Observation k m) (n + 2) ×
  Observation k m => fittedLoss (T₁ (n + 1)) L p.1 p.2)
  ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ))
    (hShortMeas : Measurable (fun p : Dataset (Observation k m) (n + 1) ×
  Observation k m => fittedLoss (T₀ n) L p.1 p.2 - fittedLoss (T₁ n) L p.1 p.2))
    (hδ₁_short_nonneg : ∀ z, 0 ≤ δ₁ (n + 1) z)
    (hδ₁_short_int : Integrable (fun z => δ₁ (n + 1) z) μ)
    (hShortLoc : ∀ᵐ z ∂μ, LocallyLipschitz (fun x : EuclideanSpace ℝ
  (DatasetCoordinate k m (n + 1)) =>
    fittedLoss (T₀ n) L (datasetOfEuclidean x) z - fittedLoss (T₁ n) L (datasetOfEuclidean x) z))
    (hShortGrad : ∀ᵐ z ∂μ, ∀ᵐ x ∂(volume : Measure
  (EuclideanSpace ℝ (DatasetCoordinate k m (n + 1)))),
  DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (DatasetCoordinate k m (n + 1)) =>
    fittedLoss (T₀ n) L (datasetOfEuclidean y) z - fittedLoss (T₁ n) L (datasetOfEuclidean y) z) x ∧
  ‖gradient (fun y : EuclideanSpace ℝ (DatasetCoordinate k m (n + 1)) =>
    fittedLoss (T₀ n) L (datasetOfEuclidean y) z - fittedLoss (T₁ n) L (datasetOfEuclidean y) z) x‖ ≤
    δ₁ (n + 1) z + δ₂ (n + 1) z * ‖x‖)
    (hHeld : ∀ i : Fin (n + 2),
  Integrable (fun D : Dataset (Observation k m) (n + 2) =>
    fittedLoss (T₀ n) L (deleteAt D i) (D i) -
      fittedLoss (T₁ n) L (deleteAt D i) (D i))
    (Measure.pi fun _ : Fin (n + 2) => μ))
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
    (c : ℝ) (hc : 0 ≤ c)
    (hQueryLip : LipschitzWith (NNReal.mk c hc)
  (modelSelectionSignedExpectedMeanQuery μ T₀ T₁ L hQueryInt))
    (hδ₂_short_zero : ∀ z, δ₂ (n + 1) z = 0)
    (hδ₂_full_zero : ∀ z, δ₂ (n + 2) z = 0) :
    let P : Measure (Dataset (Observation k m) (n + 2)) := Measure.pi fun _ : Fin (n + 2) => μ
    let R : Dataset (Observation k m) (n + 2) → ℝ := fun D =>
      Revision.looRiskL1 μ (T₀ (n + 1)) L hf₀ D - Revision.looRiskL1 μ (T₁ (n + 1)) L hf₁ D
    let E : Dataset (Observation k m) (n + 2) → ℝ := fun D =>
      looEstimate (T₀ n) L D - looEstimate (T₁ n) L D
    let C := (observationLogSobolevConstant μ).toReal
    (∀ (ε : ℝ) (_hε : 3 * δ₃ < ε),
      let t := (ε - δ₃) / 3
      let gaussian : ℝ → ℝ := fun v =>
        if v = 0 then 0 else Real.exp (-(t ^ 2 / (2 * v)))
      let Mix := (n + 2 : ℝ) * ∫ z, gaussian (C * (δ₁ (n + 1) z) ^ 2) ∂μ +
        gaussian (C * (c / Real.sqrt (n + 2 : ℝ)) ^ 2) +
        gaussian (C * (∫ z, δ₁ (n + 2) z ∂μ) ^ 2)
      P.real {D | R D - E D > ε} ≤ Mix ∧
        P.real {D | E D - R D > ε} ≤ Mix ∧
          P.real {D | |R D - E D| > ε} ≤ 2 * Mix ∧
            P.real {D | ε < |R D| ∧ E D * R D ≤ 0} ≤ 2 * Mix) ∧
    (∀ (a : NNReal) (_ha : ∀ᵐ z ∂μ, δ₁ (n + 1) z ≤ (a : ℝ))
        (t : ℝ) (_ht : 0 < t),
      let scale := (a : ℝ) + c / Real.sqrt (n + 2 : ℝ) + ∫ z, δ₁ (n + 2) z ∂μ
      let K := C * scale ^ 2
      let gaussian := if K = 0 then 0 else Real.exp (-(t ^ 2 / (2 * K)))
      P.real {D | R D - E D > δ₃ + t} ≤ gaussian ∧
        P.real {D | E D - R D > δ₃ + t} ≤ gaussian ∧
          P.real {D | |R D - E D| > δ₃ + t} ≤ 2 * gaussian ∧
            P.real {D | δ₃ + t < |R D| ∧ E D * R D ≤ 0} ≤ 2 * gaussian) := by
  exact @LOOConcentration.Manuscript.Internal.modelSelection_actual_signed_simplified_joint_tails_and_sign
    k m n μ (inferInstance : IsProbabilityMeasure μ) T₀ T₁ L δ₁ δ₂ δ₃ hδ₃_nonneg hFullMeas hδ₁_full_nonneg hδ₂_full_nonneg hδ₁_full_int hδ₂_full_int hzero hFullLoc hFullGrad hfinite hM₂ hf₀ hf₁ hShortMeas hδ₁_short_nonneg hδ₁_short_int hShortLoc hShortGrad hHeld hBias hQueryInt c hc hQueryLip hδ₂_short_zero hδ₂_full_zero

end LOOConcentration.Manuscript
