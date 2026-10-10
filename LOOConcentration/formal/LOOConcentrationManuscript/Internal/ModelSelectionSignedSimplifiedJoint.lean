import LOOConcentrationManuscript.Internal.ModelSelectionSignedSimplified
import LOOConcentrationManuscript.Internal.ModelSelectionRiskSubtractionAllDimensionsConsumer

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
section ActualSignedSimplifiedJoint

variable {k m n : ℕ}
variable (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
variable (T₀ T₁ : ∀ r : ℕ, Estimator k m (r + 1))
variable (L : Responses m → Responses m → ℝ)
variable (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℝ)
variable (hδ₃_nonneg : 0 ≤ δ₃)
variable (hFullMeas : Measurable (fun p : Dataset (Observation k m) (n + 2) ×
  Observation k m => fittedLoss (T₀ (n + 1)) L p.1 p.2 -
    fittedLoss (T₁ (n + 1)) L p.1 p.2))
variable (hδ₁_full_nonneg : ∀ z, 0 ≤ δ₁ (n + 2) z)
variable (hδ₂_full_nonneg : ∀ z, 0 ≤ δ₂ (n + 2) z)
variable (hδ₁_full_int : Integrable (fun z => δ₁ (n + 2) z) μ)
variable (hδ₂_full_int : Integrable (fun z => δ₂ (n + 2) z) μ)
variable (hzero : Integrable (fun z =>
  fittedLoss (T₀ (n + 1)) L (0 : Dataset (Observation k m) (n + 2)) z -
    fittedLoss (T₁ (n + 1)) L (0 : Dataset (Observation k m) (n + 2)) z) μ)
variable (hFullLoc : ∀ᵐ z ∂μ, LocallyLipschitz (fun x : EuclideanSpace ℝ
  (DatasetCoordinate k m (n + 2)) =>
    fittedLoss (T₀ (n + 1)) L (Revision.datasetOfEuclidean x) z -
      fittedLoss (T₁ (n + 1)) L (Revision.datasetOfEuclidean x) z))
variable (hFullGrad : ∀ᵐ z ∂μ, ∀ᵐ x ∂(volume : Measure
  (EuclideanSpace ℝ (DatasetCoordinate k m (n + 2)))),
  DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (DatasetCoordinate k m (n + 2)) =>
    fittedLoss (T₀ (n + 1)) L (Revision.datasetOfEuclidean y) z -
      fittedLoss (T₁ (n + 1)) L (Revision.datasetOfEuclidean y) z) x ∧
  ‖gradient (fun y : EuclideanSpace ℝ (DatasetCoordinate k m (n + 2)) =>
    fittedLoss (T₀ (n + 1)) L (Revision.datasetOfEuclidean y) z -
      fittedLoss (T₁ (n + 1)) L (Revision.datasetOfEuclidean y) z) x‖ ≤
    δ₁ (n + 2) z + δ₂ (n + 2) z * ‖x‖)
variable (hfinite : observationLogSobolevConstant μ ≠ ⊤)
variable (hM₂ : Integrable observationNormSq μ)
variable (hf₀ : Integrable (fun p : Dataset (Observation k m) (n + 2) ×
  Observation k m => fittedLoss (T₀ (n + 1)) L p.1 p.2)
  ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ))
variable (hf₁ : Integrable (fun p : Dataset (Observation k m) (n + 2) ×
  Observation k m => fittedLoss (T₁ (n + 1)) L p.1 p.2)
  ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ))
variable (hShortMeas : Measurable (fun p : Dataset (Observation k m) (n + 1) ×
  Observation k m => fittedLoss (T₀ n) L p.1 p.2 - fittedLoss (T₁ n) L p.1 p.2))
variable (hδ₁_short_nonneg : ∀ z, 0 ≤ δ₁ (n + 1) z)
variable (hδ₁_short_int : Integrable (fun z => δ₁ (n + 1) z) μ)
variable (hShortLoc : ∀ᵐ z ∂μ, LocallyLipschitz (fun x : EuclideanSpace ℝ
  (DatasetCoordinate k m (n + 1)) =>
    fittedLoss (T₀ n) L (datasetOfEuclidean x) z - fittedLoss (T₁ n) L (datasetOfEuclidean x) z))
variable (hShortGrad : ∀ᵐ z ∂μ, ∀ᵐ x ∂(volume : Measure
  (EuclideanSpace ℝ (DatasetCoordinate k m (n + 1)))),
  DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (DatasetCoordinate k m (n + 1)) =>
    fittedLoss (T₀ n) L (datasetOfEuclidean y) z - fittedLoss (T₁ n) L (datasetOfEuclidean y) z) x ∧
  ‖gradient (fun y : EuclideanSpace ℝ (DatasetCoordinate k m (n + 1)) =>
    fittedLoss (T₀ n) L (datasetOfEuclidean y) z - fittedLoss (T₁ n) L (datasetOfEuclidean y) z) x‖ ≤
    δ₁ (n + 1) z + δ₂ (n + 1) z * ‖x‖)
variable (hHeld : ∀ i : Fin (n + 2),
  Integrable (fun D : Dataset (Observation k m) (n + 2) =>
    fittedLoss (T₀ n) L (deleteAt D i) (D i) -
      fittedLoss (T₁ n) L (deleteAt D i) (D i))
    (Measure.pi fun _ : Fin (n + 2) => μ))
variable (hBias : ∀ i : Fin (n + 2),
  |(∫ D : Dataset (Observation k m) (n + 2),
      (fittedLoss (T₀ n) L (deleteAt D i) (D i) -
        fittedLoss (T₁ n) L (deleteAt D i) (D i))
      ∂Measure.pi fun _ : Fin (n + 2) => μ) -
    (∫ p : Dataset (Observation k m) (n + 2) × Observation k m,
      (fittedLoss (T₀ (n + 1)) L p.1 p.2 -
        fittedLoss (T₁ (n + 1)) L p.1 p.2)
      ∂(Measure.pi fun _ : Fin (n + 2) => μ).prod μ)| ≤ δ₃)
variable (hQueryInt : ∀ z : Observation k m,
  Integrable (fun D : Dataset (Observation k m) (n + 1) =>
    fittedLoss (T₀ n) L D z - fittedLoss (T₁ n) L D z)
    (Measure.pi fun _ : Fin (n + 1) => μ))
variable (c : ℝ) (hc : 0 ≤ c)
variable (hQueryLip : LipschitzWith (NNReal.mk c hc)
  (modelSelectionSignedExpectedMeanQuery μ T₀ T₁ L hQueryInt))
variable (hδ₂_short_zero : ∀ z, δ₂ (n + 1) z = 0)
variable (hδ₂_full_zero : ∀ z, δ₂ (n + 2) z = 0)

include μ T₀ T₁ L δ₁ δ₂ δ₃ hδ₃_nonneg hFullMeas hδ₁_full_nonneg hδ₂_full_nonneg
  hδ₁_full_int hδ₂_full_int hzero hFullLoc hFullGrad hfinite hM₂ hf₀ hf₁ hShortMeas
  hδ₁_short_nonneg hδ₁_short_int hShortLoc hShortGrad
  hHeld hBias hQueryInt c hc hQueryLip hδ₂_short_zero hδ₂_full_zero

/-- Both signed simplified concentration formulas and their absolute-error and
wrong-sign consequences, using the same actual conditional risks and sample law. -/
theorem modelSelection_actual_signed_simplified_joint_tails_and_sign :
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
  dsimp only
  let P : Measure (Dataset (Observation k m) (n + 2)) := Measure.pi fun _ => μ
  let R : Dataset (Observation k m) (n + 2) → ℝ := fun D =>
    Revision.looRiskL1 μ (T₀ (n + 1)) L hf₀ D - Revision.looRiskL1 μ (T₁ (n + 1)) L hf₁ D
  let E : Dataset (Observation k m) (n + 2) → ℝ := fun D =>
    looEstimate (T₀ n) L D - looEstimate (T₁ n) L D
  let C := (observationLogSobolevConstant μ).toReal
  constructor
  · intro ε hε
    let t := (ε - δ₃) / 3
    let gaussian : ℝ → ℝ := fun v =>
      if v = 0 then 0 else Real.exp (-(t ^ 2 / (2 * v)))
    let Mix := (n + 2 : ℝ) * ∫ z, gaussian (C * (δ₁ (n + 1) z) ^ 2) ∂μ +
      gaussian (C * (c / Real.sqrt (n + 2 : ℝ)) ^ 2) +
      gaussian (C * (∫ z, δ₁ (n + 2) z ∂μ) ^ 2)
    have hTails := modelSelection_actual_signed_simplified_nonuniform_tails
      μ T₀ T₁ L δ₁ δ₂ δ₃ hδ₃_nonneg hFullMeas hδ₁_full_nonneg hδ₂_full_nonneg
      hδ₁_full_int hδ₂_full_int hzero hFullLoc hFullGrad hfinite hM₂ hf₀ hf₁ hShortMeas
      hδ₁_short_nonneg hδ₁_short_int hShortLoc hShortGrad hHeld hBias hQueryInt
      c hc hQueryLip hδ₂_short_zero hδ₂_full_zero ε hε
    dsimp only at hTails
    have hTails' : P.real {D | R D - E D > ε} ≤ Mix ∧
        P.real {D | E D - R D > ε} ≤ Mix := hTails
    have hSubset : {D | |R D - E D| > ε} ⊆
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
    have hAbs : P.real {D | |R D - E D| > ε} ≤ 2 * Mix := by
      calc
        P.real {D | |R D - E D| > ε} ≤
            P.real ({D | R D - E D > ε} ∪ {D | E D - R D > ε}) :=
          measureReal_mono hSubset (measure_ne_top P _)
        _ ≤ P.real {D | R D - E D > ε} + P.real {D | E D - R D > ε} :=
          measureReal_union_le _ _
        _ ≤ Mix + Mix := add_le_add hTails'.1 hTails'.2
        _ = 2 * Mix := by ring
    have hMargin := modelSelection_actual_wrongSign_margin_event_subset_all_dimensions
      μ T₀ T₁ L hf₀ hf₁ ε
    change {D | ε < |R D| ∧ E D * R D ≤ 0} ⊆ {D | |R D - E D| > ε} at hMargin
    exact ⟨hTails'.1, hTails'.2, hAbs,
      (measureReal_mono hMargin (measure_ne_top P _)).trans hAbs⟩
  · intro a ha t ht
    have hTails := modelSelection_actual_signed_simplified_uniform_tails
      μ T₀ T₁ L δ₁ δ₂ δ₃ hδ₃_nonneg hFullMeas hδ₁_full_nonneg hδ₂_full_nonneg
      hδ₁_full_int hδ₂_full_int hzero hFullLoc hFullGrad hfinite hM₂ hf₀ hf₁ hShortMeas
      hShortLoc hShortGrad hHeld hBias hQueryInt
      c hc hQueryLip hδ₂_short_zero hδ₂_full_zero a ha t ht
    dsimp only at hTails
    have hMargin := modelSelection_actual_wrongSign_margin_event_subset_all_dimensions
      μ T₀ T₁ L hf₀ hf₁ (δ₃ + t)
    change {D | δ₃ + t < |R D| ∧ E D * R D ≤ 0} ⊆
      {D | |R D - E D| > δ₃ + t} at hMargin
    exact ⟨hTails.1, hTails.2.1, hTails.2.2,
      (measureReal_mono hMargin (measure_ne_top P _)).trans hTails.2.2⟩

end ActualSignedSimplifiedJoint
end LOOConcentration.Manuscript.Internal
