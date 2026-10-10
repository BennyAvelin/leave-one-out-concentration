import LOOConcentrationManuscript.Internal.ModelSelectionConditionedAllDimensions

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript
open MeasureTheory Filter
open LOOConcentration.Revision LOOConcentration.Manuscript.Internal
open scoped Gradient Topology ENNReal

theorem modelSelection_conditioned_concentration_and_sign {k m n : ℕ}
    (μ : Measure (LOOConcentration.Observation k m))
    [IsProbabilityMeasure μ]
    (T₀ T₁ : ∀ r : ℕ, LOOConcentration.Estimator k m (r + 1))
    (L : LOOConcentration.Responses m → LOOConcentration.Responses m → ℝ)
    (hf₀ : Integrable
      (fun p : LOOConcentration.Dataset (LOOConcentration.Observation k m)
          (n + 2) × LOOConcentration.Observation k m =>
        LOOConcentration.fittedLoss (T₀ (n + 1)) L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ))
    (hf₁ : Integrable
      (fun p : LOOConcentration.Dataset (LOOConcentration.Observation k m)
          (n + 2) × LOOConcentration.Observation k m =>
        LOOConcentration.fittedLoss (T₁ (n + 1)) L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ))
    (hlsi : LOOConcentration.Revision.observationLogSobolevConstant μ < ⊤)
    (hsecond : Integrable LOOConcentration.observationNormSq μ)
    (hH : Measurable (fun D : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 2) =>
      (LOOConcentration.Revision.looRiskL1 μ (T₀ (n + 1)) L hf₀) D -
      (LOOConcentration.Revision.looRiskL1 μ (T₁ (n + 1)) L hf₁) D -
      (LOOConcentration.looEstimate (T₀ n) L D - LOOConcentration.looEstimate (T₁ n) L D)))
    (B δ L_K : NNReal)
    (hL2 : eLpNorm (fun D : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 2) =>
      (LOOConcentration.Revision.looRiskL1 μ (T₀ (n + 1)) L hf₀) D -
      (LOOConcentration.Revision.looRiskL1 μ (T₁ (n + 1)) L hf₁) D -
      (LOOConcentration.looEstimate (T₀ n) L D - LOOConcentration.looEstimate (T₁ n) L D)) 2 (Measure.pi fun _ : Fin (n + 2) => μ) ≤ (B : ℝ≥0∞))
    (hbias : |∫ D, (fun D : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 2) =>
      (LOOConcentration.Revision.looRiskL1 μ (T₀ (n + 1)) L hf₀) D -
      (LOOConcentration.Revision.looRiskL1 μ (T₁ (n + 1)) L hf₁) D -
      (LOOConcentration.looEstimate (T₀ n) L D - LOOConcentration.looEstimate (T₁ n) L D)) D ∂Measure.pi fun _ : Fin (n + 2) => μ| ≤ (δ : ℝ))
    (K : Set (LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 2)))
    (hK : MeasurableSet K) (hKpos : 0 < (Measure.pi fun _ : Fin (n + 2) => μ) K)
    (hLip : ∀ D ∈ K, ∀ E ∈ K, |(fun D : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 2) =>
      (LOOConcentration.Revision.looRiskL1 μ (T₀ (n + 1)) L hf₀) D -
      (LOOConcentration.Revision.looRiskL1 μ (T₁ (n + 1)) L hf₁) D -
      (LOOConcentration.looEstimate (T₀ n) L D - LOOConcentration.looEstimate (T₁ n) L D)) D - (fun D : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 2) =>
      (LOOConcentration.Revision.looRiskL1 μ (T₀ (n + 1)) L hf₀) D -
      (LOOConcentration.Revision.looRiskL1 μ (T₁ (n + 1)) L hf₁) D -
      (LOOConcentration.looEstimate (T₀ n) L D - LOOConcentration.looEstimate (T₁ n) L D)) E| ≤
      (L_K : ℝ) * LOOConcentration.datasetNorm (D - E)) :
    let R := fun D =>
      (LOOConcentration.Revision.looRiskL1 μ (T₀ (n + 1)) L hf₀) D -
      (LOOConcentration.Revision.looRiskL1 μ (T₁ (n + 1)) L hf₁) D
    let E := fun D => LOOConcentration.looEstimate (T₀ n) L D -
      LOOConcentration.looEstimate (T₁ n) L D
    let H := fun D => R D - E D
    let ν := Measure.pi fun _ : Fin (n + 2) => μ
    let p := ν.real Kᶜ
    let C := (LOOConcentration.Revision.observationLogSobolevConstant μ).toReal
    let cBNT := 3 * (2 : ℝ) ^ 12 * Real.exp 2
    let C_K := cBNT * C * Real.log (Real.exp 1 / (1 - p))
    let η_K := (B : ℝ) * Real.sqrt (p / (1 - p))
    ∀ (ε : ℝ) (_hε : (δ : ℝ) + η_K < ε),
      let G := if C_K * (L_K : ℝ) ^ 2 = 0 then 0 else
        Real.exp (-((ε - (δ : ℝ) - η_K) ^ 2 / (2 * C_K * (L_K : ℝ) ^ 2)))
      ν.real {D | H D > ε} ≤ p + G ∧
      ν.real {D | -H D > ε} ≤ p + G ∧
      ν.real {D | |H D| > ε} ≤ p + 2 * G ∧
      ν.real {D | ε < |R D| ∧ E D * R D ≤ 0} ≤ p + 2 * G := by
  exact @LOOConcentration.Manuscript.Internal.model_selection_conditioned_tails_and_wrong_sign_all_dimensions
    k m n μ (inferInstance : IsProbabilityMeasure μ) T₀ T₁ L hf₀ hf₁ hlsi hsecond hH B δ L_K hL2 hbias K hK hKpos hLip

end LOOConcentration.Manuscript
