import LOOConcentrationManuscript.Internal.ModelSelectionRiskSubtractionAllDimensionsConsumer
import LOOConcentrationRevision.Concentration.DataDependentClassAssembly

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal
open MeasureTheory
open scoped ENNReal

/-- The actual two-procedure error consumes the independently certified conditioned assembly on the
original law and norm; a wrong sign at a strict true margin obeys the same tail. -/
theorem model_selection_conditioned_tails_and_wrong_sign_all_dimensions {k m n : ℕ}
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
  have h := LOOConcentration.Revision.dataDependentConcentration_class_assembly μ hlsi hsecond
    (fun D : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 2) =>
      (LOOConcentration.Revision.looRiskL1 μ (T₀ (n + 1)) L hf₀) D -
      (LOOConcentration.Revision.looRiskL1 μ (T₁ (n + 1)) L hf₁) D -
      (LOOConcentration.looEstimate (T₀ n) L D - LOOConcentration.looEstimate (T₁ n) L D)) hH B δ L_K hL2 hbias K hK hKpos hLip
  dsimp only
  intro ε hε
  have htails := h ε hε
  refine ⟨htails.1, htails.2.1, htails.2.2, ?_⟩
  exact (measureReal_mono
    (modelSelection_actual_wrongSign_margin_event_subset_all_dimensions
      μ T₀ T₁ L hf₀ hf₁ ε) (measure_ne_top (Measure.pi fun _ : Fin (n + 2) => μ) _)).trans htails.2.2

end LOOConcentration.Manuscript.Internal
