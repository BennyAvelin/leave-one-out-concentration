import LOOConcentrationManuscript.Internal.ModelSelectionSignedShortCenteringConsumer
import LOOConcentrationManuscript.Internal.ModelSelectionSignedFullRiskMean
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal
open MeasureTheory LOOConcentration

/-- The actual signed conditional-risk error has the manuscript's three
centered terms and one bounded bias. The original held-out expectations give
both the short-product integrability and the bias internally. The two full
component L¹ witnesses are only the domains of the actual conditional risks. -/
theorem modelSelection_actual_signed_bias_decomposition {k m n : ℕ}
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T₀ T₁ : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (hf₀ : Integrable
      (fun p : Dataset (Observation k m) (n + 2) × Observation k m =>
        fittedLoss (T₀ (n + 1)) L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ))
    (hf₁ : Integrable
      (fun p : Dataset (Observation k m) (n + 2) × Observation k m =>
        fittedLoss (T₁ (n + 1)) L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ))
    (hMeas : Measurable (fun p : Dataset (Observation k m) (n + 1) ×
        Observation k m => fittedLoss (T₀ n) L p.1 p.2 -
          fittedLoss (T₁ n) L p.1 p.2))
    (hHeld : ∀ i : Fin (n + 2),
      Integrable (fun D : Dataset (Observation k m) (n + 2) =>
        fittedLoss (T₀ n) L (deleteAt D i) (D i) -
          fittedLoss (T₁ n) L (deleteAt D i) (D i))
        (Measure.pi fun _ : Fin (n + 2) => μ))
    (δ₃ : ℝ)
    (hBias : ∀ i : Fin (n + 2),
      |(∫ D : Dataset (Observation k m) (n + 2),
          (fittedLoss (T₀ n) L (deleteAt D i) (D i) -
            fittedLoss (T₁ n) L (deleteAt D i) (D i))
          ∂Measure.pi fun _ : Fin (n + 2) => μ) -
        (∫ p : Dataset (Observation k m) (n + 2) × Observation k m,
          (fittedLoss (T₀ (n + 1)) L p.1 p.2 -
            fittedLoss (T₁ (n + 1)) L p.1 p.2)
          ∂(Measure.pi fun _ : Fin (n + 2) => μ).prod μ)| ≤ δ₃) :
    let P : Measure (Dataset (Observation k m) (n + 2)) :=
      Measure.pi fun _ : Fin (n + 2) => μ
    let Q : Measure (Dataset (Observation k m) (n + 1)) :=
      Measure.pi fun _ : Fin (n + 1) => μ
    let f : Observation k m → ℝ := fun z => ∫ D,
      (fittedLoss (T₀ n) L D z - fittedLoss (T₁ n) L D z) ∂Q
    let V : Dataset (Observation k m) (n + 2) → ℝ :=
      fun D => (∑ i : Fin (n + 2), f (D i)) / (n + 2 : ℝ)
    let E : Dataset (Observation k m) (n + 2) → ℝ :=
      fun D => looEstimate (T₀ n) L D - looEstimate (T₁ n) L D
    let R : Dataset (Observation k m) (n + 2) → ℝ :=
      fun D => Revision.looRiskL1 μ (T₀ (n + 1)) L hf₀ D -
        Revision.looRiskL1 μ (T₁ (n + 1)) L hf₁ D
    let I₁ := fun D => V D - E D
    let I₂ := fun D => (∫ E, V E ∂P) - V D
    let I₃ := fun D => R D - ∫ E, R E ∂P
    let bias := (∫ D, R D ∂P) - ∫ D, V D ∂P
    Integrable R P ∧ Integrable E P ∧ Integrable V P ∧
      Integrable I₁ P ∧ Integrable I₂ P ∧ Integrable I₃ P ∧
      (∫ D, I₁ D ∂P) = 0 ∧ (∫ D, I₂ D ∂P) = 0 ∧
      (∫ D, I₃ D ∂P) = 0 ∧ |bias| ≤ δ₃ ∧
      (∀ D, R D - E D = I₁ D + I₂ D + I₃ D + bias) ∧
      (∀ D, E D - R D = -I₁ D + -I₂ D + -I₃ D - bias) := by
  dsimp only
  let P : Measure (Dataset (Observation k m) (n + 2)) :=
    Measure.pi fun _ : Fin (n + 2) => μ
  let Q : Measure (Dataset (Observation k m) (n + 1)) :=
    Measure.pi fun _ : Fin (n + 1) => μ
  let F : Dataset (Observation k m) (n + 1) × Observation k m → ℝ :=
    fun p => fittedLoss (T₀ n) L p.1 p.2 - fittedLoss (T₁ n) L p.1 p.2
  let Ffull : Dataset (Observation k m) (n + 2) × Observation k m → ℝ :=
    fun p => fittedLoss (T₀ (n + 1)) L p.1 p.2 -
      fittedLoss (T₁ (n + 1)) L p.1 p.2
  let f : Observation k m → ℝ := fun z => ∫ D, F (D, z) ∂Q
  let V : Dataset (Observation k m) (n + 2) → ℝ :=
    fun D => (∑ i : Fin (n + 2), f (D i)) / (n + 2 : ℝ)
  let E : Dataset (Observation k m) (n + 2) → ℝ :=
    fun D => looEstimate (T₀ n) L D - looEstimate (T₁ n) L D
  let R : Dataset (Observation k m) (n + 2) → ℝ :=
    fun D => Revision.looRiskL1 μ (T₀ (n + 1)) L hf₀ D -
      Revision.looRiskL1 μ (T₁ (n + 1)) L hf₁ D
  have hs := modelSelection_actual_signed_short_centering μ T₀ T₁ L hMeas hHeld
  have hr := modelSelection_actual_signed_full_risk_mean μ T₀ T₁ L hf₀ hf₁
  dsimp only at hs hr
  have hV : Integrable V P := hs.2.2.1
  have hR : Integrable R P := hr.1
  have hI₂ : Integrable (fun D => (∫ E, V E ∂P) - V D) P :=
    (integrable_const _).sub hV
  have hI₂zero : (∫ D, ((∫ E, V E ∂P) - V D) ∂P) = 0 := by
    rw [integral_sub (integrable_const _) hV]
    simp only [integral_const, probReal_univ, one_smul, sub_self]
  let i : Fin (n + 2) := ⟨0, by omega⟩
  have hshortMean : (∫ D, F (deleteAt D i, D i) ∂P) =
      ∫ p, F p ∂(Q.prod μ) := deleted_section_integral μ i F hs.1
  have hBound : |(∫ D, R D ∂P) - ∫ D, V D ∂P| ≤ δ₃ := by
    have hi : |(∫ D, F (deleteAt D i, D i) ∂P) -
        ∫ p, Ffull p ∂(P.prod μ)| ≤ δ₃ := hBias i
    rw [hshortMean] at hi
    have hER : (∫ D, R D ∂P) = ∫ p, Ffull p ∂(P.prod μ) := hr.2.1
    have hEV : (∫ D, V D ∂P) = ∫ p, F p ∂(Q.prod μ) := hs.2.2.2.2.2.1
    rw [hER, hEV, abs_sub_comm]
    exact hi
  refine ⟨hR, hs.2.2.2.1, hV, hs.2.2.2.2.1, hI₂, hr.2.2.1,
    hs.2.2.2.2.2.2.2, hI₂zero, hr.2.2.2, hBound, ?_, ?_⟩
  · intro D
    ring
  · intro D
    ring

end LOOConcentration.Manuscript.Internal
