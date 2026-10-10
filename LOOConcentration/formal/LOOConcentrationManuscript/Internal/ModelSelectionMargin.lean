import LOOConcentrationRevision.Frozen.Definitions.LooRiskL1
import Mathlib.MeasureTheory.Measure.Real

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal
open MeasureTheory

/-- A wrong sign or tie at a strict true margin forces a strict deviation. -/
theorem wrong_sign_strict_margin_lt_abs_error (risk estimate ε : ℝ)
    (hmargin : ε < |risk|) (hsign : estimate * risk ≤ 0) :
    ε < |risk - estimate| := by
  have hsquare : risk ^ 2 ≤ (risk - estimate) ^ 2 := by
    nlinarith [sq_nonneg estimate]
  have habs : |risk| ≤ |risk - estimate| := by
    apply (sq_le_sq₀ (abs_nonneg risk) (abs_nonneg (risk - estimate))).mp
    simpa only [sq_abs] using hsquare
  exact hmargin.trans_le habs

/-- The actual two-procedure conditional-risk margin event is contained in the
actual deviation event. Both procedures share the observation law, dataset,
loss, and ordered deletion convention. No tail estimate is assumed here. -/
theorem model_selection_actual_wrong_sign_event_subset {k m n : ℕ}
    (μ : Measure (LOOConcentration.Observation (k + 1) (m + 1)))
    [IsProbabilityMeasure μ]
    (T₀ T₁ : ∀ r : ℕ, LOOConcentration.Estimator (k + 1) (m + 1) (r + 1))
    (L : LOOConcentration.Responses (m + 1) → LOOConcentration.Responses (m + 1) → ℝ)
    (hf₀ : Integrable
      (fun p : LOOConcentration.Dataset (LOOConcentration.Observation (k + 1) (m + 1))
          (n + 2) × LOOConcentration.Observation (k + 1) (m + 1) =>
        LOOConcentration.fittedLoss (T₀ (n + 1)) L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ))
    (hf₁ : Integrable
      (fun p : LOOConcentration.Dataset (LOOConcentration.Observation (k + 1) (m + 1))
          (n + 2) × LOOConcentration.Observation (k + 1) (m + 1) =>
        LOOConcentration.fittedLoss (T₁ (n + 1)) L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ)) (ε : ℝ) :
    let R := fun D =>
      (LOOConcentration.Revision.looRiskL1 μ (T₀ (n + 1)) L hf₀) D -
      (LOOConcentration.Revision.looRiskL1 μ (T₁ (n + 1)) L hf₁) D
    let E := fun D => LOOConcentration.looEstimate (T₀ n) L D -
      LOOConcentration.looEstimate (T₁ n) L D
    {D | ε < |R D| ∧ E D * R D ≤ 0} ⊆ {D | ε < |R D - E D|} := by
  dsimp only
  intro D hD
  exact wrong_sign_strict_margin_lt_abs_error _ _ ε hD.1 hD.2

/-- Probability comparison for the actual model-selection event under the same
ordered sample law. This is the event step consumed by a difference-tail proof. -/
theorem model_selection_actual_wrong_sign_probability_le_deviation {k m n : ℕ}
    (μ : Measure (LOOConcentration.Observation (k + 1) (m + 1)))
    [IsProbabilityMeasure μ]
    (T₀ T₁ : ∀ r : ℕ, LOOConcentration.Estimator (k + 1) (m + 1) (r + 1))
    (L : LOOConcentration.Responses (m + 1) → LOOConcentration.Responses (m + 1) → ℝ)
    (hf₀ : Integrable
      (fun p : LOOConcentration.Dataset (LOOConcentration.Observation (k + 1) (m + 1))
          (n + 2) × LOOConcentration.Observation (k + 1) (m + 1) =>
        LOOConcentration.fittedLoss (T₀ (n + 1)) L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ))
    (hf₁ : Integrable
      (fun p : LOOConcentration.Dataset (LOOConcentration.Observation (k + 1) (m + 1))
          (n + 2) × LOOConcentration.Observation (k + 1) (m + 1) =>
        LOOConcentration.fittedLoss (T₁ (n + 1)) L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ)) (ε : ℝ) :
    let R := fun D =>
      (LOOConcentration.Revision.looRiskL1 μ (T₀ (n + 1)) L hf₀) D -
      (LOOConcentration.Revision.looRiskL1 μ (T₁ (n + 1)) L hf₁) D
    let E := fun D => LOOConcentration.looEstimate (T₀ n) L D -
      LOOConcentration.looEstimate (T₁ n) L D
    (Measure.pi fun _ : Fin (n + 2) => μ).real {D | ε < |R D| ∧ E D * R D ≤ 0} ≤
      (Measure.pi fun _ : Fin (n + 2) => μ).real {D | ε < |R D - E D|} := by
  exact measureReal_mono
    (model_selection_actual_wrong_sign_event_subset μ T₀ T₁ L hf₀ hf₁ ε)
    (measure_ne_top (Measure.pi fun _ : Fin (n + 2) => μ) _)

end LOOConcentration.Manuscript.Internal
