import LOOConcentrationManuscript.Internal.ModelSelectionRiskSubtractionAllDimensions

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal

open MeasureTheory

/-- The actual conditional-risk difference minus the actual LOO-estimate
difference is almost everywhere the full-fit signed test risk minus the
finite average of the deleted-fit signed losses. -/
theorem modelSelection_actual_riskMinusLoo_ae_eq_all_dimensions {k m n : ℕ}
    (μ : Measure (LOOConcentration.Observation k m))
    [IsProbabilityMeasure μ]
    (T₀ T₁ : ∀ r : ℕ,
      LOOConcentration.Estimator k m (r + 1))
    (L : LOOConcentration.Responses m →
      LOOConcentration.Responses m → ℝ)
    (hf₀ : Integrable
      (fun p : LOOConcentration.Dataset
          (LOOConcentration.Observation k m) (n + 2) ×
          LOOConcentration.Observation k m =>
        LOOConcentration.fittedLoss (T₀ (n + 1)) L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ))
    (hf₁ : Integrable
      (fun p : LOOConcentration.Dataset
          (LOOConcentration.Observation k m) (n + 2) ×
          LOOConcentration.Observation k m =>
        LOOConcentration.fittedLoss (T₁ (n + 1)) L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ)) :
    (fun D : LOOConcentration.Dataset
        (LOOConcentration.Observation k m) (n + 2) =>
      ((LOOConcentration.Revision.looRiskL1 μ (T₀ (n + 1)) L hf₀) D -
        (LOOConcentration.Revision.looRiskL1 μ (T₁ (n + 1)) L hf₁) D) -
        (LOOConcentration.looEstimate (T₀ n) L D -
          LOOConcentration.looEstimate (T₁ n) L D)) =ᵐ[
            Measure.pi fun _ : Fin (n + 2) => μ]
    (fun D =>
      (∫ z,
        (LOOConcentration.fittedLoss (T₀ (n + 1)) L D z -
          LOOConcentration.fittedLoss (T₁ (n + 1)) L D z) ∂μ) -
      ((∑ i : Fin (n + 2),
        (LOOConcentration.fittedLoss (T₀ n) L
            (LOOConcentration.deleteAt D i) (D i) -
          LOOConcentration.fittedLoss (T₁ n) L
            (LOOConcentration.deleteAt D i) (D i))) / (n + 2 : ℝ))) := by
  have hrisk := modelSelection_riskDifference_ae_eq_integral_all_dimensions μ T₀ T₁ L hf₀ hf₁
  filter_upwards [hrisk] with D hD
  have hloo := modelSelection_looEstimate_sub_all_dimensions T₀ T₁ L D
  rw [hD, hloo]

/-- On the original sample law, a wrong sign or a tie at a strict actual
conditional-risk margin forces a strict deviation of the actual LOO difference.
This is the event implication used before applying a difference concentration
bound; it makes no tail claim. -/
theorem modelSelection_actual_wrongSign_margin_event_subset_all_dimensions {k m n : ℕ}
    (μ : Measure (LOOConcentration.Observation k m))
    [IsProbabilityMeasure μ]
    (T₀ T₁ : ∀ r : ℕ,
      LOOConcentration.Estimator k m (r + 1))
    (L : LOOConcentration.Responses m →
      LOOConcentration.Responses m → ℝ)
    (hf₀ : Integrable
      (fun p : LOOConcentration.Dataset
          (LOOConcentration.Observation k m) (n + 2) ×
          LOOConcentration.Observation k m =>
        LOOConcentration.fittedLoss (T₀ (n + 1)) L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ))
    (hf₁ : Integrable
      (fun p : LOOConcentration.Dataset
          (LOOConcentration.Observation k m) (n + 2) ×
          LOOConcentration.Observation k m =>
        LOOConcentration.fittedLoss (T₁ (n + 1)) L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ)) (ε : ℝ) :
    let R := fun D : LOOConcentration.Dataset
        (LOOConcentration.Observation k m) (n + 2) =>
      (LOOConcentration.Revision.looRiskL1 μ (T₀ (n + 1)) L hf₀) D -
        (LOOConcentration.Revision.looRiskL1 μ (T₁ (n + 1)) L hf₁) D
    let E := fun D : LOOConcentration.Dataset
        (LOOConcentration.Observation k m) (n + 2) =>
      LOOConcentration.looEstimate (T₀ n) L D -
        LOOConcentration.looEstimate (T₁ n) L D
    {D | ε < |R D| ∧ E D * R D ≤ 0} ⊆ {D | ε < |R D - E D|} := by
  dsimp only
  intro D hD
  have hsquare :
      ((LOOConcentration.Revision.looRiskL1 μ (T₀ (n + 1)) L hf₀) D -
        (LOOConcentration.Revision.looRiskL1 μ (T₁ (n + 1)) L hf₁) D) ^ 2 ≤
      (((LOOConcentration.Revision.looRiskL1 μ (T₀ (n + 1)) L hf₀) D -
        (LOOConcentration.Revision.looRiskL1 μ (T₁ (n + 1)) L hf₁) D) -
        (LOOConcentration.looEstimate (T₀ n) L D -
          LOOConcentration.looEstimate (T₁ n) L D)) ^ 2 := by
    nlinarith [sq_nonneg
      (LOOConcentration.looEstimate (T₀ n) L D -
        LOOConcentration.looEstimate (T₁ n) L D), hD.2]
  have habs :
      |(LOOConcentration.Revision.looRiskL1 μ (T₀ (n + 1)) L hf₀) D -
        (LOOConcentration.Revision.looRiskL1 μ (T₁ (n + 1)) L hf₁) D| ≤
      |((LOOConcentration.Revision.looRiskL1 μ (T₀ (n + 1)) L hf₀) D -
        (LOOConcentration.Revision.looRiskL1 μ (T₁ (n + 1)) L hf₁) D) -
        (LOOConcentration.looEstimate (T₀ n) L D -
          LOOConcentration.looEstimate (T₁ n) L D)| := by
    apply (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mp
    simpa only [sq_abs] using hsquare
  exact hD.1.trans_le habs

/-- The full signed error vanishes almost everywhere on the original zero-response
carrier, including zero feature dimension and the minimum full sample size. -/
theorem modelSelection_actual_riskMinusLoo_zero_response_all_dimensions {k n : ℕ}
    (μ : Measure (LOOConcentration.Observation k 0))
    [IsProbabilityMeasure μ]
    (T₀ T₁ : ∀ r : ℕ,
      LOOConcentration.Estimator k 0 (r + 1))
    (L : LOOConcentration.Responses 0 →
      LOOConcentration.Responses 0 → ℝ)
    (hf₀ : Integrable
      (fun p : LOOConcentration.Dataset
          (LOOConcentration.Observation k 0) (n + 2) ×
          LOOConcentration.Observation k 0 =>
        LOOConcentration.fittedLoss (T₀ (n + 1)) L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ))
    (hf₁ : Integrable
      (fun p : LOOConcentration.Dataset
          (LOOConcentration.Observation k 0) (n + 2) ×
          LOOConcentration.Observation k 0 =>
        LOOConcentration.fittedLoss (T₁ (n + 1)) L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ)) :
    (fun D : LOOConcentration.Dataset
        (LOOConcentration.Observation k 0) (n + 2) =>
      ((LOOConcentration.Revision.looRiskL1 μ (T₀ (n + 1)) L hf₀) D -
        (LOOConcentration.Revision.looRiskL1 μ (T₁ (n + 1)) L hf₁) D) -
        (LOOConcentration.looEstimate (T₀ n) L D -
          LOOConcentration.looEstimate (T₁ n) L D)) =ᵐ[
            Measure.pi fun _ : Fin (n + 2) => μ]
    (fun _ => 0) := by
  have h := modelSelection_actual_riskMinusLoo_ae_eq_all_dimensions μ T₀ T₁ L hf₀ hf₁
  filter_upwards [h] with D hD
  rw [hD]
  simp only [modelSelection_signed_fittedLoss_zero_response_all_dimensions,
    integral_zero, Finset.sum_const_zero, zero_div, sub_zero]

end LOOConcentration.Manuscript.Internal
