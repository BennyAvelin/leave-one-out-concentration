import LOOConcentrationManuscript.Internal.ModelSelectionSignedShortCentering
import LOOConcentration.Frozen.Foundations.LooEstimate
import LOOConcentration.Frozen.Foundations.FittedLoss

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal

open MeasureTheory LOOConcentration

/-- The first actual signed LOO decomposition term is integrable and centered.
The original held-out hypotheses supply short-product integrability internally;
no per-component short-loss L¹ assumptions are introduced. -/
theorem modelSelection_actual_signed_short_centering {k m n : ℕ}
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T₀ T₁ : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (hMeas : Measurable (fun p : Dataset (Observation k m) (n + 1) ×
        Observation k m => fittedLoss (T₀ n) L p.1 p.2 -
          fittedLoss (T₁ n) L p.1 p.2))
    (hHeld : ∀ i : Fin (n + 2),
      Integrable (fun D : Dataset (Observation k m) (n + 2) =>
        fittedLoss (T₀ n) L (deleteAt D i) (D i) -
          fittedLoss (T₁ n) L (deleteAt D i) (D i))
        (Measure.pi fun _ : Fin (n + 2) => μ)) :
    let P : Measure (Dataset (Observation k m) (n + 2)) :=
      Measure.pi fun _ : Fin (n + 2) => μ
    let Q : Measure (Dataset (Observation k m) (n + 1)) :=
      Measure.pi fun _ : Fin (n + 1) => μ
    let F : Dataset (Observation k m) (n + 1) × Observation k m → ℝ :=
      fun p => fittedLoss (T₀ n) L p.1 p.2 - fittedLoss (T₁ n) L p.1 p.2
    let f : Observation k m → ℝ := fun z => ∫ D, F (D, z) ∂Q
    let V : Dataset (Observation k m) (n + 2) → ℝ :=
      fun D => (∑ i : Fin (n + 2), f (D i)) / (n + 2 : ℝ)
    let E : Dataset (Observation k m) (n + 2) → ℝ :=
      fun D => looEstimate (T₀ n) L D - looEstimate (T₁ n) L D
    Integrable F (Q.prod μ) ∧ Integrable f μ ∧ Integrable V P ∧
      Integrable E P ∧ Integrable (fun D => V D - E D) P ∧
      (∫ D, V D ∂P) = ∫ p, F p ∂(Q.prod μ) ∧
      (∫ D, E D ∂P) = ∫ p, F p ∂(Q.prod μ) ∧
      (∫ D, V D - E D ∂P) = 0 := by
  dsimp only
  let F : Dataset (Observation k m) (n + 1) × Observation k m → ℝ :=
    fun p => fittedLoss (T₀ n) L p.1 p.2 - fittedLoss (T₁ n) L p.1 p.2
  have h := modelSelection_signed_short_average_centering μ F hMeas hHeld
  dsimp only at h
  have hEeq (D : Dataset (Observation k m) (n + 2)) :
      (∑ i : Fin (n + 2), F (deleteAt D i, D i)) / (n + 2 : ℝ) =
        looEstimate (T₀ n) L D - looEstimate (T₁ n) L D := by
    unfold F fittedLoss looEstimate
    rw [Finset.sum_sub_distrib, sub_div]
  simpa only [hEeq, F] using h

end LOOConcentration.Manuscript.Internal
