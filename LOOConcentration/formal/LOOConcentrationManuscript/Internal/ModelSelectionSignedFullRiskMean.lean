import LOOConcentrationManuscript.Internal.ModelSelectionRiskSubtractionAllDimensions
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal

open MeasureTheory LOOConcentration

/-- The actual conditional-risk difference is integrable, and its expectation
is exactly the original full-sample signed-loss expectation. Its centered
representative is integrable with mean zero. The two full-loss L¹ witnesses
are the domains of the two actual conditional risks, not stability hypotheses
on the individual procedures. -/
theorem modelSelection_actual_signed_full_risk_mean {k m n : ℕ}
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
      ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ)) :
    let P : Measure (Dataset (Observation k m) (n + 2)) :=
      Measure.pi fun _ : Fin (n + 2) => μ
    let F : Dataset (Observation k m) (n + 2) × Observation k m → ℝ :=
      fun p => fittedLoss (T₀ (n + 1)) L p.1 p.2 -
        fittedLoss (T₁ (n + 1)) L p.1 p.2
    let R : Dataset (Observation k m) (n + 2) → ℝ :=
      fun D => Revision.looRiskL1 μ (T₀ (n + 1)) L hf₀ D -
        Revision.looRiskL1 μ (T₁ (n + 1)) L hf₁ D
    Integrable R P ∧
      (∫ D, R D ∂P) = (∫ p, F p ∂(P.prod μ)) ∧
      Integrable (fun D => R D - ∫ E, R E ∂P) P ∧
      (∫ D, (R D - ∫ E, R E ∂P) ∂P) = 0 := by
  dsimp only
  let P : Measure (Dataset (Observation k m) (n + 2)) :=
    Measure.pi fun _ : Fin (n + 2) => μ
  let F : Dataset (Observation k m) (n + 2) × Observation k m → ℝ :=
    fun p => fittedLoss (T₀ (n + 1)) L p.1 p.2 -
      fittedLoss (T₁ (n + 1)) L p.1 p.2
  let R : Dataset (Observation k m) (n + 2) → ℝ :=
    fun D => Revision.looRiskL1 μ (T₀ (n + 1)) L hf₀ D -
      Revision.looRiskL1 μ (T₁ (n + 1)) L hf₁ D
  have hR : Integrable R P :=
    (L1.integrable_coeFn (Revision.looRiskL1 μ (T₀ (n + 1)) L hf₀)).sub
      (L1.integrable_coeFn (Revision.looRiskL1 μ (T₁ (n + 1)) L hf₁))
  have hF : Integrable F (P.prod μ) := hf₀.sub hf₁
  have hAE : R =ᵐ[P] (fun D => ∫ z, F (D, z) ∂μ) :=
    modelSelection_riskDifference_ae_eq_integral_all_dimensions μ T₀ T₁ L hf₀ hf₁
  have hMean : (∫ D, R D ∂P) = ∫ p, F p ∂(P.prod μ) := by
    calc
      _ = ∫ D, (∫ z, F (D, z) ∂μ) ∂P := integral_congr_ae hAE
      _ = _ := (integral_prod F hF).symm
  refine ⟨hR, hMean, hR.sub (integrable_const _), ?_⟩
  change (∫ D, (R D - ∫ E, R E ∂P) ∂P) = 0
  rw [integral_sub hR (integrable_const _)]
  simp only [integral_const, probReal_univ, one_smul, sub_self]

end LOOConcentration.Manuscript.Internal
