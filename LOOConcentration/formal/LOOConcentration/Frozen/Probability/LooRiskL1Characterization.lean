import LOOConcentration.Frozen.Probability.LooRiskL1
import LOOConcentration.Probability.ProductConditionalRisk

/-!
Source: `LOOConcentration/v3/BeLa-LOOConcentration-referee-revision.tex`, lines 247–257.
The conditional-risk definition, characterization, and uniqueness theorem
form one audited semantic unit.
-/

set_option autoImplicit false

namespace LOOConcentration

open MeasureTheory

theorem looRiskL1_characterization {k m n : ℕ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (T : Estimator (k + 1) (m + 1) (n + 2))
    (L : Responses (m + 1) → Responses (m + 1) → ℝ)
    (hf : Integrable
      (fun p : Dataset (Observation (k + 1) (m + 1)) (n + 2) ×
        Observation (k + 1) (m + 1) => fittedLoss T L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ))
    :
    ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ)[
      (fun p : Dataset (Observation (k + 1) (m + 1)) (n + 2) ×
        Observation (k + 1) (m + 1) => fittedLoss T L p.1 p.2) |
        MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[
          ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ)]
      fun p => (looRiskL1 μ T L hf) p.1 := by
  have hsource := condExp_fst_prod_eq_integral_test_of_integrable
    (Measure.pi fun _ : Fin (n + 2) => μ) μ
    (fun p : Dataset (Observation (k + 1) (m + 1)) (n + 2) ×
      Observation (k + 1) (m + 1) => fittedLoss T L p.1 p.2) hf
  have hclass :
      (fun D => (looRiskL1 μ T L hf) D) =ᵐ[
        Measure.pi fun _ : Fin (n + 2) => μ]
        (fun D => ∫ z, fittedLoss T L D z ∂μ) := by
    exact (hf.integral_prod_left).coeFn_toL1
  have hp := (Measure.quasiMeasurePreserving_fst
    (μ := Measure.pi fun _ : Fin (n + 2) => μ) (ν := μ)).ae_eq_comp hclass
  exact hsource.trans (by simpa only [Function.comp_def] using hp.symm)

end LOOConcentration
