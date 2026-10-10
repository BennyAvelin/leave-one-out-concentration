import LOOConcentration.Frozen.Foundations.FittedLoss
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Pi

/-!
Source: `LOOConcentration/v3/BeLa-LOOConcentration-referee-revision.tex`, lines 247–257.
The conditional-risk definition, characterization, and uniqueness theorem
form one audited semantic unit.
-/

set_option autoImplicit false

namespace LOOConcentration

open MeasureTheory

noncomputable def looRiskL1 {k m n : ℕ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (T : Estimator (k + 1) (m + 1) (n + 2))
    (L : Responses (m + 1) → Responses (m + 1) → ℝ)
    (hf : Integrable
      (fun p : Dataset (Observation (k + 1) (m + 1)) (n + 2) ×
        Observation (k + 1) (m + 1) => fittedLoss T L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ)) :
    Dataset (Observation (k + 1) (m + 1)) (n + 2) →₁[
      Measure.pi fun _ : Fin (n + 2) => μ] ℝ :=
  (hf.integral_prod_left).toL1
    (fun D => ∫ z, fittedLoss T L D z ∂μ)

end LOOConcentration
