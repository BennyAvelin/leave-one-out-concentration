import LOOConcentration.Frozen.Foundations.FittedLoss
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Expected fitted loss at one test point

Source: `LOOConcentration/v3/BeLa-LOOConcentration-referee-revision.tex`, lines 378–382.
The real expectation is defined only where its fitted-loss integrand is
integrable. Global expected-loss assertions must provide that condition at
every test point or use an author-approved representative.
-/

set_option autoImplicit false

open MeasureTheory

namespace LOOConcentration

/-- The manuscript's expected fitted loss at a fixed test observation. -/
noncomputable def meanFittedLoss {k m r : ℕ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (T : Estimator (k + 1) (m + 1) (r + 1))
    (L : Responses (m + 1) → Responses (m + 1) → ℝ)
    (z : Observation (k + 1) (m + 1))
    (_hfin : Integrable
      (fun D : Dataset (Observation (k + 1) (m + 1)) (r + 1) =>
        fittedLoss T L D z)
      (Measure.pi fun _ : Fin (r + 1) => μ)) : ℝ :=
  ∫ D : Dataset (Observation (k + 1) (m + 1)) (r + 1),
    fittedLoss T L D z ∂Measure.pi fun _ : Fin (r + 1) => μ

end LOOConcentration
