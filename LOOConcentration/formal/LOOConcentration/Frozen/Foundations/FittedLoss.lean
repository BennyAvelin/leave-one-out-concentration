import LOOConcentration.Frozen.Foundations.Estimator

/-!
# Fitted loss

Source: `LOOConcentration/v3/BeLa-LOOConcentration-referee-revision.tex`, lines 259–265.
-/

set_option autoImplicit false

namespace LOOConcentration

/-- The loss at a test observation for the estimator fitted on `D`. -/
def fittedLoss {k m n : ℕ} (T : Estimator k m (n + 1))
    (L : Responses m → Responses m → ℝ)
    (D : Dataset (Observation k m) (n + 1)) (z : Observation k m) : ℝ :=
  L ((T D) z.1) z.2

end LOOConcentration
