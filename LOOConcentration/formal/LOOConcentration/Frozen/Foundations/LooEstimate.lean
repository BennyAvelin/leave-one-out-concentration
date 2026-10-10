import LOOConcentration.Frozen.Foundations.DeleteAt
import LOOConcentration.Frozen.Foundations.Estimator

/-!
# Empirical leave-one-out estimate

Source: `LOOConcentration/v3/BeLa-LOOConcentration-referee-revision.tex`, lines 252–259.
-/

set_option autoImplicit false

namespace LOOConcentration

/-- The leave-one-out estimate for a data set of length `n + 2`. -/
noncomputable def looEstimate {k m n : ℕ} (T : Estimator k m (n + 1))
    (L : Responses m → Responses m → ℝ)
    (D : Dataset (Observation k m) (n + 2)) : ℝ :=
  (∑ i : Fin (n + 2), L ((T (deleteAt D i)) (D i).1) (D i).2) / (n + 2)

end LOOConcentration
