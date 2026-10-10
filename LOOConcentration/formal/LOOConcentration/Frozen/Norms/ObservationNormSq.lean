import LOOConcentration.Frozen.Foundations.Observation

/-!
# Squared Euclidean norm of an observation

Source: `LOOConcentration/v3/BeLa-LOOConcentration-referee-revision.tex`, line 268.
-/

set_option autoImplicit false

namespace LOOConcentration

/-- Squared Euclidean norm of an observation's combined coordinates. -/
def observationNormSq {k m : ℕ} (z : Observation k m) : ℝ :=
  (∑ i : Fin k, (z.1 i) ^ 2) + ∑ j : Fin m, (z.2 j) ^ 2

end LOOConcentration
