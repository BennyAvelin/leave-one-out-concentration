import Mathlib.Analysis.SpecialFunctions.Sqrt
import LOOConcentration.Frozen.Norms.ObservationNormSq

/-!
# Euclidean norm of an observation

Source: `LOOConcentration/v3/BeLa-LOOConcentration-referee-revision.tex`, line 268.
-/

set_option autoImplicit false

namespace LOOConcentration

/-- Euclidean norm of an observation's combined coordinates. -/
noncomputable def observationNorm {k m : ℕ} (z : Observation k m) : ℝ :=
  Real.sqrt (observationNormSq z)

end LOOConcentration
