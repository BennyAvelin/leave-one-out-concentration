import LOOConcentration.Frozen.Foundations.Features
import LOOConcentration.Frozen.Foundations.Responses

/-!
# Observations

Source: `LOOConcentration/v3/BeLa-LOOConcentration-referee-revision.tex`, lines 242–248.
-/

set_option autoImplicit false

namespace LOOConcentration

/-- One observation `(X, Y)` in `ℝ^k × ℝ^m`. -/
abbrev Observation (k m : ℕ) := Features k × Responses m

end LOOConcentration
