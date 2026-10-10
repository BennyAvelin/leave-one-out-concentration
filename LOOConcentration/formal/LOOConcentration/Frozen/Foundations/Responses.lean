import Mathlib.Topology.Instances.RealVectorSpace

/-!
# Response coordinates

Source: `LOOConcentration/v3/BeLa-LOOConcentration-referee-revision.tex`, lines 242–248.
-/

set_option autoImplicit false

namespace LOOConcentration

/-- The response coordinates of one observation. -/
abbrev Responses (m : ℕ) := Fin m → ℝ

end LOOConcentration
