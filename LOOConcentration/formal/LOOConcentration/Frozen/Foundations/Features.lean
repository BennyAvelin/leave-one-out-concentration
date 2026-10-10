import Mathlib.Topology.Instances.RealVectorSpace

/-!
# Feature coordinates

Source: `LOOConcentration/v3/BeLa-LOOConcentration-referee-revision.tex`, lines 242–248.
-/

set_option autoImplicit false

namespace LOOConcentration

/-- The feature coordinates of one observation. -/
abbrev Features (k : ℕ) := Fin k → ℝ

end LOOConcentration
