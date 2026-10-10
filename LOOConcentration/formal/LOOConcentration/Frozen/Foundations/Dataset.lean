import Mathlib.Data.Fin.SuccPred

/-!
# Ordered datasets

Source: `LOOConcentration/v3/BeLa-LOOConcentration-referee-revision.tex`, lines 240–245.
-/

set_option autoImplicit false

namespace LOOConcentration

/-- An ordered data set with `n` observations. -/
abbrev Dataset (α : Type*) (n : ℕ) := Fin n → α

end LOOConcentration
