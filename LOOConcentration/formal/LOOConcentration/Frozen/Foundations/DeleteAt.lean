import Mathlib.Data.Fin.SuccPred
import LOOConcentration.Frozen.Foundations.Dataset

/-!
# Deleting one observation

Source: `LOOConcentration/v3/BeLa-LOOConcentration-referee-revision.tex`, lines 242–245.
-/

set_option autoImplicit false

namespace LOOConcentration

/-- Remove one observation without changing the order of the others. -/
def deleteAt {α : Type*} {n : ℕ}
    (D : Dataset α (n + 1)) (i : Fin (n + 1)) : Dataset α n :=
  fun j => D (i.succAbove j)

end LOOConcentration
