import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Quadratic-gradient concentration rate

Source: `LOOConcentration/v3/BeLa-LOOConcentration-referee-revision.tex`, lines 442–448.
Zero denominators are interpreted as `+∞` inside the minimum, exactly as
specified there. The `M₂` argument must be instantiated with the actual
observation second moment in theorem statements.
-/

set_option autoImplicit false

namespace LOOConcentration

/-- The quadratic-gradient concentration rate from the manuscript, with
zero denominators interpreted as infinity inside the minimum. -/
noncomputable def thetaRate
    (C M₂ : ℝ) (_hC : 0 < C) (_hM₂ : 0 ≤ M₂)
    (r : ℕ) (_hr : 1 ≤ r)
    (t : ℝ) (_ht : 0 < t)
    (a b : ℝ) (_ha : 0 ≤ a) (_hb : 0 ≤ b) : ℝ :=
  if a ^ 2 + 2 * b ^ 2 * (r : ℝ) * M₂ = 0 then
    if b = 0 then 0 else Real.exp (-(t / (8 * C * b)))
  else if b = 0 then
    Real.exp (-(t ^ 2 / (8 * C * (a ^ 2 + 2 * b ^ 2 * (r : ℝ) * M₂))))
  else
    Real.exp (-(min
      (t ^ 2 / (8 * C * (a ^ 2 + 2 * b ^ 2 * (r : ℝ) * M₂)))
      (t / (8 * C * b))))

end LOOConcentration
