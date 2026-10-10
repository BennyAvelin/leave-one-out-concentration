import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.Pi

set_option autoImplicit false
namespace LOOConcentration

/-- The scalar ordinary least-squares predictor with intercept. On a
zero-variance design, the slope is set to zero. -/
noncomputable def olsPrediction {r : ℕ} (D : Fin (r + 2) → ℝ × ℝ) (x : ℝ) : ℝ :=
  let xbar := (∑ i : Fin (r + 2), (D i).1) / (r + 2 : ℝ)
  let ybar := (∑ i : Fin (r + 2), (D i).2) / (r + 2 : ℝ)
  let s := ∑ i : Fin (r + 2), ((D i).1 - xbar) ^ 2
  let cov := ∑ i : Fin (r + 2), ((D i).1 - xbar) * ((D i).2 - ybar)
  ybar + (cov / s) * (x - xbar)

end LOOConcentration
