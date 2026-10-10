import LOOConcentration.Frozen.Foundations.Estimator
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Positivity

set_option autoImplicit false
namespace LOOConcentration.Manuscript
open MeasureTheory

noncomputable def stabilizedLinearEstimator
    (b δ : {t : ℝ // 0 < t}) (r : ℕ) : LOOConcentration.Estimator 1 1 (r + 1) :=
  fun D =>
    let a : ℝ := (r + 1 : ℝ)⁻¹ * ∑ j : Fin (r + 1), (D j).1 0
    let U : Fin (r + 1) → ℝ := fun j => max (min ((D j).2 0) b.val) (-b.val)
    let c : ℝ := (r + 1 : ℝ)⁻¹ * ∑ j : Fin (r + 1), U j
    let v : ℝ := (r + 1 : ℝ)⁻¹ * ∑ j : Fin (r + 1), ((D j).1 0 - a) ^ 2
    let s : ℝ := (r + 1 : ℝ)⁻¹ * ∑ j : Fin (r + 1), ((D j).1 0 - a) * (U j - c)
    let beta : ℝ := s / (v + δ.val)
    { toFun := fun x => (fun _ : Fin 1 =>
        ((r + 1 : ℝ)⁻¹ * ∑ j : Fin (r + 1), (D j).2 0) + beta * (x 0 - a))
      continuous_toFun := by
        apply continuous_pi
        intro i
        fun_prop }

end LOOConcentration.Manuscript
