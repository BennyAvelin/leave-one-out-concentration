import LOOConcentration.Frozen.Foundations.Estimator
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Positivity

set_option autoImplicit false
namespace LOOConcentration.Manuscript
open MeasureTheory

noncomputable def kernelDensityEstimator
    (K : {K : ℝ → ℝ // ContDiff ℝ 1 K ∧ (∀ x, 0 ≤ K x) ∧
      (∃ B : ℝ, ∀ x, |K x| ≤ B) ∧
      (∫ x : ℝ, K x) = 1 ∧ (∃ B : ℝ, ∀ x, |deriv K x| ≤ B)})
    (h : {t : ℝ // 0 < t}) (r : ℕ) : LOOConcentration.Estimator 1 1 (r + 1) :=
  fun D =>
    { toFun := fun x => (fun _ : Fin 1 =>
        ((r + 1 : ℝ) * h.val)⁻¹ * ∑ j : Fin (r + 1), K.val ((x 0 - (D j).1 0) / h.val))
      continuous_toFun := by
        have hK : Continuous K.val := K.property.1.continuous
        apply continuous_pi
        intro i
        fun_prop }

end LOOConcentration.Manuscript
