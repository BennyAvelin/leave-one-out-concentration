import LOOConcentration.Frozen.Foundations.Estimator
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Positivity

set_option autoImplicit false
namespace LOOConcentration.Manuscript
open MeasureTheory

noncomputable def stabilizedKernelEstimator
    (K : {K : ℝ → ℝ // Continuous K ∧ ∀ x, 0 ≤ K x})
    (h δ : {t : ℝ // 0 < t}) (r : ℕ) : LOOConcentration.Estimator 1 1 (r + 1) :=
  fun D =>
    { toFun := fun x => (fun _ : Fin 1 =>
        (∑ j : Fin (r + 1), (h.val⁻¹ * K.val ((x 0 - (D j).1 0) / h.val)) * (D j).2 0) /
        ((∑ j : Fin (r + 1), h.val⁻¹ * K.val ((x 0 - (D j).1 0) / h.val)) +
          (r + 1 : ℝ) * δ.val))
      continuous_toFun := by
        have hK : Continuous K.val := K.property.1
        have hden : ∀ x : LOOConcentration.Features 1,
            0 < (∑ j : Fin (r + 1), h.val⁻¹ * K.val ((x 0 - (D j).1 0) / h.val)) +
              (r + 1 : ℝ) * δ.val := by
          intro x
          exact add_pos_of_nonneg_of_pos
            (Finset.sum_nonneg fun j _ => mul_nonneg (inv_nonneg.mpr h.property.le)
              (K.property.2 _)) (mul_pos (by positivity) δ.property)
        apply continuous_pi
        intro i
        apply Continuous.div
        · fun_prop
        · fun_prop
        · intro x
          exact (hden x).ne' }

end LOOConcentration.Manuscript
