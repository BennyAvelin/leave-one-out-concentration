import LOOConcentrationManuscript.Frozen.Definitions.KernelDensityEstimator
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal

/-- Every actual KDE feature coordinate has the literal source derivative;
response coordinates remain unchanged on the whole paired data carrier. -/
theorem kde_actual_feature_coordinate_hasDerivAt
    (K : {K : ℝ → ℝ // ContDiff ℝ 1 K ∧ (∀ x, 0 ≤ K x) ∧
      (∃ B : ℝ, ∀ x, |K x| ≤ B) ∧ (∫ x : ℝ, K x) = 1 ∧
      (∃ B : ℝ, ∀ x, |deriv K x| ≤ B)})
    (h : {t : ℝ // 0 < t}) (r : ℕ)
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1))
    (j : Fin (r + 1)) (z : LOOConcentration.Observation 1 1) :
    let F := fun t : ℝ => (LOOConcentration.Manuscript.kernelDensityEstimator K h r
      (Function.update D j ((fun _ : Fin 1 => t), (D j).2)) z.1) 0
    let q := (z.1 0 - (D j).1 0) / h.val
    HasDerivAt F (-deriv K.val q / ((r + 1 : ℝ) * h.val ^ 2)) ((D j).1 0) ∧
      |deriv F ((D j).1 0)| = |deriv K.val q| / ((r + 1 : ℝ) * h.val ^ 2) := by
  classical
  intro F q
  let x := (D j).1 0
  let A := ∑ i : Fin (r + 1), K.val ((z.1 0 - (D i).1 0) / h.val)
  have hEq : F = fun t : ℝ => ((r + 1 : ℝ) * h.val)⁻¹ *
      (A + K.val ((z.1 0 - t) / h.val) - K.val q) := by
    funext t
    change ((r + 1 : ℝ) * h.val)⁻¹ * ∑ i,
      K.val ((z.1 0 - (Function.update D j ((fun _ : Fin 1 => t), (D j).2) i).1 0) / h.val) = _
    congr 1
    have hDelta : (∑ i : Fin (r + 1),
        (K.val ((z.1 0 - (Function.update D j ((fun _ : Fin 1 => t), (D j).2) i).1 0) / h.val) -
          K.val ((z.1 0 - (D i).1 0) / h.val))) = K.val ((z.1 0 - t) / h.val) - K.val q := by
      rw [Finset.sum_eq_single j]
      · simp only [Function.update_self, q]
      · intro i _hi hij
        simp only [Function.update_of_ne hij, sub_self]
      · intro hj
        exact (hj (Finset.mem_univ j)).elim
    rw [Finset.sum_sub_distrib] at hDelta
    dsimp [A]
    linarith only [hDelta]
  have hK := (K.property.1.differentiable (by norm_num)).differentiableAt.hasDerivAt (x := q)
  have hArg : HasDerivAt (fun t : ℝ => (z.1 0 - t) / h.val) (-1 / h.val) x := by
    simpa only [Pi.neg_apply, sub_eq_add_neg, add_comm] using (((hasDerivAt_id' (𝕜 := ℝ) x).neg).add_const (z.1 0)).div_const h.val
  have hAtom := hK.comp x hArg
  have hF := ((hAtom.const_add A).sub_const (K.val q)).const_mul
    (((r + 1 : ℝ) * h.val)⁻¹)
  have hh : 0 < h.val := h.property
  have hDeriv : HasDerivAt F (-deriv K.val q / ((r + 1 : ℝ) * h.val ^ 2)) x := by
    rw [hEq]
    convert hF using 1 <;> first | rfl | (field_simp [hh.ne'])
  refine ⟨hDeriv, ?_⟩
  rw [hDeriv.deriv, abs_div, abs_neg, abs_of_pos (by positivity : 0 < (r + 1 : ℝ) * h.val ^ 2)]

end LOOConcentration.Manuscript.Internal
