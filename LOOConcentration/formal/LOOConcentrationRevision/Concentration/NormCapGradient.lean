import LOOConcentration.Concentration.NormTruncationSlope
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Tactic

set_option autoImplicit false
namespace LOOConcentration.Revision
open InnerProductSpace

noncomputable section

/-- The source norm cap has its actual gradient on the whole Euclidean carrier. -/
theorem gradient_norm_cap_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (N : ℝ) (hN : 0 < N) (x : E) :
    gradient (fun y : E => N * (1 - Real.exp (-‖y‖ ^ 2 / N))) x =
      (2 * Real.exp (-‖x‖ ^ 2 / N)) • x := by
  have hn : DifferentiableAt ℝ (fun y : E => ‖y‖ ^ 2) x :=
    (contDiff_norm_sq ℝ (n := 1)).differentiable (by norm_num) x
  have hneg : DifferentiableAt ℝ (fun y : E => -‖y‖ ^ 2) x := by fun_prop
  have ha : DifferentiableAt ℝ (fun y : E => N⁻¹ * -‖y‖ ^ 2) x := by fun_prop
  have hfun : (fun y : E => N * (1 - Real.exp (-‖y‖ ^ 2 / N))) =
      (fun y : E => N * (1 - Real.exp (N⁻¹ * -‖y‖ ^ 2))) := by
    funext y
    rw [div_eq_mul_inv, mul_comm (-‖y‖ ^ 2)]
  have he : DifferentiableAt ℝ (fun y : E => 1 - Real.exp (N⁻¹ * -‖y‖ ^ 2)) x := by
    fun_prop
  have hfn := fderiv_neg (𝕜 := ℝ) (f := fun y : E => ‖y‖ ^ 2) (x := x)
  change fderiv ℝ (fun y : E => -‖y‖ ^ 2) x = -fderiv ℝ (fun y : E => ‖y‖ ^ 2) x at hfn
  rw [hfun, gradient, fderiv_const_mul he N,
    fderiv_const_sub 1, fderiv_exp ha, fderiv_const_mul hneg N⁻¹,
    hfn, fderiv_norm_sq_apply]
  have hinner : (InnerProductSpace.toDual ℝ (E)).symm (innerSL ℝ x) = x := by
    exact (InnerProductSpace.toDual ℝ (E)).symm_apply_apply x
  simp only [map_smul, map_nsmul, smul_neg, neg_neg, smul_smul, hinner]
  rw [← Nat.cast_smul_eq_nsmul ℝ (2 : ℕ) x, smul_smul]
  congr 1
  push_cast
  field_simp [hN.ne']

/-- Joint source cap smoothness, bounds, and the sharp squared-gradient bound. -/
theorem norm_cap_bounded_smooth {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (N : ℝ) (hN : 0 < N) :
    let Q := fun x : E => N * (1 - Real.exp (-‖x‖ ^ 2 / N))
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Q ∧
      (∀ x, 0 ≤ Q x ∧ Q x ≤ N ∧ ‖gradient Q x‖ ^ 2 ≤ 4 * Q x) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |Q x| ≤ B ∧ ‖gradient Q x‖ ≤ B := by
  let Q := fun x : E => N * (1 - Real.exp (-‖x‖ ^ 2 / N))
  have hnorm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : E => ‖x‖ ^ 2) := contDiff_norm_sq ℝ
  have hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Q :=
    contDiff_const.mul (contDiff_const.sub (Real.contDiff_exp.comp (hnorm.neg.div_const N)))
  have hpoint : ∀ x, 0 ≤ Q x ∧ Q x ≤ N ∧ ‖gradient Q x‖ ^ 2 ≤ 4 * Q x := by
    intro x
    have ht : 0 ≤ ‖x‖ ^ 2 / N := div_nonneg (sq_nonneg _) hN.le
    have he : Real.exp (-‖x‖ ^ 2 / N) ≤ 1 :=
      Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) hN.le)
    have hqnonneg : 0 ≤ Q x := mul_nonneg hN.le (sub_nonneg.mpr he)
    have hqle : Q x ≤ N := by
      dsimp [Q]
      nlinarith [Real.exp_nonneg (-‖x‖ ^ 2 / N)]
    refine ⟨hqnonneg, hqle, ?_⟩
    have hscalar := LOOConcentration.normTruncation_scalar_slope_ineq ht
    have hscaled := mul_le_mul_of_nonneg_left hscalar hN.le
    have hcancel : N * (‖x‖ ^ 2 / N) = ‖x‖ ^ 2 := by field_simp [hN.ne']
    have hExp : Real.exp (-‖x‖ ^ 2 / N) ^ 2 = Real.exp (-2 * (‖x‖ ^ 2 / N)) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    change ‖gradient (fun y : E => N * (1 - Real.exp (-‖y‖ ^ 2 / N))) x‖ ^ 2 ≤ _
    rw [gradient_norm_cap_eq N hN x, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (by norm_num) (Real.exp_nonneg _)), mul_pow, mul_pow, hExp]
    dsimp [Q]
    rw [← mul_assoc, hcancel] at hscaled
    simp only [neg_div] at hscaled ⊢
    nlinarith [hscaled]
  refine ⟨hsmooth, hpoint, N + 2 * Real.sqrt N, by positivity, ?_⟩
  intro x
  obtain ⟨h0, hle, hgrad⟩ := hpoint x
  have hsqrt : (Real.sqrt N) ^ 2 = N := Real.sq_sqrt hN.le
  have hgradle : ‖gradient Q x‖ ≤ 2 * Real.sqrt N := by
    nlinarith [Real.sqrt_nonneg N, norm_nonneg (gradient Q x)]
  exact ⟨by rw [abs_of_nonneg h0]; nlinarith [Real.sqrt_nonneg N],
    hgradle.trans (by linarith)⟩

end

end LOOConcentration.Revision
