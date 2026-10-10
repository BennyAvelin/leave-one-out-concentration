import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory

/-- Actual centering retains exponential-square integrability at a fixed enlarged
scale. The uncentered bound is an internal premise of the restriction argument. -/
theorem centered_square_exponential_bound
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (X : α → ℝ) (hX : Integrable X μ) (a : ℝ) (ha : 0 < a)
    (hExp : Integrable (fun x => Real.exp ((X x)^2/a)) μ)
    (hBound : (∫ x, Real.exp ((X x)^2/a) ∂μ) ≤ 2) :
    Integrable (fun x => Real.exp ((X x - ∫ y, X y ∂μ)^2/(16*a))) μ ∧
    (∫ x, Real.exp ((X x - ∫ y, X y ∂μ)^2/(16*a)) ∂μ) ≤ 2 := by
  let m := ∫ x, X x ∂μ
  have hSqPoint (x : α) : (X x)^2 ≤ a * Real.exp ((X x)^2/a) := by
    have h := Real.add_one_le_exp ((X x)^2/a)
    have hmul := mul_le_mul_of_nonneg_left h ha.le
    have heq : a * ((X x)^2/a) = (X x)^2 := by field_simp
    nlinarith
  have hSq : Integrable (fun x => (X x)^2) μ := by
    apply (hExp.const_mul a).mono' (by fun_prop)
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (X x))]
    exact hSqPoint x
  have hSqBound : (∫ x, (X x)^2 ∂μ) ≤ 2*a := by
    calc
      _ ≤ ∫ x, a * Real.exp ((X x)^2/a) ∂μ :=
        integral_mono hSq (hExp.const_mul a) hSqPoint
      _ = a * (∫ x, Real.exp ((X x)^2/a) ∂μ) := integral_const_mul _ _
      _ ≤ a*2 := mul_le_mul_of_nonneg_left hBound ha.le
      _ = _ := by ring
  have hMean : m^2 ≤ 2*a := by
    have hc : ConvexOn ℝ Set.univ (fun x : ℝ => x^2) :=
      (show Even (2:ℕ) by decide).convexOn_pow
    have hJ := hc.map_integral_le (by fun_prop) isClosed_univ
      (ae_of_all μ fun x => Set.mem_univ (X x)) hX hSq
    exact hJ.trans hSqBound
  have hChord (z : ℝ) : Real.exp (z/8) ≤ 7/8 + (1/8)*Real.exp z := by
    have h := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ z)
      (show 0 ≤ (7/8:ℝ) by norm_num) (show 0 ≤ (1/8:ℝ) by norm_num)
      (show (7/8:ℝ)+1/8=1 by norm_num)
    simpa only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one,
      one_div_mul_eq_div] using h
  have hPoint (x : α) : Real.exp ((X x-m)^2/(16*a)) ≤
      Real.exp (1/4) * (7/8 + (1/8)*Real.exp ((X x)^2/a)) := by
    have hs : (X x-m)^2 ≤ 2*(X x)^2+2*m^2 := by
      nlinarith [sq_nonneg (X x+m)]
    have hdiv : (X x-m)^2/(16*a) ≤ (X x)^2/(8*a)+1/4 := by
      apply (div_le_iff₀ (by positivity : 0 < 16*a)).2
      have heq : ((X x)^2/(8*a)+1/4)*(16*a) = 2*(X x)^2+4*a := by field_simp; ring
      rw [heq]
      nlinarith
    calc
      _ ≤ Real.exp ((X x)^2/(8*a)+1/4) := Real.exp_le_exp.mpr hdiv
      _ = Real.exp (1/4) * Real.exp (((X x)^2/a)/8) := by
        rw [Real.exp_add, mul_comm]
        congr 1
        congr 1
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (hChord ((X x)^2/a)) (Real.exp_pos _).le
  have hDom : Integrable (fun x => Real.exp (1/4) *
      (7/8 + (1/8)*Real.exp ((X x)^2/a))) μ :=
    ((integrable_const (7/8:ℝ)).add (hExp.const_mul (1/8))).const_mul _
  have hCentered : Integrable (fun x => Real.exp ((X x-m)^2/(16*a))) μ := by
    apply hDom.mono' (by fun_prop)
    filter_upwards with x
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hPoint x
  refine ⟨hCentered, ?_⟩
  change (∫ x, Real.exp ((X x-m)^2/(16*a)) ∂μ) ≤ 2
  calc
    _ ≤ ∫ x, Real.exp (1/4)*(7/8+(1/8)*Real.exp ((X x)^2/a)) ∂μ :=
      integral_mono hCentered hDom hPoint
    _ = Real.exp (1/4)*(7/8+(1/8)*(∫ x, Real.exp ((X x)^2/a) ∂μ)) := by
      rw [integral_const_mul, integral_add (integrable_const _) (hExp.const_mul _),
        integral_const, integral_const_mul]
      simp
    _ ≤ Real.exp (1/4)*(9/8) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      linarith
    _ ≤ 2 := by
      have h := Real.exp_bound_div_one_sub_of_interval (x := (1/4:ℝ)) (by norm_num) (by norm_num)
      norm_num at h
      nlinarith

end LOOConcentration.Revision
