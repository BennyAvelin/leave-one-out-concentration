import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open MeasureTheory ProbabilityTheory Filter
open scoped ContDiff

private theorem abs_mul_exp_neg_half_sq_le_one (x : ℝ) :
    |x| * Real.exp (-(x ^ 2) / 2) ≤ 1 := by
  have habs : |x| ≤ 1 + x ^ 2 / 2 := by
    nlinarith [sq_nonneg (|x| - 1), sq_abs x]
  have he : |x| ≤ Real.exp (x ^ 2 / 2) :=
    habs.trans (by simpa [add_comm] using Real.add_one_le_exp (x ^ 2 / 2))
  calc
    _ ≤ Real.exp (x ^ 2 / 2) * Real.exp (-(x ^ 2) / 2) :=
      mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
    _ = 1 := by
      rw [← Real.exp_add]
      have hz : x ^ 2 / 2 + -(x ^ 2) / 2 = 0 := by ring
      rw [hz, Real.exp_zero]

/-- Source Gaussian kernel: actual normalized density, smoothness, finite
integrated squared loss and uniform bounds for its value and derivative. -/
theorem gaussianKernel_normalization_and_bounds :
    let K := gaussianPDFReal 0 1
    let W := (Real.sqrt (2 * Real.pi))⁻¹
    ContDiff ℝ ∞ K ∧ (∀ x, 0 ≤ K x) ∧ Integrable K ∧
      (∫ x : ℝ, K x) = 1 ∧ Integrable (fun x : ℝ => (K x) ^ 2) ∧
      (∀ x, |K x| ≤ W) ∧
      (∀ x, HasDerivAt K (-(x) * K x) x ∧ |deriv K x| ≤ W) := by
  intro K W
  have hEq : K = (fun x : ℝ => W * Real.exp (-(x ^ 2) / 2)) := by
    funext x
    simp only [K, W, gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  have hW : 0 ≤ W := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hNonneg : ∀ x, 0 ≤ K x := gaussianPDFReal_nonneg 0 1
  have hBound : ∀ x, |K x| ≤ W := by
    intro x
    rw [abs_of_nonneg (hNonneg x), hEq]
    have hexp : Real.exp (-(x ^ 2) / 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg x)) (by norm_num))
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp hW
  have hInt : Integrable K := integrable_gaussianPDFReal 0 1
  have hSquare : Integrable (fun x : ℝ => (K x) ^ 2) := by
    have hProd := hInt.bdd_mul hInt.aestronglyMeasurable
      (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hBound x))
    simpa only [pow_two] using hProd
  refine ⟨?_, hNonneg, hInt, integral_gaussianPDFReal_eq_one 0 (by norm_num), hSquare, hBound, ?_⟩
  · rw [hEq]
    fun_prop
  · intro x
    have hExp : HasDerivAt (fun y : ℝ => Real.exp (-(y ^ 2) / 2))
        (-(x) * Real.exp (-(x ^ 2) / 2)) x := by
      have hInner : HasDerivAt (fun y : ℝ => -(y ^ 2) / 2) (-(x)) x := by
        have hRaw := (((hasDerivAt_id' (𝕜 := ℝ) x).pow 2).neg.div_const 2)
        have hc : -((2 : ℝ) * x) / 2 = -x := by ring
        simpa only [Pi.neg_apply, Pi.pow_apply, Nat.cast_ofNat,
          show (2 - 1 : ℕ) = 1 from rfl, pow_one, mul_one, hc] using hRaw
      simpa only [mul_comm] using hInner.exp
    have hDeriv : HasDerivAt K (-(x) * K x) x := by
      rw [hEq]
      convert hExp.const_mul W using 1 <;> first | rfl | ring
    refine ⟨hDeriv, ?_⟩
    rw [hDeriv.deriv, abs_mul, abs_neg, abs_of_nonneg (hNonneg x), hEq]
    calc
      _ = W * (|x| * Real.exp (-(x ^ 2) / 2)) := by ring
      _ ≤ W * 1 := mul_le_mul_of_nonneg_left (abs_mul_exp_neg_half_sq_le_one x) hW
      _ = W := mul_one W

end LOOConcentration.Manuscript.Internal
