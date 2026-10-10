import LOOConcentrationManuscript.Frozen.Results.EmpiricalMeanQuadraticLossDeleteBias
import Mathlib.Analysis.Real.Sqrt

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open Filter MeasureTheory ProbabilityTheory
open scoped Topology

/-- Nonnegativity and convergence for the source's exact quadratic-mean rates. -/
theorem quadraticMean_rates_nonnegative_tendsto (v z : ℝ) (hv : 0 ≤ v) :
    (∀ r : ℕ, 0 ≤ 2 * |z| / Real.sqrt (r + 1 : ℝ)) ∧
    Tendsto (fun r : ℕ => 2 * |z| / Real.sqrt (r + 1 : ℝ)) atTop (𝓝 0) ∧
    (∀ r : ℕ, 0 ≤ (2 : ℝ) / (r + 1 : ℝ)) ∧
    Tendsto (fun r : ℕ => (2 : ℝ) / (r + 1 : ℝ)) atTop (𝓝 0) ∧
    (∀ n : ℕ, 0 ≤ v / ((n + 2 : ℝ) * (n + 1 : ℝ))) ∧
    Tendsto (fun n : ℕ => v / ((n + 2 : ℝ) * (n + 1 : ℝ))) atTop (𝓝 0) := by
  have hN₁ : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hN₂ : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hinv₁ := tendsto_inv_atTop_zero.comp hN₁
  have hinv₂ := tendsto_inv_atTop_zero.comp hN₂
  have hsqrt := tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hN₁)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r
    positivity
  · simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using hsqrt.const_mul (2 * |z|)
  · intro r
    positivity
  · simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using hinv₁.const_mul (2 : ℝ)
  · intro n
    exact div_nonneg hv (by positivity)
  · simpa only [div_eq_mul_inv, mul_inv_rev, mul_zero, Function.comp_def] using
      (hinv₁.mul hinv₂).const_mul v

end LOOConcentration.Manuscript.Internal
