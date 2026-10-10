import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Algebra.Order.Field

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal

open Filter
open scoped Topology

/-- The critical upper rate keeps the variance bound uniform when the actual
linear-growth coefficient is bounded by `B / sqrt N`. -/
theorem generic_unit_variance_critical_rate_upper
    (C B : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (δ₂ : ℕ → NNReal) (V : ℕ → ℝ)
    (hvariance : ∀ r, V r ≤ C * (r + 1 : ℝ) * (δ₂ (r + 1) : ℝ) ^ 2)
    (hcritical : ∀ r, (δ₂ (r + 1) : ℝ) ≤ B / Real.sqrt (r + 1 : ℝ)) :
    ∀ r, V r ≤ C * B ^ 2 := by
  intro r
  let N : ℝ := (r + 1 : ℝ)
  let d : ℝ := (δ₂ (r + 1) : ℝ)
  have hNpos : 0 < N := by dsimp [N]; positivity
  have hNnonneg : 0 ≤ N := hNpos.le
  have hdnonneg : 0 ≤ d := by dsimp [d]; positivity
  have hrateNonneg : 0 ≤ B / Real.sqrt N :=
    div_nonneg hB (Real.sqrt_nonneg _)
  have hdSq : d ^ 2 ≤ (B / Real.sqrt N) ^ 2 :=
    (sq_le_sq₀ hdnonneg hrateNonneg).2 (by simpa [N, d] using hcritical r)
  have hfactor : 0 ≤ C * N := mul_nonneg hC hNnonneg
  have hsqrt : Real.sqrt N ≠ 0 := (Real.sqrt_pos.mpr hNpos).ne'
  calc
    V r ≤ C * N * d ^ 2 := by simpa [N, d] using hvariance r
    _ ≤ C * N * (B / Real.sqrt N) ^ 2 := mul_le_mul_of_nonneg_left hdSq hfactor
    _ = C * B ^ 2 := by
      rw [div_pow, Real.sq_sqrt hNnonneg]
      field_simp [hsqrt]

/-- A little-o scaled growth coefficient makes the actual variance upper
bound tend to zero. This is an upper-bound conclusion, with no necessity claim. -/
theorem generic_unit_variance_subcritical_rate_tendsto_zero
    (C : ℝ)
    (δ₂ : ℕ → NNReal) (V : ℕ → ℝ)
    (hvariance : ∀ r, V r ≤ C * (r + 1 : ℝ) * (δ₂ (r + 1) : ℝ) ^ 2)
    (hVnonneg : ∀ r, 0 ≤ V r)
    (hsubcritical : Tendsto
      (fun r : ℕ => (δ₂ (r + 1) : ℝ) * Real.sqrt (r + 1 : ℝ)) atTop (𝓝 0)) :
    Tendsto V atTop (𝓝 0) := by
  have hupper : Tendsto
      (fun r : ℕ => C * ((δ₂ (r + 1) : ℝ) * Real.sqrt (r + 1 : ℝ)) ^ 2)
      atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] using
      tendsto_const_nhds.mul (hsubcritical.pow 2)
  apply squeeze_zero hVnonneg
  · intro r
    have hNnonneg : 0 ≤ (r + 1 : ℝ) := by positivity
    calc
      V r ≤ C * (r + 1 : ℝ) * (δ₂ (r + 1) : ℝ) ^ 2 := hvariance r
      _ = C * ((δ₂ (r + 1) : ℝ) * Real.sqrt (r + 1 : ℝ)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hNnonneg]
        ring
  · exact hupper

end LOOConcentration.Manuscript.Internal
