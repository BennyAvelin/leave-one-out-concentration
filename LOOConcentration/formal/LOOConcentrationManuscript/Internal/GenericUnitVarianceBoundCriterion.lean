import LOOConcentrationRevision.FunctionalInequalities.ZeroLsiPointmassViaTruncation
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal
open MeasureTheory Filter
open scoped Topology ENNReal

/-- The source's unit variance excludes the zero native constant internally.
The criterion concerns the Poincare upper bound, not necessity for actual
variance to vanish. -/
theorem generic_unit_variance_native_upper_bound_criterion
    (μ : Measure (EuclideanSpace ℝ (Fin 1))) [IsProbabilityMeasure μ]
    (hFinite : LOOConcentration.Revision.logSobolevConstant μ < ⊤)
    (hM2 : Integrable (fun x => ‖x‖ ^ 2) μ)
    (hUnitVariance : (∫ x, (x 0 - ∫ y, y 0 ∂μ) ^ 2 ∂μ) = 1)
    (b : ℕ → NNReal) :
    let C := (LOOConcentration.Revision.logSobolevConstant μ).toReal
    0 < C ∧
      (Tendsto (fun r : ℕ => C * (b (r + 1) : ℝ) ^ 2 * (r + 1 : ℝ)) atTop (𝓝 0) ↔
        Tendsto (fun r : ℕ => (b (r + 1) : ℝ) * Real.sqrt (r + 1 : ℝ)) atTop (𝓝 0)) := by
  intro C
  have hNe : LOOConcentration.Revision.logSobolevConstant μ ≠ 0 := by
    intro hz
    obtain ⟨a, ha⟩ := LOOConcentration.Revision.exists_dirac_of_logSobolevConstant_eq_zero_via_truncation μ hM2 hz
    rw [ha] at hUnitVariance
    simp only [integral_dirac, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hUnitVariance
    norm_num at hUnitVariance
  have hC : 0 < C := ENNReal.toReal_pos hNe hFinite.ne
  refine ⟨hC, ?_⟩
  let x := fun r : ℕ => (b (r + 1) : ℝ) * Real.sqrt (r + 1 : ℝ)
  have hx (r : ℕ) : 0 ≤ x r := mul_nonneg (b _).coe_nonneg (Real.sqrt_nonneg _)
  have heq (r : ℕ) : C * (b (r + 1) : ℝ) ^ 2 * (r + 1 : ℝ) = C * (x r) ^ 2 := by
    dsimp [x]
    rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ r + 1)]
    ring
  constructor
  · intro h
    have hs : Tendsto (fun r => (x r) ^ 2) atTop (𝓝 0) := by
      have hh := h.div_const C
      simpa only [heq, mul_div_cancel_left₀ _ hC.ne', zero_div] using hh
    have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hs
    have hsqrt (r : ℕ) : Real.sqrt ((x r) ^ 2) = x r := Real.sqrt_sq (hx r)
    simpa only [Function.comp_def, hsqrt, Real.sqrt_zero] using hh
  · intro h
    have hh := (h.pow 2).const_mul C
    simpa only [heq, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, x] using hh

end LOOConcentration.Manuscript.Internal
