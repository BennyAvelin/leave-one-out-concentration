import LOOConcentrationRevision.FunctionalInequalities.SobolevLinear
import LOOConcentrationRevision.FunctionalInequalities.SobolevEnergyNorm
import LOOConcentrationRevision.FunctionalInequalities.EntropyLimit
import LOOConcentrationRevision.FunctionalInequalities.LogSobolevConstant
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory Filter
open scoped ENNReal Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
    {μ : Measure (EuclideanSpace ℝ ι)} [IsProbabilityMeasure μ]

/-- The actual Sobolev perturbation has exactly the retained scaled gradient energy. -/
theorem sobolevEnergy_perturbation_of_zero (u v : SobolevPair μ)
    (hu : sobolevEnergy μ u = 0) (t : ℝ) :
    sobolevEnergy μ (sobolevPairPerturbation μ u v t) =
      ENNReal.ofReal ((|t| * ‖(WithLp.ofLp v.val).2‖)^2) := by
  rw [sobolevEnergy_eq_ofReal_norm_sq, sobolevPairPerturbation_gradient_component,
    (sobolevEnergy_eq_zero_iff u).mp hu, zero_add, norm_smul, Real.norm_eq_abs]

/-- A positive-energy Sobolev witness discharges the zero-energy entropy argument.
The witness must be produced for the original measure by the all-pairs consumer. -/
theorem squareEntropy_eq_zero_of_energy_zero_and_witness
    (hfinite : logSobolevConstant μ < ⊤) (u v : SobolevPair μ)
    (hu : sobolevEnergy μ u = 0) (hv : 0 < sobolevEnergy μ v) :
    squareEntropy μ (WithLp.ofLp u.val).1 = 0 := by
  let t : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have ht : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have htpos (n : ℕ) : 0 < t n := by
    exact one_div_pos.mpr (by positivity)
  have hG : (WithLp.ofLp v.val).2 ≠ 0 := by
    intro h
    exact hv.ne' ((sobolevEnergy_eq_zero_iff v).mpr h)
  have hnorm : 0 < ‖(WithLp.ofLp v.val).2‖ := norm_pos_iff.mpr hG
  have hpos (n : ℕ) : 0 < sobolevEnergy μ (sobolevPairPerturbation μ u v (t n)) := by
    rw [sobolevEnergy_perturbation_of_zero u v hu]
    exact ENNReal.ofReal_pos.mpr (sq_pos_of_pos (mul_pos (abs_pos.mpr (htpos n).ne') hnorm))
  have hf (n : ℕ) : squareEntropy μ ((WithLp.ofLp u.val).1 + t n • (WithLp.ofLp v.val).1) < ⊤ := by
    rw [← sobolevPairPerturbation_function_component]
    exact squareEntropy_lt_top_of_energy_pos hfinite _ (hpos n)
  have hE : Tendsto (fun n => sobolevEnergy μ (sobolevPairPerturbation μ u v (t n)))
      atTop (𝓝 0) := by
    simp_rw [sobolevEnergy_perturbation_of_zero u v hu]
    have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((ht.abs.mul_const ‖(WithLp.ofLp v.val).2‖).pow 2)
    simpa only [Function.comp_def, abs_zero, zero_mul, zero_pow (by decide : 2 ≠ 0), ENNReal.ofReal_zero] using h
  have hbound : Tendsto (fun n => 2 * logSobolevConstant μ *
      sobolevEnergy μ (sobolevPairPerturbation μ u v (t n))) atTop (𝓝 0) := by
    have hc : (2 : ℝ≥0∞) * logSobolevConstant μ ≠ ⊤ :=
      ENNReal.mul_ne_top (by norm_num) hfinite.ne
    simpa only [Function.comp_def, mul_zero] using
      (ENNReal.continuous_const_mul hc).continuousAt.tendsto.comp hE
  have hS : Tendsto (fun n => squareEntropy μ
      ((WithLp.ofLp u.val).1 + t n • (WithLp.ofLp v.val).1)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
    · intro n
      exact bot_le
    · intro n
      change squareEntropy μ ((WithLp.ofLp u.val).1 + t n • (WithLp.ofLp v.val).1) ≤ _
      rw [← sobolevPairPerturbation_function_component]
      exact squareEntropy_le_of_energy_pos _ (hpos n)
  exact squareEntropy_eq_zero_of_perturbation _ _ t ht hf hS

end LOOConcentration.Revision
