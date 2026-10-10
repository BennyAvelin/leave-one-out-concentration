import LOOConcentrationRevision.Frozen.Definitions.SquareEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

/-!
# Basic facts about literal square entropy

The entropy density's negative part has integral at most exp(-1) under a
probability law, even when its positive part has infinite integral. This is
the negative-part obligation in the revision plan; Jensen's inequality and
the zero-energy perturbation limit are separate obligations.
-/

set_option autoImplicit false

namespace LOOConcentration.Revision

open MeasureTheory
open scoped ENNReal

/-- The sharp universal bound for the negative entropy density. -/
theorem neg_mul_log_le_exp_neg_one {x : ℝ} (hx : 0 ≤ x) :
    -(x * Real.log x) ≤ Real.exp (-1) := by
  have hmin : Real.exp (-1) * Real.log (Real.exp (-1)) ≤ x * Real.log x := by
    rcases le_total x (Real.exp (-1)) with h | h
    · exact Real.mul_log_strictAntiOn.antitoneOn
        ⟨hx, h⟩ ⟨(Real.exp_pos _).le, le_rfl⟩ h
    · have ha : Real.exp (-1) ∈ Set.Ici (Real.exp (-1)) := Set.mem_Ici.mpr le_rfl
      have hb : x ∈ Set.Ici (Real.exp (-1)) := Set.mem_Ici.mpr h
      exact Real.mul_log_strictMonoOn.monotoneOn ha hb h
  simpa only [Real.log_exp, mul_neg_one, neg_neg] using neg_le_neg hmin

variable {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ]

theorem squareEntropy_negative_part_le (f : Lp ℝ 2 μ) :
    (∫⁻ x, ENNReal.ofReal (-((f x) ^ 2 * Real.log ((f x) ^ 2))) ∂μ) ≤
      ENNReal.ofReal (Real.exp (-1)) := by
  calc
    (∫⁻ x, ENNReal.ofReal (-((f x) ^ 2 * Real.log ((f x) ^ 2))) ∂μ) ≤
        ∫⁻ _ : α, ENNReal.ofReal (Real.exp (-1)) ∂μ :=
      lintegral_mono fun x => ENNReal.ofReal_le_ofReal
        (neg_mul_log_le_exp_neg_one (sq_nonneg (f x)))
    _ = ENNReal.ofReal (Real.exp (-1)) := by
      rw [lintegral_const, measure_univ, mul_one]

theorem squareEntropy_negative_part_lt_top (f : Lp ℝ 2 μ) :
    (∫⁻ x, ENNReal.ofReal (-((f x) ^ 2 * Real.log ((f x) ^ 2))) ∂μ) < ⊤ :=
  (squareEntropy_negative_part_le f).trans_lt ENNReal.ofReal_lt_top

omit [IsProbabilityMeasure μ] in
theorem integrable_sq (f : Lp ℝ 2 μ) : Integrable (fun x => (f x) ^ 2) μ :=
  (Lp.memLp f).integrable_sq

omit [IsProbabilityMeasure μ] in
theorem integral_sq_nonneg (f : Lp ℝ 2 μ) : 0 ≤ ∫ x, (f x) ^ 2 ∂μ :=
  integral_nonneg fun x => sq_nonneg (f x)

/-- Literal entropy is independent of almost-everywhere representatives. -/
theorem squareEntropy_congr_ae (f g : Lp ℝ 2 μ) (hfg : f =ᵐ[μ] g) :
    squareEntropy μ f = squareEntropy μ g := by
  have hs : (fun x => (f x) ^ 2) =ᵐ[μ] (fun x => (g x) ^ 2) :=
    hfg.fun_comp (fun t : ℝ => t ^ 2)
  have hp : (fun x => ENNReal.ofReal ((f x) ^ 2 * Real.log ((f x) ^ 2))) =ᵐ[μ]
      (fun x => ENNReal.ofReal ((g x) ^ 2 * Real.log ((g x) ^ 2))) :=
    hfg.fun_comp (fun t : ℝ => ENNReal.ofReal (t ^ 2 * Real.log (t ^ 2)))
  have hn : (fun x => ENNReal.ofReal (-((f x) ^ 2 * Real.log ((f x) ^ 2)))) =ᵐ[μ]
      (fun x => ENNReal.ofReal (-((g x) ^ 2 * Real.log ((g x) ^ 2)))) :=
    hfg.fun_comp (fun t : ℝ => ENNReal.ofReal (-(t ^ 2 * Real.log (t ^ 2))))
  unfold squareEntropy
  rw [integral_congr_ae hs, lintegral_congr_ae hp, lintegral_congr_ae hn]

end LOOConcentration.Revision
