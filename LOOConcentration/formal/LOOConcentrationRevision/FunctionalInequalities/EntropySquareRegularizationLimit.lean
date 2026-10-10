import LOOConcentration.FunctionalInequalities.EntropyTensorization
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Positivity

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory Filter
open scoped Topology

/-- Bounded square densities retain their literal entropy in a vanishing
nonnegative scalar regularization. All integral finiteness is produced here. -/
theorem tendsto_entropy_square_add_regularization
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (F : α → ℝ) (hF : Measurable F) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ x, |F x| ≤ B) (δ : ℕ → ℝ)
    (hδ : ∀ n, 0 ≤ δ n ∧ δ n ≤ 1) (hδlim : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n => LOOConcentration.entropy μ (fun x => (F x)^2 + δ n))
      atTop (𝓝 (LOOConcentration.entropy μ (fun x => (F x)^2))) := by
  have hsquare (x : α) : (F x)^2 ≤ B^2 := by
    rw [sq_le_sq, abs_of_nonneg hB]
    exact hbound x
  have hcompact : IsCompact (Set.Icc (0 : ℝ) (B^2 + 1)) := isCompact_Icc
  have hcont : Continuous (fun t : ℝ => ‖t * Real.log t‖) :=
    continuous_norm.comp Real.continuous_mul_log
  obtain ⟨M, hM0, hM⟩ := hcompact.bddAbove_image hcont.continuousOn |>.exists_ge 0
  have hDCT : Tendsto (fun n => ∫ x, ((F x)^2 + δ n) *
      Real.log ((F x)^2 + δ n) ∂μ) atTop
      (𝓝 (∫ x, (F x)^2 * Real.log ((F x)^2) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ : α => M)
    · intro n
      exact (Real.continuous_mul_log.measurable.comp
        ((hF.pow_const 2).add_const (δ n))).aestronglyMeasurable
    · exact integrable_const M
    · intro n
      exact Eventually.of_forall fun x => hM _ ⟨(F x)^2 + δ n,
        ⟨add_nonneg (sq_nonneg _) (hδ n).1,
         add_le_add (hsquare x) (hδ n).2⟩, rfl⟩
    · exact Eventually.of_forall fun x => by
        have h := (tendsto_const_nhds (x := (F x)^2)).add hδlim
        have hx := Real.continuous_mul_log.continuousAt.tendsto.comp h
        simpa only [Function.comp_def, add_zero] using hx
  have hInt : Integrable (fun x => (F x)^2) μ := by
    apply Integrable.of_bound (hF.pow_const 2).aestronglyMeasurable (B^2)
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hsquare x
  have hmean : Tendsto (fun n => ∫ x, (F x)^2 + δ n ∂μ) atTop
      (𝓝 (∫ x, (F x)^2 ∂μ)) := by
    have h := (tendsto_const_nhds (x := ∫ x, (F x)^2 ∂μ)).add hδlim
    convert h using 1
    · funext n
      rw [integral_add hInt (integrable_const (δ n))]
      simp
    · simp
  have hmeanlog := Real.continuous_mul_log.continuousAt.tendsto.comp hmean
  simpa only [LOOConcentration.entropy, Function.comp_def] using hDCT.sub hmeanlog

/-- The actual same-density consumer removes epsilon after its uniform bound
has been supplied by the product-generator producer. This is an internal
assembly helper; that producer remains an explicit obligation. -/
theorem entropy_square_le_of_all_positive_regularizations
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (F : α → ℝ) (hF : Measurable F) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ x, |F x| ≤ B) (K : ℝ)
    (hregularized : ∀ ε : ℝ, 0 < ε →
      LOOConcentration.entropy μ (fun x => (F x)^2 + ε) ≤ K) :
    LOOConcentration.entropy μ (fun x => (F x)^2) ≤ K := by
  let δ : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have hδpos (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  have hδle (n : ℕ) : δ n ≤ 1 := by
    dsimp [δ]
    exact inv_le_one_of_one_le₀ (le_add_of_nonneg_left (Nat.cast_nonneg n))
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hδlim : Tendsto δ atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hden
  have hlim := tendsto_entropy_square_add_regularization μ F hF B hB hbound δ
    (fun n => ⟨(hδpos n).le, hδle n⟩) hδlim
  exact le_of_tendsto hlim (Eventually.of_forall fun n => hregularized (δ n) (hδpos n))
end LOOConcentration.Revision
