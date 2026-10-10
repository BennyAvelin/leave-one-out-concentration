import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Order.Compact

/-!
# Two-factor entropy chain rule

For bounded nonnegative functions on a probability product, this file proves
the direct conditional-entropy decomposition by Fubini. It is a first step
towards finite-product LSI tensorization; no LSI assertion is made here.
-/

set_option autoImplicit false

namespace LOOConcentration

open MeasureTheory

/-- Integral entropy of a nonnegative real-valued function, using `0 log 0 = 0`.
The measure need not be a probability measure for this definition. -/
noncomputable def entropy {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) : ℝ :=
  (∫ x, f x * Real.log (f x) ∂μ) -
    (∫ x, f x ∂μ) * Real.log (∫ x, f x ∂μ)

private theorem exists_mul_log_norm_bound (B : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ x ∈ Set.Icc (0 : ℝ) B, ‖x * Real.log x‖ ≤ K := by
  have hcompact : IsCompact (Set.Icc (0 : ℝ) B) := isCompact_Icc
  have hcontinuous : Continuous (fun x : ℝ => ‖x * Real.log x‖) :=
    continuous_norm.comp Real.continuous_mul_log
  obtain ⟨K, hK0, hK⟩ :=
    hcompact.bddAbove_image hcontinuous.continuousOn |>.exists_ge 0
  refine ⟨K, hK0, ?_⟩
  intro x hx
  exact hK _ ⟨x, hx, rfl⟩

private theorem integrable_mul_log_of_mem_Icc
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : Measurable f) (B : ℝ)
    (hfx : ∀ x, f x ∈ Set.Icc 0 B) :
    Integrable (fun x => f x * Real.log (f x)) μ := by
  obtain ⟨K, hK0, hK⟩ := exists_mul_log_norm_bound B
  refine Integrable.of_bound ?_ K ?_
  · exact (Real.continuous_mul_log.measurable.comp hf).aestronglyMeasurable
  · filter_upwards with x
    exact hK (f x) (hfx x)

/-- Two-factor chain rule for integral entropy. If `f` is measurable and takes
values in `[0,B]`, then its entropy under a probability product splits into
the mean conditional entropy and the entropy of the section means. -/
theorem entropy_two_factor_chain_rule
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : α × β → ℝ) (B : ℝ)
    (hf : Measurable f) (hf_nonneg : ∀ p, 0 ≤ f p) (hf_le : ∀ p, f p ≤ B) :
    entropy (μ.prod ν) f =
      (∫ x, entropy ν (fun y => f (x, y)) ∂μ) +
        entropy μ (fun x => ∫ y, f (x, y) ∂ν) := by
  let g : α → ℝ := fun x => ∫ y, f (x, y) ∂ν
  let a : α → ℝ := fun x => ∫ y, f (x, y) * Real.log (f (x, y)) ∂ν
  have hf_prod_int : Integrable f (μ.prod ν) :=
    Integrable.of_mem_Icc 0 B hf.aemeasurable <| Filter.Eventually.of_forall fun p =>
      ⟨hf_nonneg p, hf_le p⟩
  have hphi_prod_int :
      Integrable (fun p : α × β => f p * Real.log (f p)) (μ.prod ν) :=
    integrable_mul_log_of_mem_Icc (μ.prod ν) hf B fun p =>
      ⟨hf_nonneg p, hf_le p⟩
  have hf_section_meas (x : α) : Measurable (fun y : β => f (x, y)) :=
    hf.comp (measurable_prodMk_left (x := x))
  have hf_section_int (x : α) : Integrable (fun y : β => f (x, y)) ν :=
    Integrable.of_mem_Icc 0 B (hf_section_meas x).aemeasurable <|
      Filter.Eventually.of_forall fun y => ⟨hf_nonneg (x, y), hf_le (x, y)⟩
  have hg_meas : Measurable g := by
    have hg_sm : StronglyMeasurable g := by
      change StronglyMeasurable (fun x => ∫ y, f (x, y) ∂ν)
      exact hf.stronglyMeasurable.integral_prod_right'
    exact hg_sm.measurable
  have hg_int : Integrable g μ := by
    change Integrable (fun x => ∫ y, f (x, y) ∂ν) μ
    exact hf_prod_int.integral_prod_left
  have hg_nonneg (x : α) : 0 ≤ g x := by
    exact integral_nonneg fun y => hf_nonneg (x, y)
  have hg_le (x : α) : g x ≤ B := by
    calc
      g x ≤ ∫ y : β, (B : ℝ) ∂ν :=
        integral_mono (hf_section_int x) (integrable_const B) (fun y => hf_le (x, y))
      _ = B := by simp
  have hphi_g_int : Integrable (fun x => g x * Real.log (g x)) μ :=
    integrable_mul_log_of_mem_Icc μ hg_meas B fun x => ⟨hg_nonneg x, hg_le x⟩
  have ha_int : Integrable a μ := by
    change Integrable
      (fun x => ∫ y, f (x, y) * Real.log (f (x, y)) ∂ν) μ
    exact hphi_prod_int.integral_prod_left
  unfold entropy
  rw [integral_prod (fun p => f p * Real.log (f p)) hphi_prod_int,
    integral_prod f hf_prod_int]
  rw [integral_sub ha_int hphi_g_int]
  ring

end LOOConcentration
