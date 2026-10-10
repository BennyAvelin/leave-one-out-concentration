import LOOConcentrationRevision.Probability.ConditionalMeanShift

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory

/-- Exact total probability for the source normalized event restriction. -/
theorem measureReal_eq_restriction_add_complement
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (K : Set α) (hK : MeasurableSet K) (hq : 0 < μ.real K) (S : Set α) :
    μ.real S = μ.real K * (normalizedRestriction μ K).real S + μ.real (S ∩ Kᶜ) := by
  have hpart := measureReal_inter_add_sdiff (μ := μ) (s := S) hK
  have hrest : (normalizedRestriction μ K).real S = (μ.real K)⁻¹ * μ.real (S ∩ K) := by
    simp only [normalizedRestriction, measureReal_ennreal_smul_apply, ENNReal.toReal_inv]
    rw [Measure.real, Measure.restrict_apply' hK]
    rfl
  rw [hrest, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hq), one_mul]
  simpa only [Set.sdiff_eq] using hpart.symm

/-- Unconditioning counts the bad event once, independently of its tail union. -/
theorem measureReal_le_complement_add_normalizedRestriction
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (K : Set α) (hK : MeasurableSet K) (hq : 0 < μ.real K) (S : Set α) :
    μ.real S ≤ μ.real Kᶜ + (normalizedRestriction μ K).real S := by
  rw [measureReal_eq_restriction_add_complement μ K hK hq S]
  have hq1 : μ.real K ≤ 1 := measureReal_le_one
  have hS : 0 ≤ (normalizedRestriction μ K).real S := measureReal_nonneg
  have hbad : μ.real (S ∩ Kᶜ) ≤ μ.real Kᶜ := measureReal_mono Set.inter_subset_right
  nlinarith

/-- Given the two actual conditional centered tails and its actual mean bound,
all three source tails follow, with only one copy of the bad-event probability. -/
theorem unconditional_tails_of_conditional_centered_tails
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (K : Set α) (hK : MeasurableSet K) (hq : 0 < μ.real K)
    (H : α → ℝ) (a ε G : ℝ) (hMean : |∫ x, H x ∂normalizedRestriction μ K| ≤ a)
    (hPlus : (normalizedRestriction μ K).real
      {x | H x - ∫ y, H y ∂normalizedRestriction μ K > ε-a} ≤ G)
    (hMinus : (normalizedRestriction μ K).real
      {x | -(H x - ∫ y, H y ∂normalizedRestriction μ K) > ε-a} ≤ G) :
    (μ.real {x | H x > ε} ≤ μ.real Kᶜ + G) ∧
    (μ.real {x | -H x > ε} ≤ μ.real Kᶜ + G) ∧
    (μ.real {x | |H x| > ε} ≤ μ.real Kᶜ + 2*G) := by
  let ν := normalizedRestriction μ K
  let : IsProbabilityMeasure ν := normalizedRestriction_isProbability μ K hq
  have hMeanLow := (abs_le.mp hMean).1
  have hMeanHigh := (abs_le.mp hMean).2
  have hpos : ν.real {x | H x > ε} ≤ G := by
    refine (measureReal_mono (μ := ν) (s₁ := {x | H x > ε})
      (s₂ := {x | H x - ∫ y, H y ∂ν > ε-a}) ?_).trans hPlus
    intro x hx
    change ε < H x at hx
    change ε-a < H x - ∫ y, H y ∂ν
    linarith
  have hneg : ν.real {x | -H x > ε} ≤ G := by
    refine (measureReal_mono (μ := ν) (s₁ := {x | -H x > ε})
      (s₂ := {x | -(H x - ∫ y, H y ∂ν) > ε-a}) ?_).trans hMinus
    intro x hx
    change ε < -H x at hx
    change ε-a < -(H x - ∫ y, H y ∂ν)
    linarith
  have habs : ν.real {x | |H x| > ε} ≤ 2*G := by
    have heq : {x | |H x| > ε} = {x | H x > ε} ∪ {x | -H x > ε} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_union, lt_abs]
    rw [heq]
    exact (measureReal_union_le _ _).trans (by linarith)
  exact ⟨(measureReal_le_complement_add_normalizedRestriction μ K hK hq _).trans
      (add_le_add le_rfl hpos),
    (measureReal_le_complement_add_normalizedRestriction μ K hK hq _).trans
      (add_le_add le_rfl hneg),
    (measureReal_le_complement_add_normalizedRestriction μ K hK hq _).trans
      (add_le_add le_rfl habs)⟩

end LOOConcentration.Revision
