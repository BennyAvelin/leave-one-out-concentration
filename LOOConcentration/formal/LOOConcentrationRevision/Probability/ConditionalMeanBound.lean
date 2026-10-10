import LOOConcentrationRevision.Probability.ConditionalMeanShift
import Mathlib.Probability.Moments.Variance

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory

/-- The source's raw L² bound controls the same normalized conditional mean,
with the exact bad-set factor and no variance estimate supplied as a premise. -/
theorem conditional_mean_shift_of_eLpNorm_le
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (F : α → ℝ) (hF : Measurable F) (B : NNReal)
    (hL2 : eLpNorm F 2 μ ≤ (B : ENNReal))
    (K : Set α) (hK : MeasurableSet K) (hq : 0 < μ.real K) :
    |∫ x, F x ∂normalizedRestriction μ K - ∫ x, F x ∂μ| ≤
      (B : ℝ) * Real.sqrt (μ.real Kᶜ / (1 - μ.real Kᶜ)) := by
  have hmem : MemLp F 2 μ :=
    ⟨hF.aestronglyMeasurable, hL2.trans_lt ENNReal.coe_lt_top⟩
  have hformula : eLpNorm F 2 μ =
      ENNReal.ofReal (Real.sqrt (∫ x, (F x)^2 ∂μ)) := by
    have h := hmem.eLpNorm_eq_integral_rpow_norm
      (by norm_num : (2 : ENNReal) ≠ 0) (by norm_num : (2 : ENNReal) ≠ ⊤)
    have hpow : (∫ x, ‖F x‖^(2 : ℝ) ∂μ) = ∫ x, (F x)^2 ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs]
    rw [show (2 : ENNReal).toReal = 2 by norm_num, hpow] at h
    rw [h, Real.sqrt_eq_rpow]
    congr 1
    norm_num
  have hraw : Real.sqrt (∫ x, (F x)^2 ∂μ) ≤ (B : ℝ) := by
    apply (ENNReal.ofReal_le_ofReal_iff B.coe_nonneg).mp
    rw [← hformula, ENNReal.ofReal_coe_nnreal]
    exact hL2
  have hvar : (∫ x, (F x - ∫ y, F y ∂μ)^2 ∂μ) ≤ ∫ x, (F x)^2 ∂μ := by
    rw [← ProbabilityTheory.variance_eq_integral hF.aemeasurable]
    exact ProbabilityTheory.variance_le_expectation_sq hF.aestronglyMeasurable
  have hcenter : Real.sqrt (∫ x, (F x - ∫ y, F y ∂μ)^2 ∂μ) ≤ (B : ℝ) :=
    (Real.sqrt_le_sqrt hvar).trans hraw
  have hqeq : μ.real K = 1 - μ.real Kᶜ := by
    linarith [probReal_add_probReal_compl (μ := μ) hK]
  have hqpos : 0 < 1 - μ.real Kᶜ := by rwa [← hqeq]
  have hfactor : Real.sqrt (μ.real Kᶜ * (1 - μ.real Kᶜ)) / (1 - μ.real Kᶜ) =
      Real.sqrt (μ.real Kᶜ / (1 - μ.real Kᶜ)) := by
    rw [Real.sqrt_mul (show 0 ≤ μ.real Kᶜ from measureReal_nonneg),
      Real.sqrt_div (show 0 ≤ μ.real Kᶜ from measureReal_nonneg)]
    apply (div_eq_div_iff (ne_of_gt hqpos) (ne_of_gt (Real.sqrt_pos.2 hqpos))).2
    rw [mul_assoc, Real.mul_self_sqrt hqpos.le]
  have h := conditional_mean_shift_of_memLp μ K hK F hmem hq
  rw [hfactor] at h
  exact h.trans (mul_le_mul_of_nonneg_right hcenter (Real.sqrt_nonneg _))

/-- The actual source mean-bias consumer keeps the same conditional law and
adds only the stipulated raw mean bound. -/
theorem normalized_mean_abs_le_of_eLpNorm_le
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (F : α → ℝ) (hF : Measurable F) (B δ : NNReal)
    (hL2 : eLpNorm F 2 μ ≤ (B : ENNReal))
    (hbias : |∫ x, F x ∂μ| ≤ (δ : ℝ))
    (K : Set α) (hK : MeasurableSet K) (hq : 0 < μ.real K) :
    |∫ x, F x ∂normalizedRestriction μ K| ≤
      (δ : ℝ) + (B : ℝ) * Real.sqrt (μ.real Kᶜ / (1 - μ.real Kᶜ)) := by
  have h := conditional_mean_shift_of_eLpNorm_le μ F hF B hL2 K hK hq
  calc
    _ ≤ |∫ x, F x ∂normalizedRestriction μ K - ∫ x, F x ∂μ| + |∫ x, F x ∂μ| :=
      by
        simpa only [sub_add_cancel] using (abs_add_le
          ((∫ x, F x ∂normalizedRestriction μ K) - (∫ x, F x ∂μ)) (∫ x, F x ∂μ))
    _ ≤ (B : ℝ) * Real.sqrt (μ.real Kᶜ / (1 - μ.real Kᶜ)) + (δ : ℝ) := add_le_add h hbias
    _ = _ := add_comm _ _

end LOOConcentration.Revision
