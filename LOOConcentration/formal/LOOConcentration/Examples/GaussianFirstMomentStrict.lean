import LOOConcentration.Examples.OlsReferencePoint
import Mathlib.Tactic

set_option autoImplicit false

namespace LOOConcentration

open MeasureTheory Set
open scoped ENNReal NNReal

/-- The nonnegative pointwise gap between `(1+x^2)/2` and `|x|`. -/
noncomputable def gaussianAbsMomentGap (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (1 + x ^ 2) - |x|

private theorem gaussianAbsMomentGap_eq_half_sq (x : ℝ) :
    gaussianAbsMomentGap x = (|x| - 1) ^ 2 / 2 := by
  dsimp [gaussianAbsMomentGap]
  nlinarith [sq_abs x]

private theorem standardGaussian_id_memLp (p : ℝ≥0) :
    MemLp (id : ℝ → ℝ) p olsTestGaussian := by
  exact ProbabilityTheory.memLp_id_gaussianReal p

private theorem standardGaussian_abs_integrable :
    Integrable (fun x : ℝ => |x|) olsTestGaussian := by
  have hid : Integrable (id : ℝ → ℝ) olsTestGaussian :=
    (standardGaussian_id_memLp 1).integrable (by norm_num)
  simpa only [Real.norm_eq_abs, id_eq] using hid.abs

private theorem standardGaussian_sq_integrable :
    Integrable (fun x : ℝ => x ^ 2) olsTestGaussian :=
  (standardGaussian_id_memLp 2).integrable_sq

private theorem standardGaussian_sq_integral :
    (∫ x : ℝ, x ^ 2 ∂olsTestGaussian) = 1 := by
  have hv := ProbabilityTheory.variance_id_gaussianReal
    (μ := 0) (v := (1 : ℝ≥0))
  change ProbabilityTheory.variance (fun x : ℝ => x) olsTestGaussian = 1 at hv
  rw [ProbabilityTheory.variance_eq_integral
    (X := fun x : ℝ => x) (μ := olsTestGaussian) measurable_id'.aemeasurable] at hv
  simpa [ProbabilityTheory.integral_id_gaussianReal] using hv

private theorem gaussianAbsMomentGap_integrable :
    Integrable gaussianAbsMomentGap olsTestGaussian := by
  have hpoly : Integrable (fun x : ℝ => 1 + x ^ 2) olsTestGaussian :=
    (integrable_const (1 : ℝ)).add standardGaussian_sq_integrable
  exact (hpoly.const_mul (1 / 2 : ℝ)).sub standardGaussian_abs_integrable

private theorem gaussianAbsMomentGap_nonneg (x : ℝ) :
    0 ≤ gaussianAbsMomentGap x := by
  rw [gaussianAbsMomentGap_eq_half_sq]
  positivity

private theorem gaussianAbsMomentGap_integral_eq :
    (∫ x : ℝ, gaussianAbsMomentGap x ∂olsTestGaussian) =
      1 - ∫ x : ℝ, |x| ∂olsTestGaussian := by
  have hpoly : Integrable (fun x : ℝ => 1 + x ^ 2) olsTestGaussian :=
    (integrable_const (1 : ℝ)).add standardGaussian_sq_integrable
  have hhalf : Integrable
      (fun x : ℝ => (1 / 2 : ℝ) * (1 + x ^ 2)) olsTestGaussian :=
    hpoly.const_mul (1 / 2 : ℝ)
  have hpolyIntegral :
    (∫ x : ℝ, 1 + x ^ 2 ∂olsTestGaussian) = 2 := by
    rw [integral_add (integrable_const (1 : ℝ)) standardGaussian_sq_integrable]
    norm_num [standardGaussian_sq_integral]
  calc
    _ = (∫ x : ℝ, (1 / 2 : ℝ) * (1 + x ^ 2) ∂olsTestGaussian) -
        ∫ x : ℝ, |x| ∂olsTestGaussian := by
      exact integral_sub hhalf standardGaussian_abs_integrable
    _ = (1 / 2 : ℝ) *
        (∫ x : ℝ, 1 + x ^ 2 ∂olsTestGaussian) -
        ∫ x : ℝ, |x| ∂olsTestGaussian := by rw [integral_const_mul]
    _ = 1 - ∫ x : ℝ, |x| ∂olsTestGaussian := by rw [hpolyIntegral]; norm_num

private theorem standardGaussian_interval_pos :
    0 < olsTestGaussian (Ioo (-1 / 2 : ℝ) (1 / 2 : ℝ)) := by
  have hvolume : volume (Ioo (-1 / 2 : ℝ) (1 / 2 : ℝ)) = 1 := by
    rw [Real.volume_Ioo]
    norm_num
  have hac : volume ≪ olsTestGaussian :=
    ProbabilityTheory.gaussianReal_absolutelyContinuous'
      (μ := 0) (v := (1 : ℝ≥0)) (by norm_num)
  by_contra hnot
  have hzero : olsTestGaussian (Ioo (-1 / 2 : ℝ) (1 / 2 : ℝ)) = 0 :=
    le_antisymm (le_of_not_gt hnot) (by positivity)
  have hvolumeZero : volume (Ioo (-1 / 2 : ℝ) (1 / 2 : ℝ)) = 0 :=
    hac hzero
  rw [hvolume] at hvolumeZero
  norm_num at hvolumeZero

private theorem gaussianAbsMomentGap_support_pos :
    0 < olsTestGaussian (Function.support gaussianAbsMomentGap) := by
  have hsubset : Ioo (-1 / 2 : ℝ) (1 / 2 : ℝ) ⊆
      Function.support gaussianAbsMomentGap := by
    intro x hx
    rw [Function.mem_support, gaussianAbsMomentGap_eq_half_sq]
    have hxabs : |x| < 1 / 2 :=
      abs_lt.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hne : |x| - 1 ≠ 0 := by linarith
    exact ne_of_gt (div_pos (sq_pos_of_ne_zero hne) (by norm_num))
  exact lt_of_lt_of_le standardGaussian_interval_pos (measure_mono hsubset)

theorem standardGaussian_abs_integral_lt_one :
    (∫ x : ℝ, |x| ∂olsTestGaussian) < 1 := by
  have hgap_pos : 0 < ∫ x : ℝ, gaussianAbsMomentGap x ∂olsTestGaussian :=
    (integral_pos_iff_support_of_nonneg gaussianAbsMomentGap_nonneg
      gaussianAbsMomentGap_integrable).2 gaussianAbsMomentGap_support_pos
  rw [gaussianAbsMomentGap_integral_eq] at hgap_pos
  linarith

/-- The actual OLS reference error is strictly below one in absolute value. -/
theorem olsReferencePoint_testError_abs_lt_one (n : ℕ) :
    |olsTestError (olsReferencePoint n)| < 1 := by
  rw [olsReferencePoint_testError_eq_firstMoment]
  have hmoment_nonneg : 0 ≤ ∫ x : ℝ, |x| ∂olsTestGaussian :=
    integral_nonneg (fun _ => abs_nonneg _)
  rw [abs_of_nonneg hmoment_nonneg]
  exact standardGaussian_abs_integral_lt_one

theorem olsReferencePoint_testError_lt_one (n : ℕ) :
    olsTestError (olsReferencePoint n) < 1 := by
  rw [olsReferencePoint_testError_eq_firstMoment]
  exact standardGaussian_abs_integral_lt_one

#print axioms gaussianAbsMomentGap_integrable
#print axioms gaussianAbsMomentGap_integral_eq
#print axioms standardGaussian_interval_pos
#print axioms standardGaussian_abs_integral_lt_one
#print axioms olsReferencePoint_testError_abs_lt_one
#print axioms olsReferencePoint_testError_lt_one

end LOOConcentration
