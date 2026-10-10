import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Weighted probability measures for integral log-sum

This module starts the reference-density construction independently of its
Jensen application. A normalized nonnegative real density defines a
probability measure, and integration under its `withDensity` measure reduces
to integration against the real density.
-/

set_option autoImplicit false

namespace LOOConcentration

open MeasureTheory
open scoped ENNReal NNReal

/-- A nonnegative integrable real density of integral one defines a
probability measure by `withDensity`. -/
theorem isProbabilityMeasure_withDensity_ofReal_of_integral_eq_one
    {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (w : α → ℝ)
    (hw_int : Integrable w ν)
    (hw_nonneg : ∀ x, 0 ≤ w x)
    (hw_integral : ∫ x, w x ∂ν = 1) :
    IsProbabilityMeasure (ν.withDensity (fun x => ENNReal.ofReal (w x))) := by
  apply isProbabilityMeasure_iff.mpr
  rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal hw_int
    (Filter.Eventually.of_forall hw_nonneg), hw_integral]
  norm_num

/-- Integrating against a real-valued `withDensity` is multiplication by its
nonnegative real density. -/
theorem integral_withDensity_ofReal_eq_integral_mul
    {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (w : α → ℝ)
    (hw_meas : Measurable w)
    (hw_nonneg : ∀ x, 0 ≤ w x)
    (F : α → ℝ) :
    (∫ x, F x ∂ν.withDensity (fun x => ENNReal.ofReal (w x))) =
      ∫ x, w x * F x ∂ν := by
  have h := integral_withDensity_eq_integral_toReal_smul
    (μ := ν) (f := fun x => ENNReal.ofReal (w x)) (by fun_prop)
    (Filter.Eventually.of_forall fun _ => by simp) F
  calc
    (∫ x, F x ∂ν.withDensity (fun x => ENNReal.ofReal (w x))) =
        ∫ x, (ENNReal.ofReal (w x)).toReal * F x ∂ν := by
      simpa only [smul_eq_mul] using h
    _ = ∫ x, w x * F x ∂ν := by
      apply integral_congr_ae
      filter_upwards [Filter.Eventually.of_forall hw_nonneg] with x hx
      rw [ENNReal.toReal_ofReal hx]

set_option linter.style.haveILetI false in
/-- Integral log-sum inequality for a strictly positive reference density.
The ratio and its `x log x` transform are integrated under the probability
measure whose density is `g / ∫ g`. -/
theorem integral_log_sum_inequality_of_pos
    {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν]
    (f g : α → ℝ)
    (hg_meas : Measurable g)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hg_pos : ∀ x, 0 < g x)
    (hf_int : Integrable f ν) (hg_int : Integrable g ν)
    (hfg_int : Integrable (fun x => f x * Real.log (f x / g x)) ν)
    (hG_pos : 0 < ∫ x, g x ∂ν) :
    (∫ x, f x ∂ν) * Real.log ((∫ x, f x ∂ν) / (∫ x, g x ∂ν)) ≤
      ∫ x, f x * Real.log (f x / g x) ∂ν := by
  let G : ℝ := ∫ x, g x ∂ν
  let w : α → ℝ := fun x => g x / G
  let q : α → ℝ := fun x => f x / g x
  let ρ : Measure α := ν.withDensity (fun x => ENNReal.ofReal (w x))
  have hG : 0 < G := by simpa [G] using hG_pos
  have hw_meas : Measurable w := hg_meas.div_const G
  have hw_int : Integrable w ν := by
    exact hg_int.div_const G
  have hw_nonneg (x : α) : 0 ≤ w x := by
    exact div_nonneg (le_of_lt (hg_pos x)) hG.le
  have hw_integral : ∫ x, w x ∂ν = 1 := by
    calc
      ∫ x, w x ∂ν = (∫ x, g x ∂ν) / G := by
        simp [w, integral_div]
      _ = 1 := by simp [G, hG.ne']
  have hρ_prob : IsProbabilityMeasure ρ := by
    dsimp [ρ]
    exact isProbabilityMeasure_withDensity_ofReal_of_integral_eq_one
      ν w hw_int hw_nonneg hw_integral
  letI : IsProbabilityMeasure ρ := hρ_prob
  have hq_weight : Integrable (fun x => w x * q x) ν := by
    have hpoint : (fun x => w x * q x) = fun x => f x / G := by
      funext x
      dsimp [w, q]
      field_simp [hG.ne', (hg_pos x).ne']
    rw [hpoint]
    exact hf_int.div_const G
  have hphi_weight :
      Integrable (fun x => w x * (q x * Real.log (q x))) ν := by
    have hpoint : (fun x => w x * (q x * Real.log (q x))) =
        fun x => (f x * Real.log (f x / g x)) / G := by
      funext x
      dsimp [w, q]
      field_simp [hG.ne', (hg_pos x).ne']
    rw [hpoint]
    exact hfg_int.div_const G
  have hdensity_meas : Measurable (fun x => ENNReal.ofReal (w x)) := by
    fun_prop
  have hdensity_lt : ∀ᵐ x ∂ν, ENNReal.ofReal (w x) < ∞ := by
    filter_upwards [] with x
    simp
  have hq_int : Integrable q ρ := by
    change Integrable q (ν.withDensity (fun x => ENNReal.ofReal (w x)))
    apply (integrable_withDensity_iff hdensity_meas hdensity_lt).2
    convert hq_weight using 1
    funext x
    rw [ENNReal.toReal_ofReal (hw_nonneg x)]
    ring
  have hphi_int : Integrable (fun x => q x * Real.log (q x)) ρ := by
    change Integrable (fun x => q x * Real.log (q x))
      (ν.withDensity (fun x => ENNReal.ofReal (w x)))
    apply (integrable_withDensity_iff hdensity_meas hdensity_lt).2
    convert hphi_weight using 1
    funext x
    rw [ENNReal.toReal_ofReal (hw_nonneg x)]
    ring
  have hq_nonneg : ∀ᵐ x ∂ρ, 0 ≤ q x :=
    Filter.Eventually.of_forall fun x => div_nonneg (hf_nonneg x) (hg_pos x).le
  have hJensen := Real.convexOn_mul_log.map_integral_le
    Real.continuous_mul_log.continuousOn isClosed_Ici hq_nonneg hq_int hphi_int
  have hq_mean : (∫ x, q x ∂ρ) = (∫ x, f x ∂ν) / G := by
    change (∫ x, q x ∂ν.withDensity (fun x => ENNReal.ofReal (w x))) = _
    rw [integral_withDensity_ofReal_eq_integral_mul ν w hw_meas hw_nonneg q]
    calc
      (∫ x, w x * q x ∂ν) = ∫ x, f x / G ∂ν := by
        apply integral_congr_ae
        filter_upwards [] with x
        dsimp [w, q]
        field_simp [hG.ne', (hg_pos x).ne']
      _ = (∫ x, f x ∂ν) / G := integral_div G f
  have hqlogq_mean :
      (∫ x, q x * Real.log (q x) ∂ρ) =
        (∫ x, f x * Real.log (f x / g x) ∂ν) / G := by
    change (∫ x, q x * Real.log (q x)
      ∂ν.withDensity (fun x => ENNReal.ofReal (w x))) = _
    rw [integral_withDensity_ofReal_eq_integral_mul ν w hw_meas hw_nonneg
      (fun x => q x * Real.log (q x))]
    calc
      (∫ x, w x * (q x * Real.log (q x)) ∂ν) =
          ∫ x, (f x * Real.log (f x / g x)) / G ∂ν := by
        apply integral_congr_ae
        filter_upwards [] with x
        dsimp [w, q]
        field_simp [hG.ne', (hg_pos x).ne']
      _ = (∫ x, f x * Real.log (f x / g x) ∂ν) / G :=
        integral_div G (fun x => f x * Real.log (f x / g x))
  have hscaled := mul_le_mul_of_nonneg_left hJensen hG.le
  calc
    (∫ x, f x ∂ν) *
        Real.log ((∫ x, f x ∂ν) / (∫ x, g x ∂ν)) =
        G * ((∫ x, q x ∂ρ) * Real.log (∫ x, q x ∂ρ)) := by
      rw [show (∫ x, g x ∂ν) = G by rfl, hq_mean]
      field_simp [hG.ne']
    _ ≤ G * (∫ x, q x * Real.log (q x) ∂ρ) := hscaled
    _ = ∫ x, f x * Real.log (f x / g x) ∂ν := by
      rw [hqlogq_mean]
      field_simp [hG.ne']

end LOOConcentration
