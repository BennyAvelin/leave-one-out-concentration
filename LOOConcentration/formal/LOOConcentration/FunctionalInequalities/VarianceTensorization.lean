import LOOConcentration.FunctionalInequalities.PoincareVarianceSplit
import Mathlib.Analysis.Convex.Integral

/-!
# Variance averaging and Efron–Stein bounds

This module proves the bounded variance-averaging step and its two-factor
Efron–Stein consequence. The finite-coordinate induction is recorded in the
companion orchestration report.
-/

set_option autoImplicit false

open Filter MeasureTheory
open scoped Topology

namespace LOOConcentration

private theorem bounded_measurable_integrable
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ}
    (hf : Measurable f) (B : ℝ) (hbound : ∀ x, ‖f x‖ ≤ B) : Integrable f μ := by
  exact Integrable.of_bound hf.aestronglyMeasurable B
    (Filter.Eventually.of_forall hbound)

private theorem square_norm_bound {x B : ℝ} (hB : 0 ≤ B) (hx : |x| ≤ B) :
    ‖x ^ 2‖ ≤ B ^ 2 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x)]
  calc
    x ^ 2 = |x| ^ 2 := by rw [sq_abs]
    _ ≤ B ^ 2 := by
      have hprod := mul_nonneg (sub_nonneg.mpr hx) (add_nonneg hB (abs_nonneg x))
      nlinarith [hprod]

private theorem integralVariance_eq_integral_sub_mean_sq
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ)
    (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ) :
    integralVariance μ f = ∫ x, (f x - ∫ z, f z ∂μ) ^ 2 ∂μ := by
  let m : ℝ := ∫ x, f x ∂μ
  have hlinear : Integrable (fun x => (-2 * m) * f x) μ := hf.const_mul _
  have hconstant : Integrable (fun _ : α => m ^ 2) μ := integrable_const _
  have hpoint (x : α) : (f x - m) ^ 2 =
      f x ^ 2 + ((-2 * m) * f x + m ^ 2) := by ring
  calc
    integralVariance μ f =
        (∫ x, f x ^ 2 ∂μ) - m ^ 2 := by simp [integralVariance, m]
    _ = ∫ x, (f x - m) ^ 2 ∂μ := by
      symm
      calc
        (∫ x, (f x - m) ^ 2 ∂μ) =
            ∫ x, f x ^ 2 + ((-2 * m) * f x + m ^ 2) ∂μ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall hpoint
        _ = (∫ x, f x ^ 2 ∂μ) +
            ((∫ x, (-2 * m) * f x ∂μ) + ∫ x, m ^ 2 ∂μ) := by
          calc
            (∫ x, f x ^ 2 + ((-2 * m) * f x + m ^ 2) ∂μ) =
                (∫ x, f x ^ 2 ∂μ) + ∫ x, ((-2 * m) * f x + m ^ 2) ∂μ :=
              integral_add' hf2 (hlinear.add hconstant)
            _ = (∫ x, f x ^ 2 ∂μ) +
                ((∫ x, (-2 * m) * f x ∂μ) + ∫ x, m ^ 2 ∂μ) := by
              exact congrArg (fun t : ℝ => (∫ x, f x ^ 2 ∂μ) + t)
                (integral_add' hlinear hconstant)
        _ = (∫ x, f x ^ 2 ∂μ) - m ^ 2 := by
          rw [integral_const_mul, integral_const]
          simp [m]
          ring
    _ = ∫ x, (f x - ∫ z, f z ∂μ) ^ 2 ∂μ := by simp [m]

/-- Variance is convex under averaging a bounded measurable family of
functions: averaging in `β` cannot increase the `α`-variance. -/
theorem integralVariance_average_le
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : α × β → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hF : Measurable F) (hFbound : ∀ p, |F p| ≤ B) :
    integralVariance μ (fun x => ∫ y, F (x, y) ∂ν) ≤
      ∫ y, integralVariance μ (fun x => F (x, y)) ∂ν := by
  let G : α → ℝ := fun x => ∫ y, F (x, y) ∂ν
  let H : β → ℝ := fun y => ∫ x, F (x, y) ∂μ
  let c : ℝ := ∫ y, H y ∂ν
  let Fc : α × β → ℝ := fun p => F p - H p.2
  have hF2 : Measurable (fun p : α × β => F p ^ 2) := hF.pow_const 2
  have hF2bound (p : α × β) : ‖F p ^ 2‖ ≤ B ^ 2 := by
    exact square_norm_bound hB (hFbound p)
  have hFint : Integrable F (μ.prod ν) :=
    bounded_measurable_integrable hF B fun p => by
      simpa only [Real.norm_eq_abs] using hFbound p
  have hFsectionMeas (x : α) : Measurable (fun y : β => F (x, y)) :=
    hF.comp (measurable_prodMk_left (x := x))
  have hFsectionInt (x : α) : Integrable (fun y : β => F (x, y)) ν :=
    bounded_measurable_integrable (hFsectionMeas x) B fun y => by
      simpa only [Real.norm_eq_abs] using hFbound (x, y)
  have hFleftSectionMeas (y : β) : Measurable (fun x : α => F (x, y)) :=
    hF.comp (measurable_prodMk_right (y := y))
  have hFleftSectionInt (y : β) : Integrable (fun x : α => F (x, y)) μ :=
    bounded_measurable_integrable (hFleftSectionMeas y) B fun x => by
      simpa only [Real.norm_eq_abs] using hFbound (x, y)
  have hHstrong : StronglyMeasurable H := by
    change StronglyMeasurable (fun y => ∫ x, F (x, y) ∂μ)
    exact hF.stronglyMeasurable.integral_prod_left'
  have hHmeas : Measurable H := hHstrong.measurable
  have hHint : Integrable H ν := by
    change Integrable (fun y => ∫ x, F (x, y) ∂μ) ν
    exact hFint.integral_prod_right
  have hHbound (y : β) : |H y| ≤ B := by
    calc
      |H y| ≤ ∫ x, |F (x, y)| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ _ : α, B ∂μ :=
        integral_mono (hFleftSectionInt y).abs (integrable_const B) fun x => hFbound (x, y)
      _ = B := by simp
  have hFcmeas : Measurable Fc := hF.sub (hHmeas.comp measurable_snd)
  have hFcbound (p : α × β) : |Fc p| ≤ 2 * B := by
    dsimp [Fc]
    calc
      |F p - H p.2| ≤ |F p| + |H p.2| := abs_sub _ _
      _ ≤ B + B := add_le_add (hFbound p) (hHbound p.2)
      _ = 2 * B := by ring
  have h2B : 0 ≤ 2 * B := by positivity
  have hFc2 : Measurable (fun p : α × β => Fc p ^ 2) := hFcmeas.pow_const 2
  have hFc2bound (p : α × β) : ‖Fc p ^ 2‖ ≤ (2 * B) ^ 2 := by
    exact square_norm_bound h2B (hFcbound p)
  have hFc2int : Integrable (fun p : α × β => Fc p ^ 2) (μ.prod ν) :=
    bounded_measurable_integrable hFc2 ((2 * B) ^ 2) hFc2bound
  have hFcsectionMeas (x : α) : Measurable (fun y : β => Fc (x, y)) :=
    hFcmeas.comp (measurable_prodMk_left (x := x))
  have hFcsectionInt (x : α) : Integrable (fun y : β => Fc (x, y)) ν :=
    bounded_measurable_integrable (hFcsectionMeas x) (2 * B) fun y => by
      simpa only [Real.norm_eq_abs] using hFcbound (x, y)
  have hFcsection2Int (x : α) : Integrable (fun y : β => Fc (x, y) ^ 2) ν :=
    bounded_measurable_integrable
      ((hFc2.comp (measurable_prodMk_left (x := x)))) ((2 * B) ^ 2) fun y => hFc2bound (x, y)
  have hFcMeanStrong : StronglyMeasurable (fun x => ∫ y, Fc (x, y) ∂ν) :=
    hFcmeas.stronglyMeasurable.integral_prod_right'
  have hFcMeanBound (x : α) : |∫ y, Fc (x, y) ∂ν| ≤ 2 * B := by
    calc
      |∫ y, Fc (x, y) ∂ν| ≤ ∫ y, |Fc (x, y)| ∂ν := abs_integral_le_integral_abs
      _ ≤ ∫ _ : β, 2 * B ∂ν :=
        integral_mono (hFcsectionInt x).abs (integrable_const _) fun y => hFcbound (x, y)
      _ = 2 * B := by simp
  have hFcMean2 : Measurable (fun x => (∫ y, Fc (x, y) ∂ν) ^ 2) :=
    hFcMeanStrong.measurable.pow_const 2
  have hFcMean2bound (x : α) :
      ‖(∫ y, Fc (x, y) ∂ν) ^ 2‖ ≤ (2 * B) ^ 2 := by
    exact square_norm_bound h2B (hFcMeanBound x)
  have hFcMean2int : Integrable (fun x => (∫ y, Fc (x, y) ∂ν) ^ 2) μ :=
    bounded_measurable_integrable hFcMean2 ((2 * B) ^ 2) hFcMean2bound
  have hFcSecondInt : Integrable (fun x => ∫ y, Fc (x, y) ^ 2 ∂ν) μ :=
    hFc2int.integral_prod_left
  have hFcLeftSection2Int (y : β) : Integrable (fun x => Fc (x, y) ^ 2) μ :=
    bounded_measurable_integrable
      ((hFc2.comp (measurable_prodMk_right (y := y)))) ((2 * B) ^ 2) fun x => hFc2bound (x, y)
  have hGstrong : StronglyMeasurable G := by
    change StronglyMeasurable (fun x => ∫ y, F (x, y) ∂ν)
    exact hF.stronglyMeasurable.integral_prod_right'
  have hGmeas : Measurable G := hGstrong.measurable
  have hGbound (x : α) : |G x| ≤ B := by
    calc
      |G x| ≤ ∫ y, |F (x, y)| ∂ν := abs_integral_le_integral_abs
      _ ≤ ∫ _ : β, B ∂ν :=
        integral_mono (hFsectionInt x).abs (integrable_const B) fun y => hFbound (x, y)
      _ = B := by simp
  have hG2 : Measurable (fun x => G x ^ 2) := hGmeas.pow_const 2
  have hG2bound (x : α) : ‖G x ^ 2‖ ≤ B ^ 2 := square_norm_bound hB (hGbound x)
  have hG2int : Integrable (fun x => G x ^ 2) μ :=
    bounded_measurable_integrable hG2 (B ^ 2) hG2bound
  have hGint : Integrable G μ :=
    bounded_measurable_integrable hGmeas B fun x => by
      simpa only [Real.norm_eq_abs] using hGbound x
  have hcenterMean (x : α) : (∫ y, Fc (x, y) ∂ν) = G x - c := by
    dsimp [Fc, G, c]
    rw [integral_sub (hFsectionInt x) hHint]
  have hmean : (∫ x, G x ∂μ) = c := by
    dsimp [G, H, c]
    exact integral_integral_swap hFint
  have hvarianceLeft : integralVariance μ G = ∫ x, (G x - c) ^ 2 ∂μ := by
    rw [integralVariance_eq_integral_sub_mean_sq μ G hGint hG2int]
    rw [hmean]
  have hJensen (x : α) : (∫ y, Fc (x, y) ∂ν) ^ 2 ≤ ∫ y, Fc (x, y) ^ 2 ∂ν := by
    have hconv : ConvexOn ℝ Set.univ (fun t : ℝ => t ^ 2) :=
      (even_two : Even (2 : ℕ)).convexOn_pow
    have hj := hconv.map_integral_le (continuous_pow 2).continuousOn isClosed_univ
      (Filter.Eventually.of_forall fun y => Set.mem_univ (Fc (x, y)))
      (hFcsectionInt x) (by simpa only [Function.comp_def] using hFcsection2Int x)
    simpa only [Function.comp_def] using hj
  have hcenteredAverage :
      integralVariance μ G = ∫ x, (∫ y, Fc (x, y) ∂ν) ^ 2 ∂μ := by
    calc
      integralVariance μ G = ∫ x, (G x - c) ^ 2 ∂μ := hvarianceLeft
      _ = ∫ x, (∫ y, Fc (x, y) ∂ν) ^ 2 ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          change (G x - c) ^ 2 = (∫ y, Fc (x, y) ∂ν) ^ 2
          rw [← hcenterMean x]
  have hsectionsVariance (y : β) :
      integralVariance μ (fun x => F (x, y)) = ∫ x, Fc (x, y) ^ 2 ∂μ := by
    have hvar := integralVariance_eq_integral_sub_mean_sq μ
      (fun x => F (x, y)) (hFleftSectionInt y) (by
        exact bounded_measurable_integrable (hF2.comp (measurable_prodMk_right (y := y)))
          (B ^ 2) fun x => hF2bound (x, y))
    simpa only [H, Fc] using hvar
  have hvarianceRhs :
      (∫ y, integralVariance μ (fun x => F (x, y)) ∂ν) =
        ∫ x, ∫ y, Fc (x, y) ^ 2 ∂ν ∂μ := by
    calc
      (∫ y, integralVariance μ (fun x => F (x, y)) ∂ν) =
          ∫ y, ∫ x, Fc (x, y) ^ 2 ∂μ ∂ν := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hsectionsVariance
      _ = ∫ x, ∫ y, Fc (x, y) ^ 2 ∂ν ∂μ := by
        exact (integral_integral_swap (μ := μ) (ν := ν)
          (f := fun x y => Fc (x, y) ^ 2) hFc2int).symm
  calc
    integralVariance μ G = ∫ x, (∫ y, Fc (x, y) ∂ν) ^ 2 ∂μ := hcenteredAverage
    _ ≤ ∫ x, ∫ y, Fc (x, y) ^ 2 ∂ν ∂μ :=
      integral_mono hFcMean2int hFcSecondInt hJensen
    _ = ∫ y, integralVariance μ (fun x => F (x, y)) ∂ν := hvarianceRhs.symm

/-- The product variance is at most the sum of the two expected conditional
variances, with coefficient one on each coordinate term. -/
theorem integralVariance_prod_two_factor_efronStein
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : α × β → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hF : Measurable F) (hFbound : ∀ p, |F p| ≤ B) :
    integralVariance (μ.prod ν) F ≤
      (∫ x, integralVariance ν (fun y => F (x, y)) ∂μ) +
        ∫ y, integralVariance μ (fun x => F (x, y)) ∂ν := by
  calc
    integralVariance (μ.prod ν) F =
        (∫ x, integralVariance ν (fun y => F (x, y)) ∂μ) +
          integralVariance μ (fun x => ∫ y, F (x, y) ∂ν) :=
      integralVariance_prod_two_factor μ ν F B hB hF hFbound
    _ = integralVariance μ (fun x => ∫ y, F (x, y) ∂ν) +
        (∫ x, integralVariance ν (fun y => F (x, y)) ∂μ) := by ring
    _ ≤ (∫ y, integralVariance μ (fun x => F (x, y)) ∂ν) +
        (∫ x, integralVariance ν (fun y => F (x, y)) ∂μ) :=
      add_le_add (integralVariance_average_le μ ν F B hB hF hFbound) le_rfl
    _ = (∫ x, integralVariance ν (fun y => F (x, y)) ∂μ) +
        ∫ y, integralVariance μ (fun x => F (x, y)) ∂ν := by ring

#print axioms LOOConcentration.integralVariance_average_le
#print axioms LOOConcentration.integralVariance_prod_two_factor_efronStein

end LOOConcentration
