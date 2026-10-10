import LOOConcentration.FunctionalInequalities.WeightedLogSum
import LOOConcentration.FunctionalInequalities.EntropyTensorization
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Entropy of bounded positive mixtures

The bounded-positive mixture inequality follows by applying the reviewed
integral log-sum inequality to each section and then using Fubini. This scope
includes bounded exponential and regularized power tests; it does not prove
the full product log-Sobolev inequality.
-/

set_option autoImplicit false

namespace LOOConcentration

open MeasureTheory

private theorem log_norm_le_endpoints
    {ε B t : ℝ} (hε : 0 < ε) (ht : t ∈ Set.Icc ε B) :
    ‖Real.log t‖ ≤ max ‖Real.log ε‖ ‖Real.log B‖ := by
  have htpos : 0 < t := lt_of_lt_of_le hε ht.1
  have hloglo : Real.log ε ≤ Real.log t := Real.log_le_log hε ht.1
  have hloghi : Real.log t ≤ Real.log B := Real.log_le_log htpos ht.2
  have hεmax : ‖Real.log ε‖ ≤ max ‖Real.log ε‖ ‖Real.log B‖ := le_max_left _ _
  have hBmax : ‖Real.log B‖ ≤ max ‖Real.log ε‖ ‖Real.log B‖ := le_max_right _ _
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · calc
      -max ‖Real.log ε‖ ‖Real.log B‖ ≤ -‖Real.log ε‖ := neg_le_neg hεmax
      _ ≤ Real.log ε := by
        rw [Real.norm_eq_abs]
        exact neg_abs_le _
      _ ≤ Real.log t := hloglo
  · exact hloghi.trans ((le_abs_self _).trans hBmax)

private theorem bounded_ratio_log_norm
    (ε B t s : ℝ) (hε : 0 < ε)
    (ht : t ∈ Set.Icc ε B) (hs : s ∈ Set.Icc ε B) :
    ‖t * Real.log (t / s)‖ ≤
      B * (max ‖Real.log ε‖ ‖Real.log B‖ + max ‖Real.log ε‖ ‖Real.log B‖) := by
  have htpos : 0 < t := lt_of_lt_of_le hε ht.1
  have hspos : 0 < s := lt_of_lt_of_le hε hs.1
  have hlogt := log_norm_le_endpoints hε ht
  have hlogs := log_norm_le_endpoints hε hs
  calc
    ‖t * Real.log (t / s)‖ = t * ‖Real.log (t / s)‖ := by
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos htpos]
    _ = t * ‖Real.log t - Real.log s‖ := by
      rw [Real.log_div htpos.ne' hspos.ne']
    _ ≤ t * (‖Real.log t‖ + ‖Real.log s‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) htpos.le
    _ ≤ B * (max ‖Real.log ε‖ ‖Real.log B‖ + max ‖Real.log ε‖ ‖Real.log B‖) :=
      mul_le_mul ht.2 (add_le_add hlogt hlogs)
        (add_nonneg (norm_nonneg _) (norm_nonneg _))
        (lt_of_lt_of_le htpos ht.2).le

private theorem integrable_mul_log_on_Icc
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {ε B : ℝ} (hε : 0 < ε) {f : α → ℝ} (hf : Measurable f)
    (hvalues : ∀ x, f x ∈ Set.Icc ε B) :
    Integrable (fun x => f x * Real.log (f x)) μ := by
  let L : ℝ := max ‖Real.log ε‖ ‖Real.log B‖
  have hLnonneg : 0 ≤ L := le_trans (norm_nonneg _) (le_max_left _ _)
  refine Integrable.of_bound
    ((Real.continuous_mul_log.measurable.comp hf).aestronglyMeasurable) (B * L) ?_
  filter_upwards with x
  have hx := hvalues x
  have hxpos : 0 < f x := lt_of_lt_of_le hε hx.1
  have hBpos : 0 < B := lt_of_lt_of_le hxpos hx.2
  have hnormx : ‖f x‖ ≤ B := by
    rw [Real.norm_eq_abs, abs_of_pos hxpos]
    exact hx.2
  have hlogx : ‖Real.log (f x)‖ ≤ L := by
    dsimp [L]
    exact log_norm_le_endpoints hε hx
  calc
    ‖f x * Real.log (f x)‖ = ‖f x‖ * ‖Real.log (f x)‖ := norm_mul _ _
    _ ≤ B * L := mul_le_mul hnormx hlogx (norm_nonneg _) hBpos.le

/-- For a bounded-positive measurable function on a probability product, the
entropy of its average in the first coordinate is at most the average of the
section entropies. All logarithmic integrands are obtained as integrable
functions from the common positive lower bound. -/
theorem entropy_mixture_bounded_positive
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : α × β → ℝ) (ε B : ℝ)
    (hF : Measurable F) (hε : 0 < ε)
    (hF_bounds : ∀ p, ε ≤ F p ∧ F p ≤ B) :
    entropy ν (fun y => ∫ x, F (x, y) ∂μ) ≤
      ∫ x, entropy ν (fun y => F (x, y)) ∂μ := by
  let m : α → ℝ := fun x => ∫ y, F (x, y) ∂ν
  let h : β → ℝ := fun y => ∫ x, F (x, y) ∂μ
  let M : ℝ := ∫ x, m x ∂μ
  let K : α × β → ℝ := fun p => F p * Real.log (F p / m p.1)
  have hF_values (p : α × β) : F p ∈ Set.Icc ε B := ⟨(hF_bounds p).1, (hF_bounds p).2⟩
  have hF_int : Integrable F (μ.prod ν) :=
    Integrable.of_mem_Icc ε B hF.aemeasurable (Filter.Eventually.of_forall hF_values)
  have hεB : ε ≤ B := by
    calc
      ε = ∫ p : α × β, (ε : ℝ) ∂μ.prod ν := by simp
      _ ≤ ∫ p, F p ∂μ.prod ν :=
        integral_mono (integrable_const ε) hF_int (fun p => (hF_bounds p).1)
      _ ≤ ∫ p : α × β, (B : ℝ) ∂μ.prod ν :=
        integral_mono hF_int (integrable_const B) (fun p => (hF_bounds p).2)
      _ = B := by simp
  have hphi_int : Integrable (fun p : α × β => F p * Real.log (F p)) (μ.prod ν) :=
    integrable_mul_log_on_Icc (μ.prod ν) hε hF hF_values
  have hF_section_meas (x : α) : Measurable (fun y : β => F (x, y)) :=
    hF.comp (measurable_prodMk_left (x := x))
  have hF_section_int (x : α) : Integrable (fun y : β => F (x, y)) ν :=
    Integrable.of_mem_Icc ε B (hF_section_meas x).aemeasurable <|
      Filter.Eventually.of_forall fun y => hF_values (x, y)
  have hm_meas : Measurable m := by
    have hm_sm : StronglyMeasurable m := by
      change StronglyMeasurable (fun x => ∫ y, F (x, y) ∂ν)
      exact hF.stronglyMeasurable.integral_prod_right'
    exact hm_sm.measurable
  have hm_int : Integrable m μ := by
    change Integrable (fun x => ∫ y, F (x, y) ∂ν) μ
    exact hF_int.integral_prod_left
  have hm_values (x : α) : m x ∈ Set.Icc ε B := by
    constructor
    · calc
        ε = ∫ y : β, (ε : ℝ) ∂ν := by simp
        _ ≤ ∫ y, F (x, y) ∂ν :=
          integral_mono (integrable_const ε) (hF_section_int x)
            (fun y => (hF_bounds (x, y)).1)
    · calc
        m x ≤ ∫ y : β, (B : ℝ) ∂ν :=
          integral_mono (hF_section_int x) (integrable_const B)
            (fun y => (hF_bounds (x, y)).2)
        _ = B := by simp
  have hm_pos (x : α) : 0 < m x := lt_of_lt_of_le hε (hm_values x).1
  have hh_meas : Measurable h := by
    have hh_sm : StronglyMeasurable h := by
      change StronglyMeasurable (fun y => ∫ x, F (x, y) ∂μ)
      exact hF.stronglyMeasurable.integral_prod_left'
    exact hh_sm.measurable
  have hh_int : Integrable h ν := by
    change Integrable (fun y => ∫ x, F (x, y) ∂μ) ν
    exact hF_int.integral_prod_right
  have hF_reverse_section_meas (y : β) : Measurable (fun x : α => F (x, y)) :=
    hF.comp (measurable_prodMk_right (y := y))
  have hF_reverse_section_int (y : β) : Integrable (fun x : α => F (x, y)) μ :=
    Integrable.of_mem_Icc ε B (hF_reverse_section_meas y).aemeasurable <|
      Filter.Eventually.of_forall fun x => hF_values (x, y)
  have hh_values (y : β) : h y ∈ Set.Icc ε B := by
    constructor
    · calc
        ε = ∫ x : α, (ε : ℝ) ∂μ := by simp
        _ ≤ ∫ x, F (x, y) ∂μ :=
          integral_mono (integrable_const ε) (hF_reverse_section_int y)
            (fun x => (hF_bounds (x, y)).1)
    · calc
        h y ≤ ∫ x : α, (B : ℝ) ∂μ :=
          integral_mono (hF_reverse_section_int y) (integrable_const B)
            (fun x => (hF_bounds (x, y)).2)
        _ = B := by simp
  let L : ℝ := max ‖Real.log ε‖ ‖Real.log B‖
  have hLnonneg : 0 ≤ L := le_trans (norm_nonneg _) (le_max_left _ _)
  have hM_values : M ∈ Set.Icc ε B := by
    constructor
    · calc
        ε = ∫ x : α, (ε : ℝ) ∂μ := by simp
        _ ≤ ∫ x, m x ∂μ :=
          integral_mono (integrable_const ε) hm_int (fun x => (hm_values x).1)
        _ = M := rfl
    · calc
        M = ∫ x, m x ∂μ := rfl
        _ ≤ ∫ x : α, (B : ℝ) ∂μ :=
          integral_mono hm_int (integrable_const B) (fun x => (hm_values x).2)
        _ = B := by simp
  have hM_pos : 0 < M := lt_of_lt_of_le hε hM_values.1
  have hmass_swap : M = ∫ y, h y ∂ν := by
    calc
      M = ∫ x, ∫ y, F (x, y) ∂ν ∂μ := rfl
      _ = ∫ p, F p ∂μ.prod ν := (integral_prod F hF_int).symm
      _ = ∫ y, ∫ x, F (x, y) ∂μ ∂ν := integral_prod_symm F hF_int
      _ = ∫ y, h y ∂ν := rfl
  have hkernel_meas : Measurable K := by
    have hm_fst : Measurable (fun p : α × β => m p.1) := hm_meas.comp measurable_fst
    have hratio : Measurable (fun p : α × β => F p / m p.1) := hF.div hm_fst
    exact hF.mul (Real.measurable_log.comp hratio)
  have hkernel_bound (p : α × β) :
      ‖K p‖ ≤ B * (L + L) := by
    dsimp [K, L]
    exact bounded_ratio_log_norm ε B (F p) (m p.1) hε (hF_values p) (hm_values p.1)
  have hkernel_int : Integrable K (μ.prod ν) := by
    refine Integrable.of_bound hkernel_meas.aestronglyMeasurable (B * (L + L)) ?_
    exact Filter.Eventually.of_forall hkernel_bound
  have hkernel_section_meas (y : β) : Measurable (fun x : α => K (x, y)) :=
    hkernel_meas.comp (measurable_prodMk_right (y := y))
  have hkernel_section_int (y : β) : Integrable (fun x : α => K (x, y)) μ := by
    refine Integrable.of_bound (hkernel_section_meas y).aestronglyMeasurable (B * (L + L)) ?_
    exact Filter.Eventually.of_forall fun x => hkernel_bound (x, y)
  have hlogh_int : Integrable (fun y => h y * Real.log (h y)) ν :=
    integrable_mul_log_on_Icc ν hε hh_meas hh_values
  have hleft_meas : Measurable (fun y => h y * Real.log (h y / M)) := by
    have hratio : Measurable (fun y => h y / M) := hh_meas.div_const M
    exact hh_meas.mul (Real.measurable_log.comp hratio)
  have hleft_int : Integrable (fun y => h y * Real.log (h y / M)) ν := by
    refine Integrable.of_bound hleft_meas.aestronglyMeasurable (B * (L + L)) ?_
    exact Filter.Eventually.of_forall fun y =>
      bounded_ratio_log_norm ε B (h y) M hε (hh_values y) hM_values
  have hlogsum_pointwise (y : β) :
      h y * Real.log (h y / M) ≤ ∫ x, K (x, y) ∂μ := by
    have hlogsum := integral_log_sum_inequality_of_pos μ
      (fun x => F (x, y)) m hm_meas
      (fun x => le_trans hε.le (hF_bounds (x, y)).1) hm_pos
      (hF_reverse_section_int y) hm_int (hkernel_section_int y) (by
        simpa only [M] using hM_pos)
    simpa only [h, M, K, m] using hlogsum
  have hleft_eq_entropy :
      (∫ y, h y * Real.log (h y / M) ∂ν) = entropy ν h := by
    have hpoint (y : β) :
        h y * Real.log (h y / M) =
          h y * Real.log (h y) - h y * Real.log M := by
      rw [Real.log_div (ne_of_gt (lt_of_lt_of_le hε (hh_values y).1)) hM_pos.ne']
      ring
    calc
      _ = ∫ y, h y * Real.log (h y) - h y * Real.log M ∂ν :=
        integral_congr_ae (Filter.Eventually.of_forall hpoint)
      _ = (∫ y, h y * Real.log (h y) ∂ν) -
            (∫ y, h y ∂ν) * Real.log M := by
        rw [integral_sub hlogh_int (hh_int.mul_const (Real.log M)), integral_mul_const]
      _ = entropy ν h := by
        unfold entropy
        rw [← hmass_swap]
  have hpoint_ineq_integrated :=
    integral_mono hleft_int hkernel_int.integral_prod_right hlogsum_pointwise
  have hlogF_section_int (x : α) :
      Integrable (fun y => F (x, y) * Real.log (F (x, y))) ν :=
    integrable_mul_log_on_Icc ν hε (hF_section_meas x) fun y => hF_values (x, y)
  have hK_section_eq_entropy (x : α) :
      (∫ y, K (x, y) ∂ν) = entropy ν (fun y => F (x, y)) := by
    have hpoint (y : β) :
        K (x, y) =
          F (x, y) * Real.log (F (x, y)) - F (x, y) * Real.log (m x) := by
      dsimp [K]
      rw [Real.log_div (ne_of_gt (lt_of_lt_of_le hε (hF_values (x, y)).1)) (hm_pos x).ne']
      ring
    calc
      _ = ∫ y, F (x, y) * Real.log (F (x, y)) -
            F (x, y) * Real.log (m x) ∂ν :=
        integral_congr_ae (Filter.Eventually.of_forall hpoint)
      _ = (∫ y, F (x, y) * Real.log (F (x, y)) ∂ν) -
            (∫ y, F (x, y) ∂ν) * Real.log (m x) := by
        rw [integral_sub (hlogF_section_int x)
          ((hF_section_int x).mul_const (Real.log (m x))), integral_mul_const]
      _ = entropy ν (fun y => F (x, y)) := by
        unfold entropy
        dsimp [m]
  let a : α → ℝ := fun x => ∫ y, F (x, y) * Real.log (F (x, y)) ∂ν
  have ha_int : Integrable a μ := by
    change Integrable (fun x => ∫ y, F (x, y) * Real.log (F (x, y)) ∂ν) μ
    exact hphi_int.integral_prod_left
  have hmphi_int : Integrable (fun x => m x * Real.log (m x)) μ :=
    integrable_mul_log_on_Icc μ hε hm_meas hm_values
  have hsection_entropy_expand (x : α) :
      entropy ν (fun y => F (x, y)) = a x - m x * Real.log (m x) := by
    unfold entropy
    dsimp [a, m]
  have hsection_entropy_int :
      Integrable (fun x => entropy ν (fun y => F (x, y))) μ := by
    have hfun : (fun x => entropy ν (fun y => F (x, y))) =
        (fun x => a x - m x * Real.log (m x)) := funext hsection_entropy_expand
    rw [hfun]
    exact ha_int.sub hmphi_int
  have hright_eq :
      (∫ y, ∫ x, K (x, y) ∂μ ∂ν) =
        ∫ x, entropy ν (fun y => F (x, y)) ∂μ := by
    calc
      _ = ∫ x, ∫ y, K (x, y) ∂ν ∂μ := by
        calc
          _ = ∫ p, K p ∂μ.prod ν := (integral_prod_symm K hkernel_int).symm
          _ = _ := integral_prod K hkernel_int
      _ = _ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hK_section_eq_entropy
  calc
    entropy ν h = ∫ y, h y * Real.log (h y / M) ∂ν := hleft_eq_entropy.symm
    _ ≤ ∫ y, ∫ x, K (x, y) ∂μ ∂ν := hpoint_ineq_integrated
    _ = ∫ x, entropy ν (fun y => F (x, y)) ∂μ := hright_eq

/-- Bounded-positive two-factor entropy subadditivity, with coefficient one
on each coordinate conditional entropy. -/
theorem entropy_two_factor_subadditive_bounded_positive
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : α × β → ℝ) (ε B : ℝ)
    (hF : Measurable F) (hε : 0 < ε)
    (hF_bounds : ∀ p, ε ≤ F p ∧ F p ≤ B) :
    entropy (μ.prod ν) F ≤
      (∫ x, entropy ν (fun y => F (x, y)) ∂μ) +
        (∫ y, entropy μ (fun x => F (x, y)) ∂ν) := by
  have hF_nonneg (p : α × β) : 0 ≤ F p := le_trans hε.le (hF_bounds p).1
  have hF_le (p : α × β) : F p ≤ B := (hF_bounds p).2
  have hchain := entropy_two_factor_chain_rule μ ν F B hF hF_nonneg hF_le
  let Fswap : β × α → ℝ := fun p => F (p.2, p.1)
  have hFswap : Measurable Fswap := hF.comp measurable_swap
  have hFswap_bounds (p : β × α) : ε ≤ Fswap p ∧ Fswap p ≤ B :=
    hF_bounds (p.2, p.1)
  have hmix := entropy_mixture_bounded_positive ν μ Fswap ε B hFswap hε hFswap_bounds
  rw [hchain]
  exact add_le_add_right (by simpa only [Fswap] using hmix) _

end LOOConcentration
