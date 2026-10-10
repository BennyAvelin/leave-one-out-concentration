import LOOConcentrationManuscript.Internal.ModelSelectionDatasetConcentration
import LOOConcentration.Frozen.Foundations.LooEstimate
import LOOConcentration.Probability.DeletedTransport
import LOOConcentration.Concentration.ThetaRateFacts
import LOOConcentrationRevision.Concentration.Chernoff
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal

open MeasureTheory
open LOOConcentration.Revision
open scoped ENNReal

/-- The sharp zero-growth Gaussian tail is bounded by the source theta rate.
This includes the zero-LSI and zero-slope branches. -/
theorem signedI1_gaussian_le_thetaRate
    (C M₂ : ℝ) (hC : 0 ≤ C) (hM₂ : 0 ≤ M₂)
    (r : ℕ) (hr : 1 ≤ r) (t : ℝ) (ht : 0 < t)
    (a : ℝ) (ha : 0 ≤ a) :
    (if C * a ^ 2 = 0 then 0 else Real.exp (-(t ^ 2 / (2 * C * a ^ 2)))) ≤
      LOOConcentration.Revision.thetaRate C M₂ hC hM₂ r hr t ht a 0 ha le_rfl := by
  by_cases hC0 : C = 0
  · simp [LOOConcentration.Revision.thetaRate, hC0]
  have hCp : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
  by_cases ha0 : a = 0
  · simp [ha0, LOOConcentration.Revision.thetaRate, hC0]
  have ha2 : 0 < a ^ 2 := sq_pos_of_ne_zero ha0
  have hCa : C * a ^ 2 ≠ 0 := ne_of_gt (mul_pos hCp ha2)
  simp only [if_neg hCa, LOOConcentration.Revision.thetaRate, if_neg hC0,
    zero_pow (by norm_num : 2 ≠ 0),
    mul_zero, zero_mul, add_zero, if_neg (ne_of_gt ha2)]
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  apply div_le_div_of_nonneg_left (sq_nonneg t) (by positivity)
  nlinarith [mul_pos hCp ha2]

/-- A Borel map of the two source growth coefficients preserves almost-everywhere
strong measurability of their source rate functions. -/
theorem signedI1_thetaRate_aestronglyMeasurable
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (C M₂ : ℝ) (hC : 0 ≤ C) (hM₂ : 0 ≤ M₂)
    (r : ℕ) (hr : 1 ≤ r) (t : ℝ) (ht : 0 < t)
    (a b : Ω → ℝ)
    (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ)
    (ha0 : ∀ x, 0 ≤ a x) (hb0 : ∀ x, 0 ≤ b x) :
    AEStronglyMeasurable
      (fun x => LOOConcentration.Revision.thetaRate C M₂ hC hM₂ r hr t ht
        (a x) (b x) (ha0 x) (hb0 x)) μ := by
  let H : ℝ × ℝ → ℝ := fun p =>
    if C = 0 then 0 else
      if p.1 ^ 2 + 2 * p.2 ^ 2 * (r : ℝ) * M₂ = 0 then
        if p.2 = 0 then 0 else Real.exp (-(t / (8 * C * p.2)))
      else if p.2 = 0 then
        Real.exp (-(t ^ 2 / (8 * C * (p.1 ^ 2 + 2 * p.2 ^ 2 * (r : ℝ) * M₂))))
      else Real.exp (-(min
        (t ^ 2 / (8 * C * (p.1 ^ 2 + 2 * p.2 ^ 2 * (r : ℝ) * M₂)))
        (t / (8 * C * p.2))))
  have hH : Measurable H := by
    by_cases hC0 : C = 0
    · simp [H, hC0]
    · have hS : Measurable (fun p : ℝ × ℝ =>
          p.1 ^ 2 + 2 * p.2 ^ 2 * (r : ℝ) * M₂) := by fun_prop
      have hSzero : MeasurableSet {p : ℝ × ℝ |
          p.1 ^ 2 + 2 * p.2 ^ 2 * (r : ℝ) * M₂ = 0} :=
        measurableSet_eq_fun hS measurable_const
      have hbzero : MeasurableSet {p : ℝ × ℝ | p.2 = 0} :=
        measurableSet_eq_fun measurable_snd measurable_const
      have hlinear : Measurable (fun p : ℝ × ℝ =>
          Real.exp (-(t / (8 * C * p.2)))) := by fun_prop
      have hgaussian : Measurable (fun p : ℝ × ℝ =>
          Real.exp (-(t ^ 2 /
            (8 * C * (p.1 ^ 2 + 2 * p.2 ^ 2 * (r : ℝ) * M₂))))) := by fun_prop
      have hgeneral : Measurable (fun p : ℝ × ℝ => Real.exp (-(min
          (t ^ 2 / (8 * C * (p.1 ^ 2 + 2 * p.2 ^ 2 * (r : ℝ) * M₂)))
          (t / (8 * C * p.2))))) := by fun_prop
      change Measurable (fun p : ℝ × ℝ =>
        if C = 0 then 0 else
          if p.1 ^ 2 + 2 * p.2 ^ 2 * (r : ℝ) * M₂ = 0 then
            if p.2 = 0 then 0 else Real.exp (-(t / (8 * C * p.2)))
          else if p.2 = 0 then
            Real.exp (-(t ^ 2 /
              (8 * C * (p.1 ^ 2 + 2 * p.2 ^ 2 * (r : ℝ) * M₂))))
          else Real.exp (-(min
            (t ^ 2 / (8 * C * (p.1 ^ 2 + 2 * p.2 ^ 2 * (r : ℝ) * M₂)))
            (t / (8 * C * p.2)))))
      simp only [if_neg hC0]
      exact Measurable.ite hSzero
        (Measurable.ite hbzero measurable_const hlinear)
        (Measurable.ite hbzero hgaussian hgeneral)
  have hab : AEMeasurable (fun x => (a x, b x)) μ :=
    ha.aemeasurable.prodMk hb.aemeasurable
  have hcomp : AEMeasurable (H ∘ fun x => (a x, b x)) μ := hH.comp_aemeasurable hab
  have heq : (fun x => LOOConcentration.Revision.thetaRate C M₂ hC hM₂ r hr t ht
      (a x) (b x)
      (ha0 x) (hb0 x)) = H ∘ (fun x => (a x, b x)) := by
    funext x
    rfl
  rw [heq]
  exact hcomp.aestronglyMeasurable

/-- The revised source theta rate remains between zero and one, including the
zero-LSI branch. -/
theorem signedI1_thetaRate_bounds
    (C M₂ : ℝ) (hC : 0 ≤ C) (hM₂ : 0 ≤ M₂)
    (r : ℕ) (hr : 1 ≤ r) (t : ℝ) (ht : 0 < t)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ LOOConcentration.Revision.thetaRate C M₂ hC hM₂ r hr t ht a b ha hb ∧
      LOOConcentration.Revision.thetaRate C M₂ hC hM₂ r hr t ht a b ha hb ≤ 1 := by
  by_cases hC0 : C = 0
  · simp [LOOConcentration.Revision.thetaRate, hC0]
  · have hCp : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
    rw [LOOConcentration.Revision.thetaRate_eq_historical_of_pos
      C M₂ hCp hM₂ r hr t ht a b ha hb]
    exact ⟨LOOConcentration.thetaRate_nonneg C M₂ hCp hM₂ r hr t ht a b ha hb,
      LOOConcentration.thetaRate_le_one C M₂ hCp hM₂ r hr t ht a b ha hb⟩

/-- Integrating pointwise signed short-section tails and applying the finite
union bound gives the two tails of the literal signed leave-one-out difference.
The final actual consumer supplies the pointwise bounds from the source gradient
condition. -/
theorem signedI1_two_sided_mixture_of_pointwise
    {k m n : ℕ} (μ : Measure (LOOConcentration.Observation k m))
    [IsProbabilityMeasure μ]
    (F : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 1) ×
      LOOConcentration.Observation k m → ℝ)
    (hFmeas : Measurable F)
    (hFint : Integrable F
      ((Measure.pi fun _ : Fin (n + 1) => μ).prod μ))
    (hmeanMeas : Measurable (fun z : LOOConcentration.Observation k m =>
      ∫ D, F (D, z) ∂(Measure.pi fun _ : Fin (n + 1) => μ)))
    (rate : LOOConcentration.Observation k m → ℝ)
    (hrateInt : Integrable rate μ)
    (hrateNonneg : ∀ z, 0 ≤ rate z)
    (t : ℝ)
    (hpoint : ∀ᵐ z ∂μ,
      (Measure.pi fun _ : Fin (n + 1) => μ).real
        {D | (∫ D', F (D', z) ∂(Measure.pi fun _ : Fin (n + 1) => μ)) - F (D, z) > t} ≤
          rate z ∧
      (Measure.pi fun _ : Fin (n + 1) => μ).real
        {D | F (D, z) - (∫ D', F (D', z) ∂(Measure.pi fun _ : Fin (n + 1) => μ)) > t} ≤
          rate z) :
    let P : Measure (LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 2)) :=
      Measure.pi fun _ : Fin (n + 2) => μ
    let f : LOOConcentration.Observation k m → ℝ := fun z =>
      ∫ D, F (D, z) ∂(Measure.pi fun _ : Fin (n + 1) => μ)
    let I₁ : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 2) → ℝ := fun D =>
      (∑ i : Fin (n + 2), f (D i)) / (n + 2 : ℝ) -
        (∑ i : Fin (n + 2), F (LOOConcentration.deleteAt D i, D i)) /
          (n + 2 : ℝ)
    Integrable I₁ P ∧
      P.real {D | I₁ D > t} ≤ (n + 2 : ℝ) * ∫ z, rate z ∂μ ∧
      P.real {D | -I₁ D > t} ≤ (n + 2 : ℝ) * ∫ z, rate z ∂μ := by
  dsimp only
  let P : Measure (LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 2)) :=
    Measure.pi fun _ : Fin (n + 2) => μ
  let Q : Measure (LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 1)) :=
    Measure.pi fun _ : Fin (n + 1) => μ
  let f : LOOConcentration.Observation k m → ℝ := fun z => ∫ D, F (D, z) ∂Q
  let Y : Fin (n + 2) → LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 2) → ℝ :=
    fun i D => f (D i) - F (LOOConcentration.deleteAt D i, D i)
  let I₁ : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 2) → ℝ :=
    fun D => (∑ i : Fin (n + 2), f (D i)) / (n + 2 : ℝ) -
      (∑ i : Fin (n + 2), F (LOOConcentration.deleteAt D i, D i)) /
        (n + 2 : ℝ)
  have hFint' : Integrable F (Q.prod μ) := by simpa only [Q] using hFint
  have hf : Integrable f μ := by
    simpa only [f] using hFint'.integral_prod_right
  have hcoord : ∀ i : Fin (n + 2),
      Integrable (fun D : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 2) =>
        f (D i)) P := by
    intro i
    exact (LOOConcentration.sample_coordinate_measurePreserving μ i).integrable_comp_of_integrable hf
  have hdelete : ∀ i : Fin (n + 2),
      Integrable (fun D : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 2) =>
        F (LOOConcentration.deleteAt D i, D i)) P := by
    intro i
    exact LOOConcentration.deleted_section_integrable μ i F hFint'
  have hVint : Integrable
      (fun D : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 2) =>
        (∑ i : Fin (n + 2), f (D i)) / (n + 2 : ℝ)) P :=
    (integrable_finsetSum Finset.univ (fun i _ => hcoord i)).div_const _
  have hEint : Integrable
      (fun D : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 2) =>
        (∑ i : Fin (n + 2), F (LOOConcentration.deleteAt D i, D i)) /
          (n + 2 : ℝ)) P :=
    (integrable_finsetSum Finset.univ (fun i _ => hdelete i)).div_const _
  have hIint : Integrable I₁ P := by
    exact hVint.sub hEint
  have hXmeas : Measurable (fun p :
      LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 1) ×
        LOOConcentration.Observation k m => f p.2 - F p) := by
    exact (hmeanMeas.comp measurable_snd).sub hFmeas
  let Splus : Set (LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 1) ×
      LOOConcentration.Observation k m) := {p | f p.2 - F p > t}
  let Sminus : Set (LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 1) ×
      LOOConcentration.Observation k m) := {p | F p - f p.2 > t}
  have hSplus : MeasurableSet Splus :=
    measurableSet_Ioi.preimage hXmeas
  have hnegXmeas : Measurable (fun p :
      LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 1) ×
        LOOConcentration.Observation k m => F p - f p.2) := by
    have heq : (fun p : LOOConcentration.Dataset
        (LOOConcentration.Observation k m) (n + 1) × LOOConcentration.Observation k m =>
          F p - f p.2) = -fun p => f p.2 - F p := by
      funext p
      exact (neg_sub (f p.2) (F p)).symm
    rw [heq]
    exact hXmeas.neg
  have hSminus : MeasurableSet Sminus :=
    measurableSet_Ioi.preimage hnegXmeas
  have hproduct (S : Set (LOOConcentration.Dataset
      (LOOConcentration.Observation k m) (n + 1) × LOOConcentration.Observation k m))
      (hS : MeasurableSet S) :
      (Q.prod μ) S = ∫⁻ z, Q ((fun D => (D, z)) ⁻¹' S) ∂μ :=
    Measure.prod_apply_symm hS
  have hsectionPlus (z : LOOConcentration.Observation k m) :
      Q ((fun D => (D, z)) ⁻¹' Splus) =
        Q {D | f z - F (D, z) > t} := by
    rfl
  have hsectionMinus (z : LOOConcentration.Observation k m) :
      Q ((fun D => (D, z)) ⁻¹' Sminus) =
        Q {D | F (D, z) - f z > t} := by
    rfl
  have hqPlus : ∀ᵐ z ∂μ,
      Q ((fun D => (D, z)) ⁻¹' Splus) ≤ ENNReal.ofReal (rate z) := by
    filter_upwards [hpoint] with z hz
    have hfinite : Q {D | f z - F (D, z) > t} ≠ ⊤ := measure_ne_top _ _
    have hreal : (Q {D | f z - F (D, z) > t}).toReal ≤ rate z := by
      simpa only [Measure.real_def, f, Q] using hz.1
    rw [hsectionPlus z, ← ENNReal.ofReal_toReal hfinite]
    exact ENNReal.ofReal_le_ofReal hreal
  have hqMinus : ∀ᵐ z ∂μ,
      Q ((fun D => (D, z)) ⁻¹' Sminus) ≤ ENNReal.ofReal (rate z) := by
    filter_upwards [hpoint] with z hz
    have hfinite : Q {D | F (D, z) - f z > t} ≠ ⊤ := measure_ne_top _ _
    have hreal : (Q {D | F (D, z) - f z > t}).toReal ≤ rate z := by
      simpa only [Measure.real_def, f, Q] using hz.2
    rw [hsectionMinus z, ← ENNReal.ofReal_toReal hfinite]
    exact ENNReal.ofReal_le_ofReal hreal
  have hlintegral : ∫⁻ z, ENNReal.ofReal (rate z) ∂μ =
      ENNReal.ofReal (∫ z, rate z ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal hrateInt
      (Filter.Eventually.of_forall hrateNonneg)).symm
  have hmixPlus : (Q.prod μ) Splus ≤ ENNReal.ofReal (∫ z, rate z ∂μ) := by
    rw [hproduct Splus hSplus]
    exact (lintegral_mono_ae hqPlus).trans_eq hlintegral
  have hmixMinus : (Q.prod μ) Sminus ≤ ENNReal.ofReal (∫ z, rate z ∂μ) := by
    rw [hproduct Sminus hSminus]
    exact (lintegral_mono_ae hqMinus).trans_eq hlintegral
  have hYiPlus (i : Fin (n + 2)) : P.real {D | Y i D > t} ≤ ∫ z, rate z ∂μ := by
    have hmap := LOOConcentration.deleted_tail_integral μ i Splus hSplus
    have hEq : {D | Y i D > t} =
        (fun D : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 2) =>
          (LOOConcentration.deleteAt D i, D i)) ⁻¹' Splus := by
      ext D
      simp [Y, Splus, f]
    rw [Measure.real_def, hEq, hmap]
    have hnonneg : 0 ≤ ∫ z, rate z ∂μ :=
      integral_nonneg_of_ae (Filter.Eventually.of_forall hrateNonneg)
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hmixPlus).trans_eq
      (ENNReal.toReal_ofReal hnonneg)
  have hYiMinus (i : Fin (n + 2)) : P.real {D | -Y i D > t} ≤ ∫ z, rate z ∂μ := by
    have hmap := LOOConcentration.deleted_tail_integral μ i Sminus hSminus
    have hEq : {D | -Y i D > t} =
        (fun D : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 2) =>
          (LOOConcentration.deleteAt D i, D i)) ⁻¹' Sminus := by
      ext D
      simp [Y, Sminus, f]
    rw [Measure.real_def, hEq, hmap]
    have hnonneg : 0 ≤ ∫ z, rate z ∂μ :=
      integral_nonneg_of_ae (Filter.Eventually.of_forall hrateNonneg)
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hmixMinus).trans_eq
      (ENNReal.toReal_ofReal hnonneg)
  have hIeq (D : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 2)) :
      I₁ D = (∑ i : Fin (n + 2), Y i D) / (n + 2 : ℝ) := by
    dsimp [I₁, Y]
    rw [Finset.sum_sub_distrib, ← sub_div]
  have hN : 0 < (n + 2 : ℝ) := by positivity
  have hsubset : {D | I₁ D > t} ⊆ ⋃ i : Fin (n + 2), {D | Y i D > t} := by
    intro D hD
    by_contra hnone
    have hcoord' : ∀ i, Y i D ≤ t := by
      intro i
      exact le_of_not_gt (fun hh => hnone (Set.mem_iUnion.mpr ⟨i, hh⟩))
    have hsum : (∑ i : Fin (n + 2), Y i D) ≤ (n + 2 : ℝ) * t := by
      calc
        _ ≤ ∑ _i : Fin (n + 2), t := Finset.sum_le_sum fun i hi => hcoord' i
        _ = (n + 2 : ℝ) * t := by simp
    have hsum' : (∑ i : Fin (n + 2), Y i D) ≤ t * (n + 2 : ℝ) := by
      simpa [mul_comm] using hsum
    change I₁ D > t at hD
    rw [hIeq] at hD
    have hdiv : (∑ i : Fin (n + 2), Y i D) / (n + 2 : ℝ) ≤ t :=
      (div_le_iff₀ hN).2 hsum'
    linarith
  have hsubsetNeg : {D | -I₁ D > t} ⊆ ⋃ i : Fin (n + 2), {D | -Y i D > t} := by
    intro D hD
    by_contra hnone
    have hcoord' : ∀ i, -Y i D ≤ t := by
      intro i
      exact le_of_not_gt (fun hh => hnone (Set.mem_iUnion.mpr ⟨i, hh⟩))
    have hsum : (∑ i : Fin (n + 2), -Y i D) ≤ (n + 2 : ℝ) * t := by
      calc
        _ ≤ ∑ _i : Fin (n + 2), t := Finset.sum_le_sum fun i hi => hcoord' i
        _ = (n + 2 : ℝ) * t := by simp
    have hsum' : (∑ i : Fin (n + 2), -Y i D) ≤ t * (n + 2 : ℝ) := by
      simpa [mul_comm] using hsum
    have hNegEq : -I₁ D = (∑ i : Fin (n + 2), -Y i D) / (n + 2 : ℝ) := by
      rw [hIeq, Finset.sum_neg_distrib, neg_div]
    change -I₁ D > t at hD
    rw [hNegEq] at hD
    have hdiv : (∑ i : Fin (n + 2), -Y i D) / (n + 2 : ℝ) ≤ t :=
      (div_le_iff₀ hN).2 hsum'
    linarith
  have hsumPlus : ∑ i : Fin (n + 2), P.real {D | Y i D > t} ≤
      (n + 2 : ℝ) * ∫ z, rate z ∂μ := by
    calc
      _ ≤ ∑ _i : Fin (n + 2), ∫ z, rate z ∂μ := Finset.sum_le_sum fun i hi => hYiPlus i
      _ = (n + 2 : ℝ) * ∫ z, rate z ∂μ := by simp
  have hsumMinus : ∑ i : Fin (n + 2), P.real {D | -Y i D > t} ≤
      (n + 2 : ℝ) * ∫ z, rate z ∂μ := by
    calc
      _ ≤ ∑ _i : Fin (n + 2), ∫ z, rate z ∂μ := Finset.sum_le_sum fun i hi => hYiMinus i
      _ = (n + 2 : ℝ) * ∫ z, rate z ∂μ := by simp
  refine ⟨hIint, ?_, ?_⟩
  · calc
      P.real {D | I₁ D > t} ≤ P.real (⋃ i : Fin (n + 2), {D | Y i D > t}) :=
        measureReal_mono hsubset
      _ ≤ ∑ i : Fin (n + 2), P.real {D | Y i D > t} := measureReal_iUnion_fintype_le _
      _ ≤ (n + 2 : ℝ) * ∫ z, rate z ∂μ := hsumPlus
  · calc
      P.real {D | -I₁ D > t} ≤ P.real (⋃ i : Fin (n + 2), {D | -Y i D > t}) :=
        measureReal_mono hsubsetNeg
      _ ≤ ∑ i : Fin (n + 2), P.real {D | -Y i D > t} := measureReal_iUnion_fintype_le _
      _ ≤ (n + 2 : ℝ) * ∫ z, rate z ∂μ := hsumMinus

end LOOConcentration.Manuscript.Internal
