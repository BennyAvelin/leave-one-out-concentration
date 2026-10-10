import LOOConcentration.Frozen.Concentration.ThetaRate
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Chernoff optimization for the quadratic-gradient MGF

These are conditional provider lemmas for `cor:quadconc#chernoff`. The MGF
premises are supplied by `lemma:quadratic`; they do not close that graph node
on their own. This module imports the frozen rate definition, not a draft
result anchor.
-/

set_option autoImplicit false

namespace LOOConcentration

open MeasureTheory

/-- Markov's inequality in the form used by the Chernoff argument. -/
private theorem measureReal_gt_le_exp_of_mgf
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (X : α → ℝ) (t lam q : ℝ) (hlam : 0 < lam)
    (hExp : Integrable (fun x => Real.exp (lam * X x)) μ)
    (hMgf : (∫ x, Real.exp (lam * X x) ∂μ) ≤ Real.exp q) :
    μ.real {x | X x > t} ≤ Real.exp (-lam * t + q) := by
  let g : α → ℝ := fun x => Real.exp (lam * (X x - t))
  have hg_eq : g = fun x => Real.exp (-lam * t) * Real.exp (lam * X x) := by
    funext x
    dsimp [g]
    calc
      Real.exp (lam * (X x - t)) = Real.exp ((-lam) * t + lam * X x) := by
        congr 1
        ring
      _ = Real.exp (-lam * t) * Real.exp (lam * X x) := Real.exp_add _ _
  have hg : Integrable g μ := by
    rw [hg_eq]
    exact hExp.const_mul _
  have hpoint : ∀ x ∈ {x | X x > t}, 1 ≤ g x := by
    intro x hx
    change 1 ≤ Real.exp (lam * (X x - t))
    apply Real.one_le_exp_iff.2
    exact le_of_lt (mul_pos hlam (sub_pos.mpr hx))
  have hnonneg : 0 ≤ᵐ[μ] g := by
    filter_upwards [] with x
    exact (Real.exp_pos _).le
  have hmarkENN : μ {x | X x > t} ≤ ENNReal.ofReal (∫ x, g x ∂μ) :=
    hg.measure_le_integral hnonneg hpoint
  have hmark : μ.real {x | X x > t} ≤ ∫ x, g x ∂μ := by
    rw [measureReal_def]
    have htoReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmarkENN
    rw [ENNReal.toReal_ofReal (integral_nonneg_of_ae hnonneg)] at htoReal
    exact htoReal
  have hInt : (∫ x, g x ∂μ) =
      Real.exp (-lam * t) * ∫ x, Real.exp (lam * X x) ∂μ := by
    rw [hg_eq, integral_const_mul]
  calc
    μ.real {x | X x > t} ≤ ∫ x, g x ∂μ := hmark
    _ = Real.exp (-lam * t) * ∫ x, Real.exp (lam * X x) ∂μ := hInt
    _ ≤ Real.exp (-lam * t) * Real.exp q :=
      mul_le_mul_of_nonneg_left hMgf (Real.exp_pos _).le
    _ = Real.exp (-lam * t + q) := by rw [← Real.exp_add]

/-- Negating a centered variable preserves a symmetric cutoff MGF premise. -/
private theorem neg_cutoff_mgf
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (X : α → ℝ) (V Λ : ℝ)
    (hMgf : ∀ s : ℝ, |s| ≤ Λ →
      Integrable (fun x => Real.exp (s * X x)) μ ∧
        (∫ x, Real.exp (s * X x) ∂μ) ≤ Real.exp (V * s ^ 2)) :
    ∀ s : ℝ, |s| ≤ Λ →
      Integrable (fun x => Real.exp (s * (-X x))) μ ∧
        (∫ x, Real.exp (s * (-X x)) ∂μ) ≤ Real.exp (V * s ^ 2) := by
  intro s hs
  have h := hMgf (-s) (by simpa using hs)
  have heq : (fun x => Real.exp (s * (-X x))) =
      fun x => Real.exp ((-s) * X x) := by
    funext x
    congr 1
    ring
  constructor
  · rw [heq]
    exact h.1
  · calc
      (∫ x, Real.exp (s * (-X x)) ∂μ) =
          ∫ x, Real.exp ((-s) * X x) ∂μ := by rw [heq]
      _ ≤ Real.exp (V * (-s) ^ 2) := h.2
      _ = Real.exp (V * s ^ 2) := by
        congr 1
        ring

/-- Negating an all-real MGF premise. -/
private theorem neg_all_mgf
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (X : α → ℝ) (Q : ℝ)
    (hMgf : ∀ s : ℝ,
      Integrable (fun x => Real.exp (s * X x)) μ ∧
        (∫ x, Real.exp (s * X x) ∂μ) ≤ Real.exp (Q * s ^ 2)) :
    ∀ s : ℝ,
      Integrable (fun x => Real.exp (s * (-X x))) μ ∧
        (∫ x, Real.exp (s * (-X x)) ∂μ) ≤ Real.exp (Q * s ^ 2) := by
  intro s
  have h := hMgf (-s)
  have heq : (fun x => Real.exp (s * (-X x))) =
      fun x => Real.exp ((-s) * X x) := by
    funext x
    congr 1
    ring
  constructor
  · rw [heq]
    exact h.1
  · calc
      (∫ x, Real.exp (s * (-X x)) ∂μ) =
          ∫ x, Real.exp ((-s) * X x) ∂μ := by rw [heq]
      _ ≤ Real.exp (Q * (-s) ^ 2) := h.2
      _ = Real.exp (Q * s ^ 2) := by
        congr 1
        ring

/-- Chernoff optimization with a finite MGF cutoff. -/
private theorem measureReal_gt_le_cutoff_rate
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (X : α → ℝ) (t V Λ : ℝ) (ht : 0 < t) (hV : 0 < V) (hΛ : 0 < Λ)
    (hMgf : ∀ s : ℝ, |s| ≤ Λ →
      Integrable (fun x => Real.exp (s * X x)) μ ∧
        (∫ x, Real.exp (s * X x) ∂μ) ≤ Real.exp (V * s ^ 2)) :
    μ.real {x | X x > t} ≤
      Real.exp (-(min (t ^ 2 / (4 * V)) (Λ * t / 2))) := by
  let lam := min (t / (2 * V)) Λ
  have hlam : 0 < lam := by
    dsimp [lam]
    exact lt_min (div_pos ht (by positivity)) hΛ
  have hlamΛ : lam ≤ Λ := min_le_right _ _
  have hlam_abs : |lam| ≤ Λ := by simpa [abs_of_pos hlam] using hlamΛ
  have hmgf := hMgf lam hlam_abs
  have hmark := measureReal_gt_le_exp_of_mgf μ X t lam (V * lam ^ 2) hlam hmgf.1 hmgf.2
  have hopt : -lam * t + V * lam ^ 2 ≤
      -(min (t ^ 2 / (4 * V)) (Λ * t / 2)) := by
    by_cases hcase : t / (2 * V) ≤ Λ
    · have hlameq : lam = t / (2 * V) := by simp [lam, hcase]
      have hthreshold : t ^ 2 / (4 * V) ≤ Λ * t / 2 := by
        have hdiv := (div_le_iff₀ (by positivity : 0 < 2 * V)).1 hcase
        have hmul := mul_le_mul_of_nonneg_left hdiv ht.le
        rw [div_le_div_iff₀ (by positivity : 0 < 4 * V)
          (by norm_num : (0 : ℝ) < 2)]
        nlinarith
      rw [hlameq, min_eq_left hthreshold]
      have hcalc : -(t / (2 * V)) * t + V * (t / (2 * V)) ^ 2 =
          -(t ^ 2 / (4 * V)) := by
        field_simp
        ring
      linarith
    · have hcut : Λ ≤ t / (2 * V) := le_of_lt (lt_of_not_ge hcase)
      have hlameq : lam = Λ := by
        dsimp [lam]
        exact min_eq_right hcut
      have hcutmul : Λ * (2 * V) ≤ t :=
        (le_div_iff₀ (by positivity : 0 < 2 * V)).1 hcut
      have hthreshold : Λ * t / 2 ≤ t ^ 2 / (4 * V) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2)
          (by positivity : (0 : ℝ) < 4 * V)]
        have hmul' := mul_le_mul_of_nonneg_right hcutmul (by positivity : 0 ≤ 2 * t)
        nlinarith
      rw [hlameq, min_eq_right hthreshold]
      have hmul : V * Λ ≤ t / 2 := by nlinarith [hcutmul]
      nlinarith
  exact hmark.trans (Real.exp_le_exp.mpr hopt)

/-- At zero variance, the endpoint cutoff MGF bound is stronger than the
zero-denominator branch of the frozen rate. No a.e.-constancy premise is
needed: `lemma:quadratic` supplies the MGF at the endpoint. -/
private theorem measureReal_gt_le_zero_variance_rate
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (X : α → ℝ) (t Λ : ℝ) (ht : 0 < t) (hΛ : 0 < Λ)
    (hMgf : ∀ s : ℝ, |s| ≤ Λ →
      Integrable (fun x => Real.exp (s * X x)) μ ∧
        (∫ x, Real.exp (s * X x) ∂μ) ≤ 1) :
    μ.real {x | X x > t} ≤ Real.exp (-(Λ * t / 2)) := by
  have hpoint := hMgf Λ (by simp [abs_of_pos hΛ])
  have hmark := measureReal_gt_le_exp_of_mgf μ X t Λ 0 hΛ hpoint.1
    (by simpa using hpoint.2)
  calc
    μ.real {x | X x > t} ≤ Real.exp (-Λ * t + 0) := hmark
    _ ≤ Real.exp (-(Λ * t / 2)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_pos hΛ ht]

/-- An all-real Gaussian MGF gives the sharp Gaussian tail, including the
zero-scale convention. -/
private theorem measureReal_gt_le_gaussian_rate
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (X : α → ℝ) (t Q : ℝ) (ht : 0 < t) (hQ : 0 ≤ Q)
    (hMgf : ∀ s : ℝ,
      Integrable (fun x => Real.exp (s * X x)) μ ∧
        (∫ x, Real.exp (s * X x) ∂μ) ≤ Real.exp (Q * s ^ 2)) :
    μ.real {x | X x > t} ≤ if Q = 0 then 0 else Real.exp (-(t ^ 2 / (4 * Q))) := by
  by_cases hQzero : Q = 0
  · subst Q
    have hzero : μ.real {x | X x > t} = 0 := by
      by_contra hne
      have hp : 0 < μ.real {x | X x > t} :=
        lt_of_le_of_ne measureReal_nonneg (Ne.symm hne)
      have hp1 : μ.real {x | X x > t} ≤ 1 := measureReal_le_one
      let lam := (1 - Real.log (μ.real {x | X x > t})) / t
      have hlog : Real.log (μ.real {x | X x > t}) ≤ 0 :=
        Real.log_nonpos hp.le hp1
      have hlam : 0 < lam := by
        dsimp [lam]
        exact div_pos (by linarith [hlog]) ht
      have hmgf := hMgf lam
      have hmark := measureReal_gt_le_exp_of_mgf μ X t lam 0 hlam hmgf.1
        (by simpa using hmgf.2)
      have hexp : Real.exp (-lam * t) =
          μ.real {x | X x > t} * Real.exp (-1) := by
        rw [show -lam * t = Real.log (μ.real {x | X x > t}) - 1 by
          dsimp [lam]
          field_simp [ne_of_gt ht]
          ring]
        rw [show Real.log (μ.real {x | X x > t}) - 1 =
          Real.log (μ.real {x | X x > t}) + (-1) by ring, Real.exp_add,
          Real.exp_log hp]
      have hexp_lt : μ.real {x | X x > t} * Real.exp (-1) <
          μ.real {x | X x > t} := by
        calc
          μ.real {x | X x > t} * Real.exp (-1) =
              Real.exp (-1) * μ.real {x | X x > t} := by ring
          _ < μ.real {x | X x > t} :=
            mul_lt_of_lt_one_left hp (Real.exp_lt_one_iff.mpr (by norm_num))
      simp only [add_zero] at hmark
      rw [hexp] at hmark
      linarith
    simpa using hzero.le
  · have hQpos : 0 < Q := lt_of_le_of_ne hQ (Ne.symm hQzero)
    let lam := t / (2 * Q)
    have hlam : 0 < lam := div_pos ht (by positivity)
    have hmgf := hMgf lam
    have hmark := measureReal_gt_le_exp_of_mgf μ X t lam (Q * lam ^ 2) hlam hmgf.1 hmgf.2
    have hcalc : -lam * t + Q * lam ^ 2 = -(t ^ 2 / (4 * Q)) := by
      dsimp [lam]
      field_simp
      ring
    rw [if_neg hQzero]
    rw [hcalc] at hmark
    exact hmark

/-- Conditional two-sided Chernoff estimate for the frozen `thetaRate`.

The Gaussian MGF premise is used exactly when `b=0`; otherwise the cutoff MGF
premise is used. Both are supplied by the separate source node
`lemma:quadratic`. The output bounds both strict tails, including all frozen
zero-scale conventions.
-/
theorem chernoff_thetaRate_of_quadraticMGF
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (F : α → ℝ) (C M₂ : ℝ) (hC : 0 < C) (hM₂ : 0 ≤ M₂)
    (r : ℕ) (hr : 1 ≤ r) (t : ℝ) (ht : 0 < t)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hmgf_gaussian : b = 0 → ∀ s : ℝ,
      Integrable (fun x => Real.exp (s * (F x - ∫ y, F y ∂μ))) μ ∧
        (∫ x, Real.exp (s * (F x - ∫ y, F y ∂μ)) ∂μ) ≤
          Real.exp ((C * a ^ 2 / 2) * s ^ 2))
    (hmgf_cutoff : 0 < b → ∀ s : ℝ, |s| ≤ 1 / (4 * C * b) →
      Integrable (fun x => Real.exp (s * (F x - ∫ y, F y ∂μ))) μ ∧
        (∫ x, Real.exp (s * (F x - ∫ y, F y ∂μ)) ∂μ) ≤
          Real.exp ((2 * C * (a ^ 2 + 2 * b ^ 2 * (r : ℝ) * M₂)) * s ^ 2)) :
    let θ := thetaRate C M₂ hC hM₂ r hr t ht a b ha hb
    μ.real {x | F x - ∫ y, F y ∂μ > t} ≤ θ ∧
      μ.real {x | ∫ y, F y ∂μ - F x > t} ≤ θ := by
  dsimp
  let X : α → ℝ := fun x => F x - ∫ y, F y ∂μ
  by_cases hb0 : b = 0
  · have hmgf := hmgf_gaussian hb0
    let Q := C * a ^ 2 / 2
    have hQ : 0 ≤ Q := by positivity
    have hXneg := neg_all_mgf μ X Q hmgf
    have hu := measureReal_gt_le_gaussian_rate μ X t Q ht hQ hmgf
    have hl := measureReal_gt_le_gaussian_rate μ (-X) t Q ht hQ hXneg
    have ha_eq : a ^ 2 + 2 * b ^ 2 * (r : ℝ) * M₂ = a ^ 2 := by simp [hb0]
    have hset : {x | (-X) x > t} = {x | ∫ y, F y ∂μ - F x > t} := by
      ext x
      simp only [Set.mem_ofPred_eq]
      dsimp [X]
      constructor <;> intro hx <;> nlinarith
    rw [hset] at hl
    by_cases ha0 : a = 0
    · have hθ : thetaRate C M₂ hC hM₂ r hr t ht a b ha hb = 0 := by
        simp [thetaRate, ha0, hb0]
      constructor
      · rw [hθ]
        simpa [Q, ha0] using hu
      · rw [hθ]
        simpa [Q, ha0] using hl
    · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have hθ : thetaRate C M₂ hC hM₂ r hr t ht a b ha hb =
          Real.exp (-(t ^ 2 / (8 * C * a ^ 2))) := by
        simp [thetaRate, hb0, ha0]
      have hstrong : Real.exp (-(t ^ 2 / (4 * Q))) ≤
          Real.exp (-(t ^ 2 / (8 * C * a ^ 2))) := by
        apply Real.exp_le_exp.mpr
        dsimp [Q]
        have hden : 0 < C * a ^ 2 := by positivity
        field_simp [ne_of_gt hden]
        nlinarith [sq_nonneg t]
      have hu' : μ.real {x | X x > t} ≤ Real.exp (-(t ^ 2 / (4 * Q))) := by
        simpa [ne_of_gt (show 0 < Q by dsimp [Q]; positivity)] using hu
      have hl' : μ.real {x | ∫ y, F y ∂μ - F x > t} ≤
          Real.exp (-(t ^ 2 / (4 * Q))) := by
        simpa [ne_of_gt (show 0 < Q by dsimp [Q]; positivity)] using hl
      constructor
      · calc
          μ.real {x | X x > t} ≤ Real.exp (-(t ^ 2 / (4 * Q))) := hu'
          _ ≤ thetaRate C M₂ hC hM₂ r hr t ht a b ha hb := by rw [hθ]; exact hstrong
      · calc
          μ.real {x | ∫ y, F y ∂μ - F x > t} ≤
              Real.exp (-(t ^ 2 / (4 * Q))) := hl'
          _ ≤ thetaRate C M₂ hC hM₂ r hr t ht a b ha hb := by rw [hθ]; exact hstrong
  · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    have hmgf := hmgf_cutoff hbpos
    let S := a ^ 2 + 2 * b ^ 2 * (r : ℝ) * M₂
    let V := 2 * C * S
    let Λ := 1 / (4 * C * b)
    have hS : 0 ≤ S := by dsimp [S]; positivity
    have hΛ : 0 < Λ := by dsimp [Λ]; positivity
    have hXneg := neg_cutoff_mgf μ X V Λ hmgf
    have huθ : μ.real {x | X x > t} ≤ thetaRate C M₂ hC hM₂ r hr t ht a b ha hb := by
      by_cases hS0 : S = 0
      · have hrate : thetaRate C M₂ hC hM₂ r hr t ht a b ha hb =
            Real.exp (-(Λ * t / 2)) := by
          calc
            thetaRate C M₂ hC hM₂ r hr t ht a b ha hb =
                Real.exp (-(t / (8 * C * b))) := by
              simp [thetaRate, S, hS0, hb0]
            _ = Real.exp (-(Λ * t / 2)) := by
              congr 1
              dsimp [Λ]
              field_simp [ne_of_gt hC, ne_of_gt hbpos]
              ring
        have hbound := measureReal_gt_le_zero_variance_rate μ X t Λ ht hΛ
          (by
            intro s hs
            have h := hmgf s hs
            simpa [V, S, hS0] using h)
        simpa [hrate] using hbound
      · have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hS0)
        have hVpos : 0 < V := by dsimp [V]; positivity
        have hrate : thetaRate C M₂ hC hM₂ r hr t ht a b ha hb =
            Real.exp (-(min (t ^ 2 / (4 * V)) (Λ * t / 2))) := by
          calc
            thetaRate C M₂ hC hM₂ r hr t ht a b ha hb =
                Real.exp (-(min (t ^ 2 / (8 * C * S)) (t / (8 * C * b)))) := by
              simp [thetaRate, S, hS0, hb0]
            _ = Real.exp (-(min (t ^ 2 / (4 * V)) (Λ * t / 2))) := by
              apply congrArg Real.exp
              apply congrArg Neg.neg
              congr 1
              · dsimp [V]
                field_simp [ne_of_gt hC, ne_of_gt hSpos]
                ring
              · dsimp [Λ]
                field_simp [ne_of_gt hC, ne_of_gt hbpos]
                ring
        have hbound := measureReal_gt_le_cutoff_rate μ X t V Λ ht hVpos hΛ
          (by
            intro s hs
            have h := hmgf s hs
            simpa [V, S] using h)
        simpa [hrate] using hbound
    have hlθ : μ.real {x | ∫ y, F y ∂μ - F x > t} ≤
        thetaRate C M₂ hC hM₂ r hr t ht a b ha hb := by
      have hset : {x | (-X) x > t} = {x | ∫ y, F y ∂μ - F x > t} := by
        ext x
        simp only [Set.mem_ofPred_eq]
        dsimp [X]
        constructor <;> intro hx <;> nlinarith
      rw [← hset]
      by_cases hS0 : S = 0
      · have hbound := measureReal_gt_le_zero_variance_rate μ (-X) t Λ ht hΛ
          (by
            intro s hs
            have h := hXneg s hs
            simpa [V, S, hS0] using h)
        have hrate : thetaRate C M₂ hC hM₂ r hr t ht a b ha hb =
            Real.exp (-(Λ * t / 2)) := by
          calc
            thetaRate C M₂ hC hM₂ r hr t ht a b ha hb =
                Real.exp (-(t / (8 * C * b))) := by
              simp [thetaRate, S, hS0, hb0]
            _ = Real.exp (-(Λ * t / 2)) := by
              congr 1
              dsimp [Λ]
              field_simp [ne_of_gt hC, ne_of_gt hbpos]
              ring
        simpa [hrate] using hbound
      · have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hS0)
        have hVpos : 0 < V := by dsimp [V]; positivity
        have hbound := measureReal_gt_le_cutoff_rate μ (-X) t V Λ ht hVpos hΛ
          (by
            intro s hs
            have h := hXneg s hs
            simpa [V, S] using h)
        have hrate : thetaRate C M₂ hC hM₂ r hr t ht a b ha hb =
            Real.exp (-(min (t ^ 2 / (4 * V)) (Λ * t / 2))) := by
          calc
            thetaRate C M₂ hC hM₂ r hr t ht a b ha hb =
                Real.exp (-(min (t ^ 2 / (8 * C * S)) (t / (8 * C * b)))) := by
              simp [thetaRate, S, hS0, hb0]
            _ = Real.exp (-(min (t ^ 2 / (4 * V)) (Λ * t / 2))) := by
              apply congrArg Real.exp
              apply congrArg Neg.neg
              congr 1
              · dsimp [V]
                field_simp [ne_of_gt hC, ne_of_gt hSpos]
                ring
              · dsimp [Λ]
                field_simp [ne_of_gt hC, ne_of_gt hbpos]
                ring
        simpa [hrate] using hbound
    exact ⟨huθ, hlθ⟩

end LOOConcentration
