import LOOConcentration.Frozen.Concentration.ThetaRate
import LOOConcentration.Results.StandingFacts
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Measurability and elementary bounds for the frozen quadratic rate

The proofs unfold the frozen rate without changing its zero-denominator
branches. No tail or MGF conclusion is used.
-/

set_option autoImplicit false

namespace LOOConcentration

open MeasureTheory

/-- The frozen rate is measurable in measurable nonnegative coefficient
functions. The nested measurable cases follow the exact frozen definition. -/
theorem measurable_thetaRate {α : Type*} [MeasurableSpace α]
    {a b : α → ℝ} (ha : Measurable a) (hb : Measurable b)
    (C M₂ : ℝ) (hC : 0 < C) (hM₂ : 0 ≤ M₂) (r : ℕ) (hr : 1 ≤ r)
    (t : ℝ) (ht : 0 < t)
    (ha0 : ∀ x, 0 ≤ a x) (hb0 : ∀ x, 0 ≤ b x) :
    Measurable (fun x => thetaRate C M₂ hC hM₂ r hr t ht
      (a x) (b x) (ha0 x) (hb0 x)) := by
  let S : α → ℝ := fun x => a x ^ 2 + 2 * b x ^ 2 * (r : ℝ) * M₂
  have hS : Measurable S := by fun_prop
  have hSzero : MeasurableSet {x | S x = 0} :=
    measurableSet_eq_fun hS measurable_const
  have hbzero : MeasurableSet {x | b x = 0} :=
    measurableSet_eq_fun hb measurable_const
  have hlinear : Measurable (fun x => Real.exp (-(t / (8 * C * b x)))) := by
    fun_prop
  have hgaussian : Measurable
      (fun x => Real.exp (-(t ^ 2 / (8 * C * S x)))) := by
    fun_prop
  have hgeneral : Measurable
      (fun x => Real.exp (-(min (t ^ 2 / (8 * C * S x))
        (t / (8 * C * b x))))) := by
    fun_prop
  unfold thetaRate
  change Measurable (fun x =>
    if S x = 0 then
      if b x = 0 then 0 else Real.exp (-(t / (8 * C * b x)))
    else if b x = 0 then Real.exp (-(t ^ 2 / (8 * C * S x)))
    else Real.exp (-(min (t ^ 2 / (8 * C * S x))
        (t / (8 * C * b x)))))
  exact Measurable.ite hSzero
    (Measurable.ite hbzero measurable_const hlinear)
    (Measurable.ite hbzero hgaussian hgeneral)

/-- The frozen rate is nonnegative, including the zero-scale branches. -/
theorem thetaRate_nonneg
    (C M₂ : ℝ) (hC : 0 < C) (hM₂ : 0 ≤ M₂) (r : ℕ) (hr : 1 ≤ r)
    (t : ℝ) (ht : 0 < t) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ thetaRate C M₂ hC hM₂ r hr t ht a b ha hb := by
  unfold thetaRate
  split_ifs <;> positivity

/-- The frozen rate is at most one in every zero-denominator branch. -/
theorem thetaRate_le_one
    (C M₂ : ℝ) (hC : 0 < C) (hM₂ : 0 ≤ M₂) (r : ℕ) (hr : 1 ≤ r)
    (t : ℝ) (ht : 0 < t) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    thetaRate C M₂ hC hM₂ r hr t ht a b ha hb ≤ 1 := by
  unfold thetaRate
  by_cases hS : a ^ 2 + 2 * b ^ 2 * (r : ℝ) * M₂ = 0
  · rw [if_pos hS]
    by_cases hbzero : b = 0
    · simp [hbzero]
    · rw [if_neg hbzero, Real.exp_le_one_iff]
      exact neg_nonpos.mpr
        (div_nonneg ht.le (by positivity))
  · rw [if_neg hS]
    by_cases hbzero : b = 0
    · rw [if_pos hbzero, Real.exp_le_one_iff]
      have hSnonneg : 0 ≤ a ^ 2 + 2 * b ^ 2 * (r : ℝ) * M₂ := by positivity
      have hSpos : 0 < a ^ 2 + 2 * b ^ 2 * (r : ℝ) * M₂ :=
        lt_of_le_of_ne hSnonneg (Ne.symm hS)
      exact neg_nonpos.mpr
        (div_nonneg (sq_nonneg t) (by positivity))
    · rw [if_neg hbzero, Real.exp_le_one_iff]
      have hSnonneg : 0 ≤ a ^ 2 + 2 * b ^ 2 * (r : ℝ) * M₂ := by positivity
      have hSpos : 0 < a ^ 2 + 2 * b ^ 2 * (r : ℝ) * M₂ :=
        lt_of_le_of_ne hSnonneg (Ne.symm hS)
      have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hbzero)
      exact neg_nonpos.mpr (le_min
        (div_nonneg (sq_nonneg t) (by positivity))
        (div_nonneg ht.le (by positivity)))

/-- The frozen rate takes values in the interval [0,1]. -/
theorem thetaRate_mem_Icc
    (C M₂ : ℝ) (hC : 0 < C) (hM₂ : 0 ≤ M₂) (r : ℕ) (hr : 1 ≤ r)
    (t : ℝ) (ht : 0 < t) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    thetaRate C M₂ hC hM₂ r hr t ht a b ha hb ∈ Set.Icc 0 1 :=
  ⟨thetaRate_nonneg C M₂ hC hM₂ r hr t ht a b ha hb,
    thetaRate_le_one C M₂ hC hM₂ r hr t ht a b ha hb⟩

/-- A measurable frozen rate is integrable under a finite measure. -/
theorem integrable_thetaRate_of_measurable
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {a b : α → ℝ} (ha : Measurable a) (hb : Measurable b)
    (C M₂ : ℝ) (hC : 0 < C) (hM₂ : 0 ≤ M₂) (r : ℕ) (hr : 1 ≤ r)
    (t : ℝ) (ht : 0 < t)
    (ha0 : ∀ x, 0 ≤ a x) (hb0 : ∀ x, 0 ≤ b x) :
    Integrable (fun x => thetaRate C M₂ hC hM₂ r hr t ht
      (a x) (b x) (ha0 x) (hb0 x)) μ := by
  apply Integrable.of_mem_Icc 0 1
    (measurable_thetaRate ha hb C M₂ hC hM₂ r hr t ht ha0 hb0).aemeasurable
  filter_upwards [] with x
  exact thetaRate_mem_Icc C M₂ hC hM₂ r hr t ht (a x) (b x)
    (ha0 x) (hb0 x)

/-- Under the standing assumption, the actual theta rate at the deleted
training size n + 1 is integrable. This discharges wave-4's rate-integrability
premise without a separate measurability assumption. -/
theorem standing_thetaRate_integrable {k m n : ℕ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator (k + 1) (m + 1) (r + 1))
    (L : Responses (m + 1) → Responses (m + 1) → ℝ)
    {C : ℝ} {δ₁ δ₂ : ℕ → Observation (k + 1) (m + 1) → ℝ}
    {δ₃ : ℕ → ℝ} {c d t : ℝ}
    (h : StandingAssumption (n := n) μ C T L δ₁ δ₂ δ₃ c d)
    (ht : 0 < t) :
    Integrable
      (fun z : Observation (k + 1) (m + 1) =>
        thetaRate C (∫ z, observationNormSq z ∂μ) (standing_lsi_pos h)
          (standing_moment_nonneg h) (n + 1) (by omega) t ht
          (δ₁ (n + 1) z) (δ₂ (n + 1) z)
          (standing_delta_nonneg h n z).1 (standing_delta_nonneg h n z).2) μ := by
  have hδmeas : Measurable (δ₁ (n + 1)) ∧ Measurable (δ₂ (n + 1)) := by
    rcases h.2.2.1 with ⟨_, _, _, hδ, _, _, _, _, _⟩
    exact hδ n
  exact integrable_thetaRate_of_measurable hδmeas.1 hδmeas.2
    C (∫ z, observationNormSq z ∂μ) (standing_lsi_pos h)
    (standing_moment_nonneg h) (n + 1) (by omega) t ht
    (fun z => (standing_delta_nonneg h n z).1)
    (fun z => (standing_delta_nonneg h n z).2)

/-- The frozen rate is monotone in both nonnegative rate coefficients. The
proof keeps the zero-denominator branches explicit. -/
theorem thetaRate_mono
    (C M₂ : ℝ) (hC : 0 < C) (hM₂ : 0 ≤ M₂) (r : ℕ) (hr : 1 ≤ r)
    (t : ℝ) (ht : 0 < t)
    (a a' b b' : ℝ) (ha : 0 ≤ a) (ha' : 0 ≤ a')
    (hb : 0 ≤ b) (hb' : 0 ≤ b')
    (haa' : a ≤ a') (hbb' : b ≤ b') :
    thetaRate C M₂ hC hM₂ r hr t ht a b ha hb ≤
      thetaRate C M₂ hC hM₂ r hr t ht a' b' ha' hb' := by
  let S : ℝ := a ^ 2 + 2 * b ^ 2 * (r : ℝ) * M₂
  let S' : ℝ := a' ^ 2 + 2 * b' ^ 2 * (r : ℝ) * M₂
  let θ := fun (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) =>
    thetaRate C M₂ hC hM₂ r hr t ht x y hx hy
  change θ a b ha hb ≤ θ a' b' ha' hb'
  have hSnonneg : 0 ≤ S := by dsimp [S]; positivity
  have hS'nonneg : 0 ≤ S' := by dsimp [S']; positivity
  have hSqA : a ^ 2 ≤ a' ^ 2 := by nlinarith [sq_nonneg (a' - a)]
  have hSqB : b ^ 2 ≤ b' ^ 2 := by nlinarith [sq_nonneg (b' - b)]
  have hcoef : 0 ≤ 2 * (r : ℝ) * M₂ := by positivity
  have hterm : 2 * b ^ 2 * (r : ℝ) * M₂ ≤
      2 * b' ^ 2 * (r : ℝ) * M₂ := by
    calc
      2 * b ^ 2 * (r : ℝ) * M₂ = b ^ 2 * (2 * (r : ℝ) * M₂) := by ring
      _ ≤ b' ^ 2 * (2 * (r : ℝ) * M₂) :=
        mul_le_mul_of_nonneg_right hSqB hcoef
      _ = 2 * b' ^ 2 * (r : ℝ) * M₂ := by ring
  have hSS' : S ≤ S' := by
    dsimp [S, S']
    linarith
  have hquadAnti (hSp : 0 < S) (hS'p : 0 < S') :
      t ^ 2 / (8 * C * S') ≤ t ^ 2 / (8 * C * S) := by
    have hd : 8 * C * S ≤ 8 * C * S' :=
      mul_le_mul_of_nonneg_left hSS' (by positivity)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    exact mul_le_mul_of_nonneg_left hd (sq_nonneg t)
  have hlinAnti (hbp : 0 < b) (hb'p : 0 < b') :
      t / (8 * C * b') ≤ t / (8 * C * b) := by
    have hd : 8 * C * b ≤ 8 * C * b' :=
      mul_le_mul_of_nonneg_left hbb' (by positivity)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    exact mul_le_mul_of_nonneg_left hd ht.le
  by_cases hS0 : S = 0
  · by_cases hb0 : b = 0
    · have hS0' : a ^ 2 + 2 * b ^ 2 * (r : ℝ) * M₂ = 0 := by
        simpa [S] using hS0
      have hsource : θ a b ha hb = 0 := by
        change thetaRate C M₂ hC hM₂ r hr t ht a b ha hb = 0
        unfold thetaRate
        rw [if_pos hS0', if_pos hb0]
      rw [hsource]
      exact thetaRate_nonneg C M₂ hC hM₂ r hr t ht a' b' ha' hb'
    · have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
      have hb'p : 0 < b' := lt_of_lt_of_le hbp hbb'
      have hlin := hlinAnti hbp hb'p
      have hsource : θ a b ha hb =
          Real.exp (-(t / (8 * C * b))) := by
        simp [θ, thetaRate, S, hS0, hb0]
      by_cases hS'0 : S' = 0
      · have htarget : θ a' b' ha' hb' =
            Real.exp (-(t / (8 * C * b'))) := by
          simp [θ, thetaRate, S', hS'0, ne_of_gt hb'p]
        calc
          θ a b ha hb = Real.exp (-(t / (8 * C * b))) := hsource
          _ ≤ Real.exp (-(t / (8 * C * b'))) :=
            Real.exp_le_exp.mpr (neg_le_neg hlin)
          _ = θ a' b' ha' hb' := htarget.symm
      · have hS'p : 0 < S' := lt_of_le_of_ne hS'nonneg (Ne.symm hS'0)
        have htarget : θ a' b' ha' hb' =
            Real.exp (-(min (t ^ 2 / (8 * C * S'))
              (t / (8 * C * b')))) := by
          simp [θ, thetaRate, S', hS'0, ne_of_gt hb'p]
        have hmin : min (t ^ 2 / (8 * C * S')) (t / (8 * C * b')) ≤
            t / (8 * C * b) :=
          (min_le_right _ _).trans hlin
        calc
          θ a b ha hb = Real.exp (-(t / (8 * C * b))) := hsource
          _ ≤ Real.exp (-(min (t ^ 2 / (8 * C * S'))
              (t / (8 * C * b')))) :=
            Real.exp_le_exp.mpr (neg_le_neg hmin)
          _ = θ a' b' ha' hb' := htarget.symm
  · have hSp : 0 < S := lt_of_le_of_ne hSnonneg (Ne.symm hS0)
    have hS'p : 0 < S' := lt_of_lt_of_le hSp hSS'
    have hquad := hquadAnti hSp hS'p
    by_cases hb0 : b = 0
    · have ha_ne : a ≠ 0 := by
        intro ha0
        apply hS0
        simp [S, hb0, ha0]
      have hsource : θ a b ha hb =
          Real.exp (-(t ^ 2 / (8 * C * S))) := by
        simp [θ, thetaRate, S, hb0, ha_ne]
      by_cases hb'0 : b' = 0
      · have ha'_ne : a' ≠ 0 := by
          intro ha'0
          have hS'zero : S' = 0 := by simp [S', hb'0, ha'0]
          exact (ne_of_gt hS'p) hS'zero
        have htarget : θ a' b' ha' hb' =
            Real.exp (-(t ^ 2 / (8 * C * S'))) := by
          simp [θ, thetaRate, S', hb'0, ha'_ne]
        calc
          θ a b ha hb = Real.exp (-(t ^ 2 / (8 * C * S))) := hsource
          _ ≤ Real.exp (-(t ^ 2 / (8 * C * S'))) :=
            Real.exp_le_exp.mpr (neg_le_neg hquad)
          _ = θ a' b' ha' hb' := htarget.symm
      · have hb'p : 0 < b' := lt_of_le_of_ne hb' (Ne.symm hb'0)
        have htarget : θ a' b' ha' hb' =
            Real.exp (-(min (t ^ 2 / (8 * C * S'))
              (t / (8 * C * b')))) := by
          simp [θ, thetaRate, S', ne_of_gt hS'p, hb'0]
        have hmin : min (t ^ 2 / (8 * C * S'))
            (t / (8 * C * b')) ≤ t ^ 2 / (8 * C * S) :=
          (min_le_left _ _).trans hquad
        calc
          θ a b ha hb = Real.exp (-(t ^ 2 / (8 * C * S))) := hsource
          _ ≤ Real.exp (-(min (t ^ 2 / (8 * C * S'))
              (t / (8 * C * b')))) :=
            Real.exp_le_exp.mpr (neg_le_neg hmin)
          _ = θ a' b' ha' hb' := htarget.symm
    · have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
      have hb'p : 0 < b' := lt_of_lt_of_le hbp hbb'
      have hlin := hlinAnti hbp hb'p
      have hsource : θ a b ha hb =
          Real.exp (-(min (t ^ 2 / (8 * C * S))
            (t / (8 * C * b)))) := by
        simp [θ, thetaRate, S, hS0, hb0]
      have htarget : θ a' b' ha' hb' =
          Real.exp (-(min (t ^ 2 / (8 * C * S'))
            (t / (8 * C * b')))) := by
        simp [θ, thetaRate, S', ne_of_gt hS'p, ne_of_gt hb'p]
      have hmin : min (t ^ 2 / (8 * C * S'))
          (t / (8 * C * b')) ≤
        min (t ^ 2 / (8 * C * S)) (t / (8 * C * b)) :=
        min_le_min hquad hlin
      calc
        θ a b ha hb =
            Real.exp (-(min (t ^ 2 / (8 * C * S))
              (t / (8 * C * b)))) := hsource
        _ ≤ Real.exp (-(min (t ^ 2 / (8 * C * S'))
            (t / (8 * C * b')))) :=
          Real.exp_le_exp.mpr (neg_le_neg hmin)
        _ = θ a' b' ha' hb' := htarget.symm

end LOOConcentration
