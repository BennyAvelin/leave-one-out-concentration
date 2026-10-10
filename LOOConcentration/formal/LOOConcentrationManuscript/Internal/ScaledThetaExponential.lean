import LOOConcentrationRevision.Frozen.Definitions.ThetaRate

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open MeasureTheory

/-- Fixed positive deviations and source `a/√N,b/N` rates give a uniform
exponential rate. This numeric ingredient is for the actual kernel application. -/
theorem thetaRate_scaled_exponential_bound
    (σ M₂ a b τ : ℝ) (hσ : 0 ≤ σ) (hM₂ : 0 ≤ M₂)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hτ : 0 < τ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) (hN : 0 < N) (t : ℝ) (ht : τ ≤ t),
      LOOConcentration.Revision.thetaRate σ M₂ hσ hM₂ N hN
        t (lt_of_lt_of_le hτ ht)
        (a / Real.sqrt (N : ℝ)) (b / (N : ℝ))
        (div_nonneg ha (Real.sqrt_nonneg _)) (div_nonneg hb (by positivity)) ≤
        Real.exp (-c * (N : ℝ)) := by
  let A := a ^ 2 + 2 * b ^ 2 * M₂
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let q := τ ^ 2 / (8 * (σ + 1) * (A + 1))
  let l := τ / (8 * (σ + 1) * (b + 1))
  have hq : 0 < q := by dsimp [q]; positivity
  have hl : 0 < l := by dsimp [l]; positivity
  refine ⟨min q l, lt_min hq hl, ?_⟩
  intro N hN t ht
  have hNr : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have htpos : 0 < t := hτ.trans_le ht
  have hEnergy : (a / Real.sqrt (N : ℝ)) ^ 2 +
      2 * (b / (N : ℝ)) ^ 2 * (N : ℝ) * M₂ = A / (N : ℝ) := by
    dsimp [A]
    have hs : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hNr).ne'
    field_simp [hs, hNr.ne']
    rw [Real.sq_sqrt hNr.le]
    ring
  have hSafeQ : q * (8 * σ * A) ≤ τ ^ 2 := by
    have hden : 8 * σ * A ≤ 8 * (σ + 1) * (A + 1) := by nlinarith
    calc
      q * (8 * σ * A) ≤ q * (8 * (σ + 1) * (A + 1)) :=
        mul_le_mul_of_nonneg_left hden hq.le
      _ = τ ^ 2 := by dsimp [q]; field_simp
  have hSafeL : l * (8 * σ * b) ≤ τ := by
    have hden : 8 * σ * b ≤ 8 * (σ + 1) * (b + 1) := by nlinarith
    calc
      l * (8 * σ * b) ≤ l * (8 * (σ + 1) * (b + 1)) :=
        mul_le_mul_of_nonneg_left hden hl.le
      _ = τ := by dsimp [l]; field_simp
  unfold LOOConcentration.Revision.thetaRate
  split_ifs with hzero hE hbzero hbzero
  · exact (Real.exp_pos _).le
  · exact (Real.exp_pos _).le
  · have hbpos : 0 < b := lt_of_le_of_ne hb (by
      intro heq
      apply hbzero
      simp only [←heq,zero_div])
    have hσpos : 0 < σ := lt_of_le_of_ne hσ (Ne.symm hzero)
    apply Real.exp_le_exp.mpr
    have hL : min q l * (N : ℝ) ≤ t / (8 * σ * (b / (N : ℝ))) := by
      apply (le_div_iff₀ (by positivity)).2
      calc
        min q l * (N : ℝ) * (8 * σ * (b / (N : ℝ))) =
            min q l * (8 * σ * b) := by field_simp
        _ ≤ l * (8 * σ * b) := mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
        _ ≤ τ := hSafeL
        _ ≤ t := ht
    linarith only [hL]
  · have hσpos : 0 < σ := lt_of_le_of_ne hσ (Ne.symm hzero)
    have hEpos : 0 < A / (N : ℝ) := by
      apply lt_of_le_of_ne (div_nonneg hA hNr.le)
      exact Ne.symm (by simpa only [hEnergy] using hE)
    apply Real.exp_le_exp.mpr
    have hQ : min q l * (N : ℝ) ≤ t ^ 2 / (8 * σ * (A / (N : ℝ))) := by
      apply (le_div_iff₀ (by positivity)).2
      calc
        min q l * (N : ℝ) * (8 * σ * (A / (N : ℝ))) =
            min q l * (8 * σ * A) := by field_simp
        _ ≤ q * (8 * σ * A) := mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
        _ ≤ τ ^ 2 := hSafeQ
        _ ≤ t ^ 2 := by nlinarith
    rw [hEnergy]
    linarith only [hQ]
  · have hσpos : 0 < σ := lt_of_le_of_ne hσ (Ne.symm hzero)
    have hbpos : 0 < b := lt_of_le_of_ne hb (by
      intro heq
      apply hbzero
      simp only [←heq,zero_div])
    have hEpos : 0 < A / (N : ℝ) := by
      apply lt_of_le_of_ne (div_nonneg hA hNr.le)
      exact Ne.symm (by simpa only [hEnergy] using hE)
    have hQ : min q l * (N : ℝ) ≤ t ^ 2 / (8 * σ * (A / (N : ℝ))) := by
      apply (le_div_iff₀ (by positivity)).2
      calc
        min q l * (N : ℝ) * (8 * σ * (A / (N : ℝ))) =
            min q l * (8 * σ * A) := by field_simp
        _ ≤ q * (8 * σ * A) := mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
        _ ≤ τ ^ 2 := hSafeQ
        _ ≤ t ^ 2 := by nlinarith
    have hL : min q l * (N : ℝ) ≤ t / (8 * σ * (b / (N : ℝ))) := by
      apply (le_div_iff₀ (by positivity)).2
      calc
        min q l * (N : ℝ) * (8 * σ * (b / (N : ℝ))) =
            min q l * (8 * σ * b) := by field_simp
        _ ≤ l * (8 * σ * b) := mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
        _ ≤ τ := hSafeL
        _ ≤ t := ht
    apply Real.exp_le_exp.mpr
    rw [hEnergy]
    have hm := le_min hQ hL
    linarith only [hm]

theorem thetaRate_three_scaled_exponential_bound
    (σ M₂ C B M ε : ℝ) (hσ : 0 ≤ σ) (hM₂ : 0 ≤ M₂)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      3 * (B / (n + 2 : ℝ)) < ε ∧
      let Θ := fun (N : ℕ) (t a b : ℝ) =>
        if σ = 0 then 0 else
        if a ^ 2 + 2 * b ^ 2 * (N : ℝ) * M₂ = 0 then
          if b = 0 then 0 else Real.exp (-(t / (8 * σ * b)))
        else if b = 0 then
          Real.exp (-(t ^ 2 / (8 * σ * (a ^ 2 + 2 * b ^ 2 * (N : ℝ) * M₂))))
        else Real.exp (-(min
          (t ^ 2 / (8 * σ * (a ^ 2 + 2 * b ^ 2 * (N : ℝ) * M₂)))
          (t / (8 * σ * b))))
      Θ (n + 1) (ε / 3) (C / Real.sqrt (n + 1 : ℝ)) (C / (n + 1 : ℝ)) +
        Θ (n + 2) (ε / 3) (M / Real.sqrt (n + 2 : ℝ)) 0 +
        Θ (n + 2) (ε / 3 - B / (n + 2 : ℝ))
          (C / Real.sqrt (n + 2 : ℝ)) (C / (n + 2 : ℝ)) ≤
        3 * Real.exp (-c * (n : ℝ)) := by
  obtain ⟨c₁,hc₁,h₁⟩ := thetaRate_scaled_exponential_bound σ M₂ C C (ε / 6)
    hσ hM₂ hC hC (by positivity)
  obtain ⟨c₂,hc₂,h₂⟩ := thetaRate_scaled_exponential_bound σ M₂ M 0 (ε / 6)
    hσ hM₂ hM (by positivity) (by positivity)
  obtain ⟨n₀,hn₀⟩ := exists_nat_gt (6 * B / ε)
  refine ⟨min c₁ c₂, lt_min hc₁ hc₂, n₀, ?_⟩
  intro n hn
  have hN : 0 < (n + 2 : ℝ) := by positivity
  have hsize : 6 * B / ε < (n + 2 : ℝ) := by
    have hcast : (n₀ : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
    linarith
  have hsmall : B / (n + 2 : ℝ) < ε / 6 := by
    have hh : 6 * B < (n + 2 : ℝ) * ε := (div_lt_iff₀ hε).mp hsize
    apply (div_lt_iff₀ hN).mpr
    nlinarith
  refine ⟨by linarith, ?_⟩
  intro Θ
  have ht₁ : ε / 6 ≤ ε / 3 := by linarith
  have ht₃ : ε / 6 ≤ ε / 3 - B / (n + 2 : ℝ) := by linarith
  have ha := h₁ (n + 1) (by omega) (ε / 3) ht₁
  have hb := h₂ (n + 2) (by omega) (ε / 3) ht₁
  have hd := h₁ (n + 2) (by omega) (ε / 3 - B / (n + 2 : ℝ)) ht₃
  have hexp (k : ℕ) (d : ℝ) (hdpos : 0 ≤ d) (hnd : n ≤ k)
      (hcd : min c₁ c₂ ≤ d) :
      Real.exp (-d * (k : ℝ)) ≤ Real.exp (-min c₁ c₂ * (n : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have hnk : (n : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hnd
    have hc : min c₁ c₂ * (n : ℝ) ≤ d * (k : ℝ) :=
      (mul_le_mul_of_nonneg_right hcd (by positivity)).trans
        (mul_le_mul_of_nonneg_left hnk hdpos)
    linarith
  have he₁ := hexp (n + 1) c₁ hc₁.le (by omega) (min_le_left _ _)
  have he₂ := hexp (n + 2) c₂ hc₂.le (by omega) (min_le_right _ _)
  have he₃ := hexp (n + 2) c₁ hc₁.le (by omega) (min_le_left _ _)
  simp only [LOOConcentration.Revision.thetaRate, Nat.cast_add, Nat.cast_one,
    Nat.cast_ofNat, zero_div] at ha hb hd he₁ he₂ he₃
  have hsum := add_le_add (add_le_add (ha.trans he₁) (hb.trans he₂)) (hd.trans he₃)
  have heq : Real.exp (-min c₁ c₂ * (n : ℝ)) +
      Real.exp (-min c₁ c₂ * (n : ℝ)) + Real.exp (-min c₁ c₂ * (n : ℝ)) =
      3 * Real.exp (-min c₁ c₂ * (n : ℝ)) := by ring
  rw [heq] at hsum
  simpa only [Θ, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, if_true] using hsum

end LOOConcentration.Manuscript.Internal
