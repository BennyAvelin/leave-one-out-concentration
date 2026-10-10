import LOOConcentrationManuscript.Internal.ScaledThetaExponential

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal

/-- Numeric decay used by the literal KDE simplified-concentration consumer. -/
theorem simplifiedRate_two_scaled_exponential_bound
    (σ A ε : ℝ) (hσ : 0 ≤ σ) (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      let s := A / Real.sqrt (n + 1 : ℝ) + 2 * (A / Real.sqrt (n + 2 : ℝ))
      (if σ * s ^ 2 = 0 then 0 else Real.exp (-(ε ^ 2 / (2 * σ * s ^ 2)))) ≤
        Real.exp (-c * (n : ℝ)) := by
  let c := ε ^ 2 / (18 * (σ + 1) * (A + 1) ^ 2)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  intro n s
  have hN : 0 < (n + 1 : ℝ) := by positivity
  have hsqrt : 0 < Real.sqrt (n + 1 : ℝ) := Real.sqrt_pos.mpr hN
  have hdiv : A / Real.sqrt (n + 2 : ℝ) ≤ A / Real.sqrt (n + 1 : ℝ) :=
    div_le_div_of_nonneg_left hA hsqrt (Real.sqrt_le_sqrt (by norm_num))
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hsBound : s ≤ 3 * A / Real.sqrt (n + 1 : ℝ) := by
    have heq : 3 * A / Real.sqrt (n + 1 : ℝ) =
        3 * (A / Real.sqrt (n + 1 : ℝ)) := by ring
    rw [heq]
    dsimp [s]
    linarith
  have hSq : s ^ 2 ≤ (3 * A / Real.sqrt (n + 1 : ℝ)) ^ 2 :=
    (sq_le_sq₀ hs (by positivity)).mpr hsBound
  have hEnergy : s ^ 2 * (n + 1 : ℝ) ≤ 9 * A ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hSq hN.le
    have heq : (3 * A / Real.sqrt (n + 1 : ℝ)) ^ 2 * (n + 1 : ℝ) = 9 * A ^ 2 := by
      field_simp [hsqrt.ne']
      rw [Real.sq_sqrt hN.le]
      ring
    rwa [heq] at h
  have hEnergyN : s ^ 2 * (n : ℝ) ≤ 9 * A ^ 2 := by
    have hh : s ^ 2 * (n : ℝ) ≤ s ^ 2 * (n + 1 : ℝ) :=
      mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
    exact hh.trans hEnergy
  have hSafe : c * (18 * σ * A ^ 2) ≤ ε ^ 2 := by
    have hd : 18 * σ * A ^ 2 ≤ 18 * (σ + 1) * (A + 1) ^ 2 := by nlinarith
    calc
      c * (18 * σ * A ^ 2) ≤ c * (18 * (σ + 1) * (A + 1) ^ 2) :=
        mul_le_mul_of_nonneg_left hd hc.le
      _ = ε ^ 2 := by dsimp [c]; field_simp
  split_ifs with hz
  · exact (Real.exp_pos _).le
  · have hd : 0 < 2 * σ * s ^ 2 := by
      have hp : 0 < σ * s ^ 2 := lt_of_le_of_ne (mul_nonneg hσ (sq_nonneg _)) (Ne.symm hz)
      linarith
    apply Real.exp_le_exp.mpr
    have hnum : c * (n : ℝ) * (2 * σ * s ^ 2) ≤ ε ^ 2 := by
      calc
        c * (n : ℝ) * (2 * σ * s ^ 2) = c * (2 * σ) * (s ^ 2 * (n : ℝ)) := by ring
        _ ≤ c * (2 * σ) * (9 * A ^ 2) :=
          mul_le_mul_of_nonneg_left hEnergyN (by positivity)
        _ = c * (18 * σ * A ^ 2) := by ring
        _ ≤ ε ^ 2 := hSafe
    have hb := (le_div_iff₀ hd).mpr hnum
    linarith only [hb]

/-- Numeric decay used by the literal KDE simplified-concentration consumer. -/
theorem simplifiedRate_bandwidth_exponential_bound
    (σ M h ε : ℝ) (hσ : 0 ≤ σ) (hM : 0 ≤ M) (hh : 0 < h) (hε : 0 < ε) :
    let c := ε ^ 2 / (18 * (σ + 1) * (M + 1) ^ 2)
    0 < c ∧ ∀ n : ℕ,
      let s := M / (h ^ 2 * Real.sqrt (n + 1 : ℝ)) + 2 * (M / (h ^ 2 * Real.sqrt (n + 2 : ℝ)))
      (if σ * s ^ 2 = 0 then 0 else Real.exp (-(ε ^ 2 / (2 * σ * s ^ 2)))) ≤
        Real.exp (-c * (n + 1 : ℝ) * h ^ 4) := by
  intro c
  let A := M / h ^ 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨hc, ?_⟩
  intro n s
  have hsDef : s = A / Real.sqrt (n + 1 : ℝ) + 2 * (A / Real.sqrt (n + 2 : ℝ)) := by dsimp [s, A]; ring
  have hN : 0 < (n + 1 : ℝ) := by positivity
  have hsqrt : 0 < Real.sqrt (n + 1 : ℝ) := Real.sqrt_pos.mpr hN
  have hdiv : A / Real.sqrt (n + 2 : ℝ) ≤ A / Real.sqrt (n + 1 : ℝ) :=
    div_le_div_of_nonneg_left hA hsqrt (Real.sqrt_le_sqrt (by norm_num))
  have hs : 0 ≤ s := by rw [hsDef]; positivity
  have hsBound : s ≤ 3 * A / Real.sqrt (n + 1 : ℝ) := by
    have heq : 3 * A / Real.sqrt (n + 1 : ℝ) =
        3 * (A / Real.sqrt (n + 1 : ℝ)) := by ring
    rw [heq]
    rw [hsDef]
    linarith
  have hSq : s ^ 2 ≤ (3 * A / Real.sqrt (n + 1 : ℝ)) ^ 2 :=
    (sq_le_sq₀ hs (by positivity)).mpr hsBound
  have hEnergy : s ^ 2 * (n + 1 : ℝ) ≤ 9 * A ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hSq hN.le
    have heq : (3 * A / Real.sqrt (n + 1 : ℝ)) ^ 2 * (n + 1 : ℝ) = 9 * A ^ 2 := by
      field_simp [hsqrt.ne']
      rw [Real.sq_sqrt hN.le]
      ring
    rwa [heq] at h
  have hEnergyH : s ^ 2 * (n + 1 : ℝ) * h ^ 4 ≤ 9 * M ^ 2 := by
    have hE := mul_le_mul_of_nonneg_right hEnergy (pow_nonneg hh.le 4)
    have heq : 9 * A ^ 2 * h ^ 4 = 9 * M ^ 2 := by dsimp [A]; field_simp
    rwa [heq] at hE
  have hSafe : c * (18 * σ * M ^ 2) ≤ ε ^ 2 := by
    have hd : 18 * σ * M ^ 2 ≤ 18 * (σ + 1) * (M + 1) ^ 2 := by nlinarith
    calc
      c * (18 * σ * M ^ 2) ≤ c * (18 * (σ + 1) * (M + 1) ^ 2) :=
        mul_le_mul_of_nonneg_left hd hc.le
      _ = ε ^ 2 := by dsimp [c]; field_simp
  split_ifs with hz
  · exact (Real.exp_pos _).le
  · have hd : 0 < 2 * σ * s ^ 2 := by
      have hp : 0 < σ * s ^ 2 := lt_of_le_of_ne (mul_nonneg hσ (sq_nonneg _)) (Ne.symm hz)
      linarith
    apply Real.exp_le_exp.mpr
    have hnum : c * (n + 1 : ℝ) * h ^ 4 * (2 * σ * s ^ 2) ≤ ε ^ 2 := by
      calc
        c * (n + 1 : ℝ) * h ^ 4 * (2 * σ * s ^ 2) = c * (2 * σ) * (s ^ 2 * (n + 1 : ℝ) * h ^ 4) := by ring
        _ ≤ c * (2 * σ) * (9 * M ^ 2) :=
          mul_le_mul_of_nonneg_left hEnergyH (by positivity)
        _ = c * (18 * σ * M ^ 2) := by ring
        _ ≤ ε ^ 2 := hSafe
    have hb := (le_div_iff₀ hd).mpr hnum
    linarith only [hb]

end LOOConcentration.Manuscript.Internal
