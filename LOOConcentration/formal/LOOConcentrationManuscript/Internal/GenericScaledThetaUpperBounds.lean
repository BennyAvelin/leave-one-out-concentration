import LOOConcentrationManuscript.Internal.ScaledThetaExponential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal

/-- Uniform source rate bounds suffice for exponential decay of the actual
Theta expression; coefficients need not equal their upper bounds. The constant
precedes the sample size, threshold, and actual coefficients. -/
theorem thetaRate_of_uniform_scaled_upper_bounds
    (σ M₂ A B τ : ℝ) (hσ : 0 ≤ σ) (hM₂ : 0 ≤ M₂)
    (_hA : 0 ≤ A) (hB : 0 ≤ B) (hτ : 0 < τ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) (hN : 0 < N) (t : ℝ) (ht : τ ≤ t)
      (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
      (_haBound : a ≤ A / Real.sqrt (N : ℝ)) (_hbBound : b ≤ B / (N : ℝ)),
      LOOConcentration.Revision.thetaRate σ M₂ hσ hM₂ N hN
        t (lt_of_lt_of_le hτ ht) a b ha hb ≤ Real.exp (-c * (N : ℝ)) := by
  let E₀ := A ^ 2 + 2 * B ^ 2 * M₂
  have hE₀ : 0 ≤ E₀ := by dsimp [E₀]; positivity
  let q := τ ^ 2 / (8 * (σ + 1) * (E₀ + 1))
  let l := τ / (8 * (σ + 1) * (B + 1))
  have hq : 0 < q := by dsimp [q]; positivity
  have hl : 0 < l := by dsimp [l]; positivity
  let c := min q l
  have hc : 0 < c := lt_min hq hl
  refine ⟨c, hc, ?_⟩
  intro N hN t ht a b ha hb haBound hbBound
  have hNr : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hScale : (A / Real.sqrt (N : ℝ)) ^ 2 +
      2 * (B / (N : ℝ)) ^ 2 * (N : ℝ) * M₂ = E₀ / (N : ℝ) := by
    dsimp [E₀]
    have hs : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hNr).ne'
    field_simp [hs, hNr.ne']
    rw [Real.sq_sqrt hNr.le]
    ring
  have haSq : a ^ 2 ≤ (A / Real.sqrt (N : ℝ)) ^ 2 := by
    have hp := mul_nonneg (sub_nonneg.mpr haBound)
      (add_nonneg (ha.trans haBound) ha)
    nlinarith only [hp]
  have hbSq : b ^ 2 ≤ (B / (N : ℝ)) ^ 2 := by
    have hp := mul_nonneg (sub_nonneg.mpr hbBound)
      (add_nonneg (hb.trans hbBound) hb)
    nlinarith only [hp]
  have hEnergy : a ^ 2 + 2 * b ^ 2 * (N : ℝ) * M₂ ≤ E₀ / (N : ℝ) := by
    rw [← hScale]
    exact add_le_add haSq
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbSq (by norm_num))
          hNr.le) hM₂)
  have hSafeQ : q * (8 * σ * E₀) ≤ τ ^ 2 := by
    have hden : 8 * σ * E₀ ≤ 8 * (σ + 1) * (E₀ + 1) := by nlinarith
    calc
      _ ≤ q * (8 * (σ + 1) * (E₀ + 1)) :=
        mul_le_mul_of_nonneg_left hden hq.le
      _ = τ ^ 2 := by dsimp [q]; field_simp
  have hSafeL : l * (8 * σ * B) ≤ τ := by
    have hden : 8 * σ * B ≤ 8 * (σ + 1) * (B + 1) := by nlinarith
    calc
      _ ≤ l * (8 * (σ + 1) * (B + 1)) :=
        mul_le_mul_of_nonneg_left hden hl.le
      _ = τ := by dsimp [l]; field_simp
  have hLinear : c * (N : ℝ) * (8 * σ * b) ≤ t := by
    calc
      _ ≤ c * (N : ℝ) * (8 * σ * (B / (N : ℝ))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hbBound (by positivity)) (by positivity)
      _ = c * (8 * σ * B) := by field_simp
      _ ≤ l * (8 * σ * B) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ ≤ τ := hSafeL
      _ ≤ t := ht
  have hQuadratic : c * (N : ℝ) *
      (8 * σ * (a ^ 2 + 2 * b ^ 2 * (N : ℝ) * M₂)) ≤ t ^ 2 := by
    calc
      _ ≤ c * (N : ℝ) * (8 * σ * (E₀ / (N : ℝ))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hEnergy (by positivity)) (by positivity)
      _ = c * (8 * σ * E₀) := by field_simp
      _ ≤ q * (8 * σ * E₀) :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
      _ ≤ τ ^ 2 := hSafeQ
      _ ≤ t ^ 2 := by nlinarith
  unfold LOOConcentration.Revision.thetaRate
  split_ifs with hzero hzeroE hzeroB hzeroB
  · exact (Real.exp_pos _).le
  · exact (Real.exp_pos _).le
  · have hσpos : 0 < σ := lt_of_le_of_ne hσ (Ne.symm hzero)
    have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hzeroB)
    apply Real.exp_le_exp.mpr
    have h := (le_div_iff₀ (by positivity : 0 < 8 * σ * b)).2 hLinear
    linarith only [h]
  · have hσpos : 0 < σ := lt_of_le_of_ne hσ (Ne.symm hzero)
    have hEpos : 0 < a ^ 2 + 2 * b ^ 2 * (N : ℝ) * M₂ :=
      lt_of_le_of_ne (by positivity) (Ne.symm hzeroE)
    apply Real.exp_le_exp.mpr
    have h := (le_div_iff₀ (by positivity :
      0 < 8 * σ * (a ^ 2 + 2 * b ^ 2 * (N : ℝ) * M₂))).2 hQuadratic
    linarith only [h]
  · have hσpos : 0 < σ := lt_of_le_of_ne hσ (Ne.symm hzero)
    have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hzeroB)
    have hEpos : 0 < a ^ 2 + 2 * b ^ 2 * (N : ℝ) * M₂ :=
      lt_of_le_of_ne (by positivity) (Ne.symm hzeroE)
    apply Real.exp_le_exp.mpr
    have hL := (le_div_iff₀ (by positivity : 0 < 8 * σ * b)).2 hLinear
    have hQ := (le_div_iff₀ (by positivity :
      0 < 8 * σ * (a ^ 2 + 2 * b ^ 2 * (N : ℝ) * M₂))).2 hQuadratic
    have h := le_min hQ hL
    linarith only [h]

end LOOConcentration.Manuscript.Internal
