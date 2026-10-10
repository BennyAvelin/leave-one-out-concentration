import LOOConcentrationRevision.Frozen.Definitions.ThetaRate
import LOOConcentrationManuscript.Internal.IsometryLSITransportConsumer

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal

theorem thetaRate_mono_constant
    (C₁ C₂ M₂ : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hM₂ : 0 ≤ M₂)
    (hle : C₁ ≤ C₂) (r : ℕ) (hr : 1 ≤ r) (t : ℝ) (ht : 0 < t)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    LOOConcentration.Revision.thetaRate C₁ M₂ hC₁ hM₂ r hr t ht a b ha hb ≤
      LOOConcentration.Revision.thetaRate C₂ M₂ hC₂ hM₂ r hr t ht a b ha hb := by
  have htheta_nonneg (C : ℝ) (hC : 0 ≤ C) :
      0 ≤ LOOConcentration.Revision.thetaRate C M₂ hC hM₂ r hr t ht a b ha hb := by
    unfold LOOConcentration.Revision.thetaRate
    split_ifs <;> positivity
  by_cases hC₁zero : C₁ = 0
  · simpa [LOOConcentration.Revision.thetaRate, hC₁zero] using htheta_nonneg C₂ hC₂
  have hC₁pos : 0 < C₁ := lt_of_le_of_ne hC₁ (Ne.symm hC₁zero)
  have hC₂pos : 0 < C₂ := lt_of_lt_of_le hC₁pos hle
  have hC₂zero : C₂ ≠ 0 := ne_of_gt hC₂pos
  simp only [LOOConcentration.Revision.thetaRate, if_neg hC₁zero, if_neg hC₂zero]
  have hquotient_mono (x k : ℝ) (hx : 0 ≤ x) (hk : 0 < k) :
      x / (8 * C₂ * k) ≤ x / (8 * C₁ * k) := by
    have hprod : 8 * C₁ * k ≤ 8 * C₂ * k := by
      have hmul := mul_le_mul_of_nonneg_right hle hk.le
      nlinarith
    exact div_le_div_of_nonneg_left hx (by positivity) hprod
  have hexp_quotient_mono (x k : ℝ) (hx : 0 ≤ x) (hk : 0 < k) :
      Real.exp (-(x / (8 * C₁ * k))) ≤ Real.exp (-(x / (8 * C₂ * k))) := by
    apply Real.exp_le_exp.mpr
    exact neg_le_neg (hquotient_mono x k hx hk)
  have hD_nonneg : 0 ≤ a ^ 2 + 2 * b ^ 2 * (r : ℝ) * M₂ := by
    positivity
  by_cases hDzero : a ^ 2 + 2 * b ^ 2 * (r : ℝ) * M₂ = 0
  · by_cases hbzero : b = 0
    · simp only [if_pos hDzero, if_pos hbzero]
      exact le_rfl
    · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hbzero)
      simp only [if_pos hDzero, if_neg hbzero]
      exact hexp_quotient_mono t b ht.le hbpos
  · have hDpos : 0 < a ^ 2 + 2 * b ^ 2 * (r : ℝ) * M₂ :=
      lt_of_le_of_ne hD_nonneg (Ne.symm hDzero)
    by_cases hbzero : b = 0
    · simp only [if_neg hDzero, if_pos hbzero]
      exact hexp_quotient_mono (t ^ 2) (a ^ 2 + 2 * b ^ 2 * (r : ℝ) * M₂)
        (sq_nonneg t) hDpos
    · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hbzero)
      simp only [if_neg hDzero, if_neg hbzero]
      apply Real.exp_le_exp.mpr
      exact neg_le_neg (min_le_min
        (hquotient_mono (t ^ 2)
          (a ^ 2 + 2 * b ^ 2 * (r : ℝ) * M₂) (sq_nonneg t) hDpos)
        (hquotient_mono t b ht.le hbpos))

end LOOConcentration.Manuscript.Internal
