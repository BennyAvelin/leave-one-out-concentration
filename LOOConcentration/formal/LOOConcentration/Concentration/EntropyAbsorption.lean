import LOOConcentration.Concentration.EntropyVariational
import Mathlib.Tactic

/-!
# Absorption of tilted entropy

This module proves the scalar absorption step from the finite tilted-entropy,
tilted-norm, and ordinary norm-MGF bounds. The latter estimates remain explicit
provider inputs.
-/

set_option autoImplicit false

open MeasureTheory

namespace LOOConcentration

noncomputable section

private theorem div_le_four_thirds_of_three_fourths {x d : ℝ}
    (hx : 0 ≤ x) (hd : 3 / 4 ≤ d) (hdpos : 0 < d) :
    x / d ≤ (4 / 3) * x := by
  rw [div_le_iff₀ hdpos]
  have hxmul : x * (3 / 4) ≤ x * d :=
    mul_le_mul_of_nonneg_left hd hx
  calc
    x = (4 / 3) * (x * (3 / 4)) := by ring
    _ ≤ (4 / 3) * (x * d) :=
      mul_le_mul_of_nonneg_left hxmul (by norm_num)
    _ = (4 / 3) * x * d := by ring

/-- Numeric absorption from the two tilted-entropy inequalities and a finite
norm-MGF estimate. -/
theorem quadratic_entropy_absorption_of_predecessor_bounds
    {C b a M2 lam s H Qtilt logZnorm : ℝ} (r : ℕ)
    (hC : 0 < C) (hb : 0 < b) (_ha : 0 ≤ a) (hM2 : 0 ≤ M2)
    (hlam : 0 < |lam|) (hcut : |lam| ≤ 1 / (4 * C * b))
    (hs : s = 2 * C * lam ^ 2 * b ^ 2)
    (hEntropy : H ≤ C * lam ^ 2 * (a ^ 2 + b ^ 2 * Qtilt))
    (hTiltNorm : s * Qtilt ≤ H + logZnorm)
    (hNormMGF : logZnorm ≤
      (s * (r : ℝ) * M2) / (1 - 2 * C * s)) :
    H ≤ 2 * C * lam ^ 2 * (a ^ 2 + 2 * b ^ 2 * (r : ℝ) * M2) := by
  have hlamne : lam ≠ 0 := abs_pos.mp hlam
  have hlamSqPos : 0 < lam ^ 2 := sq_pos_of_ne_zero hlamne
  have hspos : 0 < s := by
    rw [hs]
    exact mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hC)
      hlamSqPos) (sq_pos_of_pos hb)
  have hCutScaled : |lam| * (4 * C * b) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 4 * C * b)).mp hcut
  let x : ℝ := 4 * C * b * |lam|
  have hxnonneg : 0 ≤ x := by
    dsimp [x]
    positivity
  have hxle : x ≤ 1 := by
    dsimp [x]
    calc
      4 * C * b * |lam| = |lam| * (4 * C * b) := mul_comm _ _
      _ ≤ 1 := hCutScaled
  have hxsq : x ^ 2 ≤ 1 := by
    calc
      x ^ 2 = x * x := by rw [pow_two]
      _ ≤ 1 * 1 := mul_le_mul hxle hxle hxnonneg (by norm_num)
      _ = 1 := one_mul 1
  have hxsqEq : x ^ 2 = 16 * C ^ 2 * lam ^ 2 * b ^ 2 := by
    dsimp [x]
    calc
      (4 * C * b * |lam|) ^ 2 =
          (4 * C * b) ^ 2 * |lam| ^ 2 := by rw [mul_pow]
      _ = 16 * C ^ 2 * lam ^ 2 * b ^ 2 := by rw [sq_abs]; ring
  have hFourth : 4 * C ^ 2 * lam ^ 2 * b ^ 2 ≤ (1 / 4 : ℝ) := by
    calc
      4 * C ^ 2 * lam ^ 2 * b ^ 2 =
          (1 / 4 : ℝ) * (16 * C ^ 2 * lam ^ 2 * b ^ 2) := by ring
      _ = (1 / 4 : ℝ) * x ^ 2 := by rw [← hxsqEq]
      _ ≤ (1 / 4 : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hxsq (by norm_num)
      _ = 1 / 4 := by norm_num
  have hCsEq : 2 * C * s = 4 * C ^ 2 * lam ^ 2 * b ^ 2 := by
    rw [hs]
    ring
  have hCsUpper : 2 * C * s ≤ (1 / 4 : ℝ) := by
    calc
      2 * C * s = 4 * C ^ 2 * lam ^ 2 * b ^ 2 := hCsEq
      _ ≤ 1 / 4 := hFourth
  have hCsLtOne : 2 * C * s < 1 := by linarith
  have hsMulLtOne : s * (2 * C) < 1 := by
    calc
      s * (2 * C) = 2 * C * s := by ring
      _ < 1 := hCsLtOne
  have hsLt : s < 1 / (2 * C) :=
    (lt_div_iff₀ (by positivity : 0 < 2 * C)).2 hsMulLtOne
  have hdenLower : (3 / 4 : ℝ) ≤ 1 - 2 * C * s := by
    linarith [hCsUpper]
  have hsMul : s * (2 * C) < 1 :=
    (lt_div_iff₀ (by positivity : 0 < 2 * C)).mp hsLt
  have hdenPos : 0 < 1 - 2 * C * s := by
    have hden : 2 * C * s < 1 := by
      calc
        2 * C * s = s * (2 * C) := by ring
        _ < 1 := hsMul
    exact sub_pos.mpr hden
  have hNumeratorNonneg : 0 ≤ s * (r : ℝ) * M2 := by
    positivity
  have hMGFRelaxed :
      (s * (r : ℝ) * M2) / (1 - 2 * C * s) ≤
        (4 / 3) * (s * (r : ℝ) * M2) :=
    div_le_four_thirds_of_three_fourths hNumeratorNonneg hdenLower hdenPos
  have hMGFBound : logZnorm ≤ (4 / 3) * (s * (r : ℝ) * M2) :=
    hNormMGF.trans hMGFRelaxed
  have hEntropyTwice :
      2 * H ≤ 2 * C * lam ^ 2 * a ^ 2 + s * Qtilt := by
    calc
      2 * H ≤ 2 * (C * lam ^ 2 * (a ^ 2 + b ^ 2 * Qtilt)) :=
        mul_le_mul_of_nonneg_left hEntropy (by norm_num)
      _ = 2 * C * lam ^ 2 * a ^ 2 + s * Qtilt := by
        rw [hs]
        ring
  have hAbsorbed : H ≤ 2 * C * lam ^ 2 * a ^ 2 + logZnorm := by
    linarith [hEntropyTwice, hTiltNorm]
  have hCoefficient :
      (4 / 3) * (s * (r : ℝ) * M2) ≤
        4 * C * lam ^ 2 * b ^ 2 * (r : ℝ) * M2 := by
    rw [hs]
    have hProduct : 0 ≤ C * lam ^ 2 * b ^ 2 * (r : ℝ) * M2 := by
      positivity
    calc
      (4 / 3) * (2 * C * lam ^ 2 * b ^ 2 * (r : ℝ) * M2) =
          (8 / 3) * (C * lam ^ 2 * b ^ 2 * (r : ℝ) * M2) := by ring
      _ ≤ 4 * (C * lam ^ 2 * b ^ 2 * (r : ℝ) * M2) :=
        mul_le_mul_of_nonneg_right (by norm_num) hProduct
      _ = 4 * C * lam ^ 2 * b ^ 2 * (r : ℝ) * M2 := by ring
  calc
    H ≤ 2 * C * lam ^ 2 * a ^ 2 + logZnorm := hAbsorbed
    _ ≤ 2 * C * lam ^ 2 * a ^ 2 +
        (4 / 3) * (s * (r : ℝ) * M2) :=
      add_le_add le_rfl hMGFBound
    _ ≤ 2 * C * lam ^ 2 * a ^ 2 +
        4 * C * lam ^ 2 * b ^ 2 * (r : ℝ) * M2 :=
      add_le_add le_rfl hCoefficient
    _ = 2 * C * lam ^ 2 *
        (a ^ 2 + 2 * b ^ 2 * (r : ℝ) * M2) := by ring

/-- Dataset specialization combining the wave-2 finite tilted-norm inequality
with the scalar absorption step. The entropy-LSI and norm-MGF estimates are
still provider inputs; finite integrability is explicit at this application.
-/
theorem datasetNormSq_entropy_absorption
    {k m n : ℕ} {μ : Measure (Dataset (Observation k m) n)}
    [IsProbabilityMeasure μ] (F : Dataset (Observation k m) n → ℝ)
    (hFmeas : Measurable F) {B C b a M2 lam s : ℝ} (r : ℕ)
    (hB : 0 ≤ B) (hF : ∀ D, |F D| ≤ B)
    (hC : 0 < C) (hb : 0 < b) (_ha : 0 ≤ a) (hM2 : 0 ≤ M2)
    (hlam : 0 < |lam|) (hcut : |lam| ≤ 1 / (4 * C * b))
    (hs : s = 2 * C * lam ^ 2 * b ^ 2)
    (hNormExp : Integrable
      (fun D => Real.exp (s * datasetNormSq D)) μ)
    (hTiltMoment : Integrable
      (fun D => tiltDensity μ F lam D * datasetNormSq D) μ)
    (hEntropy : tiltEntropy μ F lam ≤
      C * lam ^ 2 *
        (a ^ 2 + b ^ 2 *
          (∫ D, tiltDensity μ F lam D * datasetNormSq D ∂μ)))
    (hNormMGF : Real.log
        (∫ D, Real.exp (s * datasetNormSq D) ∂μ) ≤
          (s * (r : ℝ) * M2) / (1 - 2 * C * s)) :
    tiltEntropy μ F lam ≤
      2 * C * lam ^ 2 * (a ^ 2 + 2 * b ^ 2 * (r : ℝ) * M2) := by
  have hlamne : lam ≠ 0 := abs_pos.mp hlam
  have hlamSqPos : 0 < lam ^ 2 := sq_pos_of_ne_zero hlamne
  have hspos : 0 < s := by
    rw [hs]
    exact mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hC)
      hlamSqPos) (sq_pos_of_pos hb)
  have hTiltNorm := datasetNormSq_tilt_variational_inequality
    (μ := μ) (F := F) hFmeas (B := B) (t := lam) (s := s)
    hB hF hspos hNormExp hTiltMoment
  exact quadratic_entropy_absorption_of_predecessor_bounds
    (r := r) hC hb _ha hM2 hlam hcut hs hEntropy hTiltNorm hNormMGF

end
end LOOConcentration
