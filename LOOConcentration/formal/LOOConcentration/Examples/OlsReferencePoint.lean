import LOOConcentration.Examples.OlsGoodSetErrorLipschitz
import Mathlib.Tactic

set_option autoImplicit false

namespace LOOConcentration

open MeasureTheory

/-- The literal alternating-design, zero-noise OLS reference sample. -/
def olsReferencePoint (n : ℕ) : Fin (n + 2) → ℝ × ℝ :=
  fun i => ((-1 : ℝ) ^ (i.1 + 1), 0)

private theorem ols_neg_one_pow_sq (k : ℕ) : ((-1 : ℝ) ^ k) ^ 2 = 1 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      change (((-1 : ℝ) ^ k * (-1)) ^ 2) = 1
      rw [mul_pow, ih]
      norm_num

private theorem ols_sum_alternating_pow (N : ℕ) :
    (∑ i : Fin N, (-1 : ℝ) ^ (i.1 + 1)) =
      if N % 2 = 0 then 0 else -1 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Fin.sum_univ_succ]
      have htail :
          (∑ j : Fin N, (-1 : ℝ) ^ ((Fin.succ j).1 + 1)) =
            -(∑ j : Fin N, (-1 : ℝ) ^ (j.1 + 1)) := by
        calc
          _ = ∑ j : Fin N, -((-1 : ℝ) ^ (j.1 + 1)) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [Fin.val_succ]
            rw [show j.1 + 1 + 1 = (j.1 + 1) + 1 by omega, pow_succ]
            norm_num
          _ = _ := by rw [Finset.sum_neg_distrib]
      rw [htail]
      simp only [Fin.val_zero, zero_add, pow_one]
      rw [ih]
      by_cases h : N % 2 = 0
      · have hnext : (N + 1) % 2 ≠ 0 := by omega
        simp [h, hnext]
      · have hnext : (N + 1) % 2 = 0 := by omega
        simp [h, hnext]

@[simp] theorem olsReferencePoint_noise_zero (n : ℕ) (i : Fin (n + 2)) :
    (olsReferencePoint n i).2 = 0 := rfl

theorem olsReferencePoint_covariate_sq (n : ℕ) (i : Fin (n + 2)) :
    (olsReferencePoint n i).1 ^ 2 = 1 := by
  exact ols_neg_one_pow_sq (i.1 + 1)

/-- Exact alternating sum, including the unpaired `-1` in odd dimension. -/
theorem olsReferencePoint_alternating_sum (n : ℕ) :
    (∑ i : Fin (n + 2), (olsReferencePoint n i).1) =
      if (n + 2) % 2 = 0 then 0 else -1 := by
  simpa [olsReferencePoint] using ols_sum_alternating_pow (n + 2)

/-- The mean is zero for even sample size and `-1/N` for odd sample size. -/
theorem olsReferencePoint_xbar (n : ℕ) :
    olsXBar (olsReferencePoint n) =
      if n % 2 = 0 then 0 else -1 / (n + 2 : ℝ) := by
  unfold olsXBar
  rw [olsReferencePoint_alternating_sum]
  have hmod : (n + 2) % 2 = n % 2 := by omega
  rw [hmod]
  by_cases h : n % 2 = 0 <;> simp [h, Nat.cast_add]

theorem olsReferencePoint_xbar_even (n : ℕ) (h : (n + 2) % 2 = 0) :
    olsXBar (olsReferencePoint n) = 0 := by
  have hn : n % 2 = 0 := by omega
  rw [olsReferencePoint_xbar, if_pos hn]

theorem olsReferencePoint_xbar_odd (n : ℕ) (h : (n + 2) % 2 = 1) :
    olsXBar (olsReferencePoint n) = -1 / (n + 2 : ℝ) := by
  have hn : n % 2 ≠ 0 := by omega
  rw [olsReferencePoint_xbar, if_neg hn]

theorem olsReferencePoint_norm_sq (n : ℕ) :
    olsNoiseNormSq (olsReferencePoint n) = (n + 2 : ℝ) := by
  unfold olsNoiseNormSq
  calc
    _ = ∑ _i : Fin (n + 2), (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [olsReferencePoint_covariate_sq, olsReferencePoint_noise_zero]
      norm_num
    _ = (n + 2 : ℝ) := by simp

theorem olsReferencePoint_norm (n : ℕ) :
    olsNoiseNorm (olsReferencePoint n) = Real.sqrt (n + 2 : ℝ) := by
  unfold olsNoiseNorm
  rw [olsReferencePoint_norm_sq]

private theorem olsReferencePoint_mean_identity (n : ℕ) :
    olsCenteredDesign (olsReferencePoint n) =
      (n + 2 : ℝ) - (n + 2 : ℝ) *
        (olsXBar (olsReferencePoint n)) ^ 2 := by
  let c : ℝ := olsXBar (olsReferencePoint n)
  have hsumSq :
      (∑ i : Fin (n + 2), (olsReferencePoint n i).1 ^ 2) = (n + 2 : ℝ) := by
    calc
      _ = ∑ _i : Fin (n + 2), (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact olsReferencePoint_covariate_sq n i
      _ = (n + 2 : ℝ) := by simp
  have hsum :
      (∑ i : Fin (n + 2), (olsReferencePoint n i).1) = (n + 2 : ℝ) * c := by
    dsimp [c]
    unfold olsXBar
    push_cast
    have hN : (n + 2 : ℝ) ≠ 0 := by positivity
    field_simp [hN]
  have hcross :
      (∑ i : Fin (n + 2), 2 * (olsReferencePoint n i).1 * c) =
        2 * c * ∑ i : Fin (n + 2), (olsReferencePoint n i).1 := by
    calc
      _ = ∑ i : Fin (n + 2), (2 * c) * (olsReferencePoint n i).1 := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by rw [Finset.mul_sum]
  have hconst :
      (∑ _i : Fin (n + 2), c ^ 2) = (n + 2 : ℝ) * c ^ 2 := by
    simp
  unfold olsCenteredDesign
  calc
    _ = ∑ i : Fin (n + 2),
        ((olsReferencePoint n i).1 ^ 2 -
          2 * (olsReferencePoint n i).1 * c + c ^ 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [c]
      ring
    _ = (∑ i : Fin (n + 2), (olsReferencePoint n i).1 ^ 2) -
        (∑ i : Fin (n + 2), 2 * (olsReferencePoint n i).1 * c) +
        (∑ _i : Fin (n + 2), c ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = (n + 2 : ℝ) - 2 * c *
        (∑ i : Fin (n + 2), (olsReferencePoint n i).1) +
        (n + 2 : ℝ) * c ^ 2 := by rw [hsumSq, hcross, hconst]
    _ = (n + 2 : ℝ) - (n + 2 : ℝ) * c ^ 2 := by
      rw [hsum]
      ring

theorem olsReferencePoint_centeredDesign_eq (n : ℕ) :
    olsCenteredDesign (olsReferencePoint n) =
      (n + 2 : ℝ) - (n + 2 : ℝ) *
        (olsXBar (olsReferencePoint n)) ^ 2 :=
  olsReferencePoint_mean_identity n

private theorem olsReferencePoint_xbar_sq_le (n : ℕ) :
    (olsXBar (olsReferencePoint n)) ^ 2 ≤ 1 / (n + 2 : ℝ) := by
  rw [olsReferencePoint_xbar]
  by_cases h : n % 2 = 0
  · simp [h]
    positivity
  · simp [h]
    have hN : 0 < (n + 2 : ℝ) := by positivity
    have hN1 : 1 ≤ (n + 2 : ℝ) := by
      exact_mod_cast (show 1 ≤ n + 2 by omega)
    have hfracDiv : (1 : ℝ) / (n + 2 : ℝ) ≤ 1 :=
      (div_le_iff₀ hN).2 (by linarith)
    have hfrac : (n + 2 : ℝ)⁻¹ ≤ 1 := by
      simpa only [one_div] using hfracDiv
    have hfrac_nonneg : 0 ≤ (n + 2 : ℝ)⁻¹ := inv_nonneg.mpr (le_of_lt hN)
    have hsq : ((n + 2 : ℝ)⁻¹) ^ 2 ≤ (n + 2 : ℝ)⁻¹ := by
      calc
        _ = (n + 2 : ℝ)⁻¹ * (n + 2 : ℝ)⁻¹ := by ring
        _ ≤ 1 * (n + 2 : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right hfrac hfrac_nonneg
        _ = _ := by ring
    calc
      (-1 / (n + 2 : ℝ)) ^ 2 = ((n + 2 : ℝ)⁻¹) ^ 2 := by
        ring
      _ ≤ (n + 2 : ℝ)⁻¹ := hsq

theorem olsReferencePoint_mem_olsGoodSet {n : ℕ} (hn : 192 ≤ n + 2) :
    olsReferencePoint n ∈ olsGoodSet n := by
  have hN192 : (192 : ℝ) ≤ (n + 2 : ℝ) := by exact_mod_cast hn
  have hN64 : (1 : ℝ) ≤ (n + 2 : ℝ) / 64 := by linarith
  have hbarSq := olsReferencePoint_xbar_sq_le n
  have hdrop : (n + 2 : ℝ) *
      (olsXBar (olsReferencePoint n)) ^ 2 ≤ 1 := by
    calc
      _ ≤ (n + 2 : ℝ) * (1 / (n + 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hbarSq (by positivity)
      _ = 1 := by field_simp
  have hdesign : (n + 2 : ℝ) / 2 ≤
      olsCenteredDesign (olsReferencePoint n) := by
    rw [olsReferencePoint_centeredDesign_eq]
    have hlarge : (2 : ℝ) ≤ (n + 2 : ℝ) := by linarith
    calc
      (n + 2 : ℝ) / 2 ≤ (n + 2 : ℝ) - 1 := by linarith
      _ ≤ (n + 2 : ℝ) -
          (n + 2 : ℝ) * (olsXBar (olsReferencePoint n)) ^ 2 := by linarith
  have hnorm : olsNoiseNorm (olsReferencePoint n) ≤
      3 * Real.sqrt (n + 2 : ℝ) := by
    rw [olsReferencePoint_norm]
    linarith [Real.sqrt_nonneg (n + 2 : ℝ)]
  change olsNoiseNorm (olsReferencePoint n) ≤ 3 * Real.sqrt (n + 2 : ℝ) ∧
    (n + 2 : ℝ) / 2 ≤ olsCenteredDesign (olsReferencePoint n) ∧
    ∀ i : Fin (n + 2),
      (olsReferencePoint n i).1 ^ 2 ≤ (n + 2 : ℝ) / 64
  refine ⟨hnorm, hdesign, ?_⟩
  intro i
  rw [olsReferencePoint_covariate_sq]
  exact hN64

private theorem olsNoisePredictor_eq_zero_of_zero_noise {N : ℕ}
    (G : Fin N → ℝ × ℝ) (hnoise : ∀ i, (G i).2 = 0) (u : ℝ) :
    olsNoisePredictor G u = 0 := by
  have hbar : olsEBar G = 0 := by
    unfold olsEBar
    simp [hnoise]
  have hcross : olsCenteredCross G = 0 := by
    unfold olsCenteredCross
    simp [hbar, hnoise]
  unfold olsNoisePredictor olsNoiseSlope
  rw [hbar, hcross]
  simp

theorem olsReferencePoint_noisePredictor_eq_zero (n : ℕ) (u : ℝ) :
    olsNoisePredictor (olsReferencePoint n) u = 0 := by
  exact olsNoisePredictor_eq_zero_of_zero_noise (olsReferencePoint n)
    (fun _ => olsReferencePoint_noise_zero n _) u

theorem olsReferencePoint_risk_section_integrable (n : ℕ) :
    Integrable (olsRiskLoss (olsReferencePoint n)) olsTestLaw :=
  olsTestRiskLoss_integrable (olsReferencePoint n)

private theorem olsTestGaussian_abs_integrable_wave10 :
    Integrable (fun x : ℝ => |x|) olsTestGaussian := by
  have hmem₂ : MemLp (id : ℝ → ℝ) (ENNReal.ofReal 2) olsTestGaussian := by
    exact ProbabilityTheory.memLp_id_gaussianReal' _ (by norm_num)
  have hmemAbs₂ : MemLp (fun x : ℝ => |x|) (ENNReal.ofReal 2) olsTestGaussian := by
    simpa only [Real.norm_eq_abs, id_eq] using hmem₂.norm
  exact hmemAbs₂.integrable (by norm_num)

private theorem olsTestLaw_snd_abs_integrable_wave10 :
    Integrable (fun z : ℝ × ℝ => |z.2|) olsTestLaw :=
  olsTestGaussian_abs_integrable_wave10.comp_snd olsTestGaussian

private theorem olsTestLaw_snd_abs_integral_eq_wave10 :
    (∫ z : ℝ × ℝ, |z.2| ∂olsTestLaw) =
      ∫ e : ℝ, |e| ∂olsTestGaussian := by
  rw [integral_prod _ olsTestLaw_snd_abs_integrable_wave10]
  simp

theorem olsReferencePoint_testRisk_eq_firstMoment (n : ℕ) :
    olsTestRisk (olsReferencePoint n) =
      ∫ e : ℝ, |e| ∂olsTestGaussian := by
  have hsection := olsReferencePoint_risk_section_integrable n
  calc
    olsTestRisk (olsReferencePoint n) =
        ∫ z : ℝ × ℝ, olsRiskLoss (olsReferencePoint n) z ∂olsTestLaw := rfl
    _ = ∫ z : ℝ × ℝ, |z.2| ∂olsTestLaw := by
      apply integral_congr_ae
      filter_upwards with z
      simp [olsRiskLoss, olsReferencePoint_noisePredictor_eq_zero]
    _ = ∫ e : ℝ, |e| ∂olsTestGaussian :=
      olsTestLaw_snd_abs_integral_eq_wave10

theorem olsReferencePoint_validation_eq_zero (n : ℕ) :
    olsValidationError (olsReferencePoint n) = 0 := by
  unfold olsValidationError
  have hsum :
      (∑ i : Fin (n + 2),
        |(olsReferencePoint n i).2 -
          olsNoisePredictor (deleteAt (olsReferencePoint n) i)
            (olsReferencePoint n i).1|) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hdelNoise : ∀ j : Fin (n + 1),
        (deleteAt (olsReferencePoint n) i j).2 = 0 := by
      intro j
      rfl
    have hdelPredictor := olsNoisePredictor_eq_zero_of_zero_noise
      (deleteAt (olsReferencePoint n) i) hdelNoise (olsReferencePoint n i).1
    simp [hdelPredictor]
  rw [hsum]
  simp

theorem olsReferencePoint_testError_eq_firstMoment (n : ℕ) :
    olsTestError (olsReferencePoint n) =
      ∫ e : ℝ, |e| ∂olsTestGaussian := by
  simp [olsTestError, olsReferencePoint_testRisk_eq_firstMoment,
    olsReferencePoint_validation_eq_zero]

theorem olsReferencePoint_testError_abs_le_one (n : ℕ) :
    |olsTestError (olsReferencePoint n)| ≤ 1 := by
  rw [olsReferencePoint_testError_eq_firstMoment]
  have hnonneg : 0 ≤ ∫ e : ℝ, |e| ∂olsTestGaussian :=
    integral_nonneg (fun _ => abs_nonneg _)
  calc
    |∫ e : ℝ, |e| ∂olsTestGaussian| =
        ∫ e : ℝ, |e| ∂olsTestGaussian := abs_of_nonneg hnonneg
    _ ≤ 1 := olsTestGaussian_abs_integral_le_one

#print axioms olsReferencePoint_xbar
#print axioms olsReferencePoint_xbar_even
#print axioms olsReferencePoint_xbar_odd
#print axioms olsReferencePoint_norm_sq
#print axioms olsReferencePoint_norm
#print axioms olsReferencePoint_centeredDesign_eq
#print axioms olsReferencePoint_mem_olsGoodSet
#print axioms olsReferencePoint_noisePredictor_eq_zero
#print axioms olsReferencePoint_risk_section_integrable
#print axioms olsReferencePoint_testRisk_eq_firstMoment
#print axioms olsReferencePoint_validation_eq_zero
#print axioms olsReferencePoint_testError_eq_firstMoment
#print axioms olsReferencePoint_testError_abs_le_one

end LOOConcentration
