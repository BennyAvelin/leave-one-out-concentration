import LOOConcentrationRevision.Concentration.StandingValidationSourceCorollary

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory

private theorem sharp_gaussian_le_theta_zero_growth
    (C M₂ : ℝ) (hC : 0 ≤ C) (hM₂ : 0 ≤ M₂)
    (r : ℕ) (hr : 1 ≤ r) (t : ℝ) (ht : 0 < t) (a : ℝ) (ha : 0 ≤ a) :
    (if C * a ^ 2 = 0 then 0 else Real.exp (-(t ^ 2 / (2 * C * a ^ 2)))) ≤
      thetaRate C M₂ hC hM₂ r hr t ht a 0 ha le_rfl := by
  by_cases hC0 : C = 0
  · simp [hC0, thetaRate]
  have hCp : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
  by_cases ha0 : a = 0
  · simp [ha0, thetaRate, hC0]
  have ha2 : 0 < a ^ 2 := sq_pos_of_ne_zero ha0
  have hCa : C * a ^ 2 ≠ 0 := ne_of_gt (mul_pos hCp ha2)
  simp only [if_neg hCa, thetaRate, if_neg hC0, zero_pow (by norm_num : 2 ≠ 0),
    mul_zero, zero_mul, add_zero, if_neg (ne_of_gt ha2) ]
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  apply div_le_div_of_nonneg_left (sq_nonneg t) (by positivity)
  nlinarith [mul_pos hCp ha2]

/-- The literal source Theta rate for the validation component, obtained by
weakening only the internally proved sharper zero-growth Gaussian branch. -/
theorem standing_validation_theta_tails_via_source_corollary
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)
    (t : ℝ) (ht : 0 < t) :
    let ν := datasetLawOfObservation (r := n+2) μ
    let F := fun x : EuclideanSpace ℝ (DatasetCoordinate k m (n+2)) =>
      standingValidationAverage μ T L δ₁ δ₂ δ₃ c d hSt (datasetOfEuclidean x)
    let C := (observationLogSobolevConstant μ).toReal
    let M₂ := ∫ z, observationNormSq z ∂μ
    let a := c / Real.sqrt (n+2:ℝ)
    let b := d / (n+2:ℝ)
    let θ := thetaRate C M₂ ENNReal.toReal_nonneg
      (integral_nonneg_of_ae (ae_of_all _ fun z => observationNormSq_nonneg z))
      (n+2) (by omega) t ht a b
      (div_nonneg hSt.c_nonneg (Real.sqrt_nonneg _))
      (div_nonneg hSt.d_nonneg (by positivity))
    ν.real {x | F x - ∫ y, F y ∂ν > t} ≤ θ ∧
      ν.real {x | ∫ y, F y ∂ν - F x > t} ≤ θ := by
  dsimp only
  have h := standing_validation_tails_via_source_corollary
    μ T L δ₁ δ₂ δ₃ c d hSt t ht
  dsimp only at h
  let C := (observationLogSobolevConstant μ).toReal
  let M₂ := ∫ z, observationNormSq z ∂μ
  let a := c / Real.sqrt (n+2:ℝ)
  let b := d / (n+2:ℝ)
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hM₂ : 0 ≤ M₂ := integral_nonneg_of_ae
    (ae_of_all _ fun z => observationNormSq_nonneg z)
  have ha : 0 ≤ a := div_nonneg hSt.c_nonneg (Real.sqrt_nonneg _)
  have hb : 0 ≤ b := div_nonneg hSt.d_nonneg (by positivity)
  let θ := thetaRate C M₂ hC hM₂ (n+2) (by omega) t ht a b ha hb
  have hbound :
      (if b = 0 then
        (if C * a ^ 2 = 0 then 0 else Real.exp (-(t ^ 2 / (2 * C * a ^ 2))))
       else θ) ≤ θ := by
    by_cases hb0 : b = 0
    · simp only [hb0, θ]
      exact sharp_gaussian_le_theta_zero_growth C M₂ hC hM₂
        (n+2) (by omega) t ht a ha
    · simp only [if_neg hb0, le_refl]
  exact ⟨h.1.trans hbound, h.2.trans hbound⟩

end LOOConcentration.Revision
