import LOOConcentrationRevision.Concentration.SourceBoundedGradientMgf

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory

/-- The zero-growth source branch on every product size, including zero. -/
theorem source_product_centered_mgf_bounded_gradient_all_sizes
    {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℕ)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : 0 ≤ C) (hLC : logSobolevConstant μ ≤ ENNReal.ofReal C)
    (hM2 : Integrable (fun x : EuclideanSpace ℝ ι => ‖x‖ ^ 2) μ)
    (F : EuclideanSpace ℝ (Fin r × ι) → ℝ)
    (hloc : LocallyLipschitz F) (a : NNReal)
    (hgrad : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin r × ι))),
      DifferentiableAt ℝ F x ∧ ‖gradient F x‖ ≤ (a : ℝ)) (t : ℝ) :
    let ν := euclideanProductLaw (κ := Fin r) μ
    Integrable F ν ∧ Integrable (fun x => Real.exp (t * (F x - ∫ y, F y ∂ν))) ν ∧
      (∫ x, Real.exp (t * (F x - ∫ y, F y ∂ν)) ∂ν) ≤
        Real.exp ((C * (a : ℝ) ^ 2 / 2) * t ^ 2) ∧
      Real.log (∫ x, Real.exp (t * (F x - ∫ y, F y ∂ν)) ∂ν) ≤
        (C * (a : ℝ) ^ 2 / 2) * t ^ 2 := by
  cases r with
  | zero =>
    let ν := euclideanProductLaw (κ := Fin 0) μ
    let : IsProbabilityMeasure ν := euclideanProductLaw_isProbabilityMeasure μ
    have hF : F = fun _ => F 0 := funext fun x => congrArg F (Subsingleton.elim x 0)
    have hV : 0 ≤ (C * (a : ℝ) ^ 2 / 2) * t ^ 2 := by positivity
    dsimp only
    rw [hF]
    simp only [integral_const, probReal_univ, one_smul, sub_self, mul_zero,
      Real.exp_zero, Real.log_one]
    exact ⟨integrable_const _, integrable_const _,
      by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hV, hV⟩
  | succ r => exact source_product_centered_mgf_bounded_gradient r μ C hC hLC hM2 F hloc a hgrad t

/-- The positive-growth source branch on every product size, including zero. -/
theorem source_product_centered_mgf_positive_growth_all_sizes
    {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℕ)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : 0 ≤ C) (hLC : logSobolevConstant μ ≤ ENNReal.ofReal C)
    (hM2 : Integrable (fun x : EuclideanSpace ℝ ι => ‖x‖ ^ 2) μ)
    (F : EuclideanSpace ℝ (Fin r × ι) → ℝ)
    (hloc : LocallyLipschitz F) (a b : NNReal) (hb : 0 < (b : ℝ))
    (hgrad : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin r × ι))),
      DifferentiableAt ℝ F x ∧ ‖gradient F x‖ ≤ (a : ℝ) + (b : ℝ) * ‖x‖)
    (t : ℝ) (hcut : |t| ≤ 1 / (4 * C * (b : ℝ))) :
    let ν := euclideanProductLaw (κ := Fin r) μ
    let V := (2 * C * ((a : ℝ) ^ 2 + 2 * (b : ℝ) ^ 2 *
      ((r : ℕ) : ℝ) * (∫ x, ‖x‖ ^ 2 ∂μ))) * t ^ 2
    Integrable F ν ∧ Integrable (fun x => Real.exp (t * (F x - ∫ y, F y ∂ν))) ν ∧
      (∫ x, Real.exp (t * (F x - ∫ y, F y ∂ν)) ∂ν) ≤ Real.exp V ∧
        Real.log (∫ x, Real.exp (t * (F x - ∫ y, F y ∂ν)) ∂ν) ≤ V := by
  cases r with
  | zero =>
    let ν := euclideanProductLaw (κ := Fin 0) μ
    let : IsProbabilityMeasure ν := euclideanProductLaw_isProbabilityMeasure μ
    have hF : F = fun _ => F 0 := funext fun x => congrArg F (Subsingleton.elim x 0)
    have hV : 0 ≤ (2 * C * (a : ℝ) ^ 2) * t ^ 2 := by positivity
    dsimp only
    rw [hF]
    simp only [integral_const, probReal_univ, one_smul, sub_self, mul_zero,
      Real.exp_zero, Real.log_one, Nat.cast_zero, zero_mul, add_zero]
    exact ⟨integrable_const _, integrable_const _,
      by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hV, hV⟩
  | succ r => exact source_product_centered_mgf_positive_growth_nonneg_constant r μ C hC hLC hM2 F hloc a b hb hgrad t hcut

end LOOConcentration.Revision
