import LOOConcentrationRevision.Concentration.SourceZeroConstantViaTruncation
import LOOConcentrationRevision.Concentration.LipschitzHerbst
import LOOConcentrationRevision.Concentration.SourcePositiveGrowthMgf

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory

/-- The zero-growth branch retains the sharp Gaussian coefficient and all real
parameters. The actual global Lipschitz and integrability inputs are internal. -/
theorem source_product_centered_mgf_bounded_gradient
    {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℕ)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : 0 ≤ C) (hLC : logSobolevConstant μ ≤ ENNReal.ofReal C)
    (hM2 : Integrable (fun x : EuclideanSpace ℝ ι => ‖x‖ ^ 2) μ)
    (F : EuclideanSpace ℝ (Fin (r + 1) × ι) → ℝ)
    (hloc : LocallyLipschitz F) (a : NNReal)
    (hgrad : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin (r + 1) × ι))),
      DifferentiableAt ℝ F x ∧ ‖gradient F x‖ ≤ (a : ℝ)) (t : ℝ) :
    let ν := euclideanProductLaw (κ := Fin (r + 1)) μ
    Integrable F ν ∧ Integrable (fun x => Real.exp (t * (F x - ∫ y, F y ∂ν))) ν ∧
      (∫ x, Real.exp (t * (F x - ∫ y, F y ∂ν)) ∂ν) ≤
        Real.exp ((C * (a : ℝ) ^ 2 / 2) * t ^ 2) ∧
      Real.log (∫ x, Real.exp (t * (F x - ∫ y, F y ∂ν)) ∂ν) ≤
        (C * (a : ℝ) ^ 2 / 2) * t ^ 2 := by
  let ν := euclideanProductLaw (κ := Fin (r + 1)) μ
  let : IsProbabilityMeasure ν := euclideanProductLaw_isProbabilityMeasure μ
  by_cases hzero : C = 0
  · have hz : logSobolevConstant μ ≤ 0 := by simpa only [hzero, ENNReal.ofReal_zero] using hLC
    have hLCzero : logSobolevConstant μ = 0 := le_antisymm hz zero_le
    have hd := source_product_centered_mgf_zero_constant_via_truncation r μ hLCzero hM2 F t
    dsimp only at hd ⊢
    simpa only [hzero, zero_mul, zero_div, Real.exp_zero] using
      And.intro hd.1 (And.intro hd.2.1 (And.intro hd.2.2.1.le hd.2.2.2.le))
  · have hνLC : logSobolevConstant ν ≤ ENNReal.ofReal C :=
      (logSobolevConstant_euclideanProductLaw_le r μ
        (lt_of_le_of_lt hLC ENNReal.ofReal_lt_top)).trans hLC
    have hsource := source_product_segment_estimate_and_integrable
      (κ := Fin (r + 1)) μ hM2 F hloc a 0 (by simpa using hgrad)
    have hLip : LipschitzWith a F := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, NNReal.coe_zero, zero_div, zero_mul,
        add_zero, mul_comm] using hsource.1 x y
    obtain ⟨hInt, hBound⟩ := lipschitz_centered_exp_integrable_and_mgf_le
      ν C hC hνLC F a hLip hsource.2 t
    exact ⟨hsource.2, hInt, hBound,
      (Real.log_le_iff_le_exp (integral_exp_pos hInt)).2 hBound⟩

/-- The positive-growth source window also covers zero admissible C, where the
literal real-valued cutoff forces parameter zero before any division is used. -/
theorem source_product_centered_mgf_positive_growth_nonneg_constant
    {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℕ)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : 0 ≤ C) (hLC : logSobolevConstant μ ≤ ENNReal.ofReal C)
    (hM2 : Integrable (fun x : EuclideanSpace ℝ ι => ‖x‖ ^ 2) μ)
    (F : EuclideanSpace ℝ (Fin (r + 1) × ι) → ℝ)
    (hloc : LocallyLipschitz F) (a b : NNReal) (hb : 0 < (b : ℝ))
    (hgrad : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin (r + 1) × ι))),
      DifferentiableAt ℝ F x ∧ ‖gradient F x‖ ≤ (a : ℝ) + (b : ℝ) * ‖x‖)
    (t : ℝ) (hcut : |t| ≤ 1 / (4 * C * (b : ℝ))) :
    let ν := euclideanProductLaw (κ := Fin (r + 1)) μ
    let V := (2 * C * ((a : ℝ) ^ 2 + 2 * (b : ℝ) ^ 2 *
      ((r + 1 : ℕ) : ℝ) * (∫ x, ‖x‖ ^ 2 ∂μ))) * t ^ 2
    Integrable F ν ∧ Integrable (fun x => Real.exp (t * (F x - ∫ y, F y ∂ν))) ν ∧
      (∫ x, Real.exp (t * (F x - ∫ y, F y ∂ν)) ∂ν) ≤ Real.exp V ∧
        Real.log (∫ x, Real.exp (t * (F x - ∫ y, F y ∂ν)) ∂ν) ≤ V := by
  by_cases hzero : C = 0
  · have hz : logSobolevConstant μ ≤ 0 := by simpa only [hzero, ENNReal.ofReal_zero] using hLC
    have hLCzero : logSobolevConstant μ = 0 := le_antisymm hz zero_le
    have hd := source_product_centered_mgf_zero_constant_via_truncation r μ hLCzero hM2 F t
    dsimp only at hd ⊢
    simpa only [hzero, zero_mul, mul_zero, Real.exp_zero] using
      And.intro hd.1 (And.intro hd.2.1 (And.intro hd.2.2.1.le hd.2.2.2.le))
  · exact source_product_centered_mgf_positive_growth
      r μ C (lt_of_le_of_ne hC (Ne.symm hzero)) hLC hM2 F hloc a b hb hgrad t hcut

end LOOConcentration.Revision
