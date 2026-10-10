import LOOConcentrationRevision.FunctionalInequalities.ZeroLsiPointmassViaTruncation
import LOOConcentrationRevision.Probability.EuclideanProductSecondMoment
import LOOConcentrationRevision.FunctionalInequalities.BoundedProductLSI
import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory
open scoped ENNReal
/-- At zero constant, the actual admitted pair forces the actual product law
 to be a point mass, so the centered original exponential equals one. -/
theorem source_product_centered_mgf_zero_constant_via_truncation
    {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℕ)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hLC : logSobolevConstant μ = 0)
    (hM2 : Integrable (fun x : EuclideanSpace ℝ ι => ‖x‖ ^ 2) μ)
    (F : EuclideanSpace ℝ (Fin (r + 1) × ι) → ℝ) (t : ℝ) :
    let ν := euclideanProductLaw (κ := Fin (r + 1)) μ
    Integrable F ν ∧ Integrable (fun x => Real.exp (t * (F x - ∫ y, F y ∂ν))) ν ∧
      (∫ x, Real.exp (t * (F x - ∫ y, F y ∂ν)) ∂ν) = 1 ∧
      Real.log (∫ x, Real.exp (t * (F x - ∫ y, F y ∂ν)) ∂ν) = 0 := by
  let ν := euclideanProductLaw (κ := Fin (r + 1)) μ
  let : IsProbabilityMeasure ν := euclideanProductLaw_isProbabilityMeasure μ
  have hνLC : logSobolevConstant ν = 0 := by
    have hp := logSobolevConstant_euclideanProductLaw_le r μ
      (by rw [hLC]; exact bot_lt_top)
    have hz : logSobolevConstant ν ≤ 0 := by simpa only [ν, hLC] using hp
    exact le_antisymm hz zero_le
  have hνM2 := integrable_euclideanProductLaw_norm_sq (κ := Fin (r + 1)) μ hM2
  obtain ⟨x, hx⟩ := exists_dirac_of_logSobolevConstant_eq_zero_via_truncation ν hνM2 hνLC
  dsimp only
  have hx' : euclideanProductLaw (κ := Fin (r + 1)) μ = Measure.dirac x := hx
  rw [hx']
  simp only [integral_dirac, sub_self, mul_zero, Real.exp_zero, Real.log_one, and_true]
  exact ⟨integrable_dirac (by simp), integrable_dirac (by simp)⟩
end LOOConcentration.Revision
