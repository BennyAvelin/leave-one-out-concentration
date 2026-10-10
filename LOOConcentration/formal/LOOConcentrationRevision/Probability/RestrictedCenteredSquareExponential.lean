import LOOConcentrationRevision.Probability.RestrictionSquareExponential
import LOOConcentrationRevision.Probability.CenteredSquareExponential

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory

/-- The same raw variable and normalized restriction retain actual conditional
centering and a logarithmic square-exponential scale. Raw square-exponential
premises must be supplied by the actual subgaussian producer. -/
theorem normalizedRestriction_centered_square_exponential_bound
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (K : Set α) (hq : 0 < μ.real K) (X : α → ℝ) (hX : Integrable X μ)
    (a : ℝ) (ha : 0 < a)
    (hExp : Integrable (fun x => Real.exp ((X x)^2/a)) μ)
    (hBound : (∫ x, Real.exp ((X x)^2/a) ∂μ) ≤ 2) :
    let ν := normalizedRestriction μ K
    let Y := fun x => X x - ∫ y, X y ∂ν
    Integrable Y ν ∧ (∫ x, Y x ∂ν) = 0 ∧
    Integrable (fun x => Real.exp ((Y x)^2/(32*a*Real.log (Real.exp 1/μ.real K)))) ν ∧
    (∫ x, Real.exp ((Y x)^2/(32*a*Real.log (Real.exp 1/μ.real K))) ∂ν) ≤ 2 := by
  let ν := normalizedRestriction μ K
  let : IsProbabilityMeasure ν := normalizedRestriction_isProbability μ K hq
  have hK0 : μ K ≠ 0 := by
    intro hz
    have : μ.real K = 0 := by simp [Measure.real, hz]
    exact hq.ne' this
  have hXν : Integrable X ν := hX.restrict.smul_measure (ENNReal.inv_ne_top.mpr hK0)
  have hY : Integrable (fun x => X x - ∫ y, X y ∂ν) ν :=
    hXν.sub (integrable_const _)
  have hYmean : (∫ x, X x - ∫ y, X y ∂ν ∂ν) = 0 := by
    rw [integral_sub hXν (integrable_const _), integral_const]
    simp
  let ℓ := Real.log (Real.exp 1/μ.real K)
  have hℓ1 : 1 ≤ ℓ := by
    have hq1 : μ.real K ≤ 1 := measureReal_le_one
    have hlogq := Real.log_nonpos hq.le hq1
    dsimp [ℓ]
    rw [Real.log_div (Real.exp_pos _).ne' hq.ne', Real.log_exp]
    linarith
  have hScale : 0 < 2*a*ℓ := by positivity
  obtain ⟨hRawν, hBoundν⟩ := normalizedRestriction_square_exponential_bound
    μ K hq X hX.aestronglyMeasurable a ha hExp hBound
  obtain ⟨hCenter, hCenterBound⟩ := centered_square_exponential_bound
    ν X hXν (2*a*ℓ) hScale hRawν hBoundν
  have hden : 16*(2*a*ℓ) = 32*a*ℓ := by ring
  rw [hden] at hCenter hCenterBound
  exact ⟨hY, hYmean, hCenter, hCenterBound⟩

end LOOConcentration.Revision
