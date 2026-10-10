import LOOConcentrationRevision.Probability.RestrictedCenteredSquareExponential
import LOOConcentrationRevision.Probability.SquareExponentialToSubgaussian

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory

/-- The actual square-exponential package produces the whole centered MGF on
exactly the same normalized restriction. Its raw package has a separate producer. -/
theorem normalizedRestriction_centered_hasSubgaussianMGF_of_square_bound
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (K : Set α) (hq : 0 < μ.real K) (X : α → ℝ) (hX : Integrable X μ)
    (a : ℝ) (ha : 0 < a)
    (hExp : Integrable (fun x => Real.exp ((X x)^2/a)) μ)
    (hBound : (∫ x, Real.exp ((X x)^2/a) ∂μ) ≤ 2) :
    let ν := normalizedRestriction μ K
    ProbabilityTheory.HasSubgaussianMGF (fun x => X x - ∫ y, X y ∂ν)
      (Real.toNNReal (512*a*Real.log (Real.exp 1/μ.real K))) ν := by
  let ν := normalizedRestriction μ K
  let : IsProbabilityMeasure ν := normalizedRestriction_isProbability μ K hq
  let ℓ := Real.log (Real.exp 1/μ.real K)
  have hℓ1 : 1 ≤ ℓ := by
    have hq1 : μ.real K ≤ 1 := measureReal_le_one
    have hlogq := Real.log_nonpos hq.le hq1
    dsimp [ℓ]
    rw [Real.log_div (Real.exp_pos _).ne' hq.ne', Real.log_exp]
    linarith
  have hScale : 0 < 32*a*ℓ := by positivity
  obtain ⟨hY, hMean, hCenterExp, hCenterBound⟩ :=
    normalizedRestriction_centered_square_exponential_bound μ K hq X hX a ha hExp hBound
  have hSG := square_exponential_hasSubgaussianMGF ν
    (fun x => X x - ∫ y, X y ∂ν) (32*a*ℓ) hScale hY hMean hCenterExp hCenterBound
  convert hSG using 1
  apply NNReal.eq
  change (Real.toNNReal (512*a*ℓ) : ℝ) = 16*(32*a*ℓ)
  rw [Real.coe_toNNReal _ (by positivity)]
  ring

end LOOConcentration.Revision
