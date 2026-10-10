import LOOConcentrationRevision.Probability.SubgaussianSquareExponential
import LOOConcentrationRevision.Probability.RestrictedCenteredMGFOfSquare

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory

/-- Every actual scalar subgaussian variable yields the quoted BNT proxy after
normalization and conditional centering. Whole measure-infimum comparison is a
separate obligation; this scalar estimate is its actual consumer ingredient. -/
theorem normalizedRestriction_centered_hasSubgaussianMGF
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (K : Set α) (hq : 0 < μ.real K) (X : α → ℝ) (c : NNReal)
    (hX : ProbabilityTheory.HasSubgaussianMGF X c μ) :
    let ν := normalizedRestriction μ K
    ProbabilityTheory.HasSubgaussianMGF (fun x => X x - ∫ y, X y ∂ν)
      (Real.toNNReal ((3*(2:ℝ)^12*Real.exp 2)*(c:ℝ)*Real.log (Real.exp 1/μ.real K))) ν := by
  let ν := normalizedRestriction μ K
  let : IsProbabilityMeasure ν := normalizedRestriction_isProbability μ K hq
  let ℓ := Real.log (Real.exp 1/μ.real K)
  have hℓ1 : 1 ≤ ℓ := by
    have hlogq := Real.log_nonpos hq.le (measureReal_le_one (μ := μ) (s := K))
    dsimp [ℓ]
    rw [Real.log_div (Real.exp_pos _).ne' hq.ne', Real.log_exp]
    linarith
  by_cases hc : c = 0
  · have hX0 : ProbabilityTheory.HasSubgaussianMGF X 0 μ := hc ▸ hX
    have hzeroν : X =ᵐ[ν] 0 :=
      Measure.ae_smul_measure (hX0.ae_eq_zero_of_hasSubgaussianMGF_zero.restrict) ((μ K)⁻¹)
    have hMean : (∫ x, X x ∂ν) = 0 := by rw [integral_congr_ae hzeroν]; simp
    have hCentered : (fun x => X x - ∫ y, X y ∂ν) =ᵐ[ν] 0 := by
      filter_upwards [hzeroν] with x hx
      simp [hMean, hx]
    have hSG := (ProbabilityTheory.HasSubgaussianMGF.fun_zero :
      ProbabilityTheory.HasSubgaussianMGF (fun _ : α => 0) 0 ν).congr hCentered.symm
    simpa only [hc, NNReal.coe_zero, mul_zero, zero_mul, Real.toNNReal_zero] using hSG
  · have hcpos : 0 < c := pos_iff_ne_zero.mpr hc
    have hcR : (0:ℝ) < c := by exact_mod_cast hcpos
    obtain ⟨hExp, hBound⟩ := subgaussian_square_exponential_bound μ X c hcpos hX
    have hSmall := normalizedRestriction_centered_hasSubgaussianMGF_of_square_bound
      μ K hq X hX.integrable (8*(c:ℝ)) (by positivity) hExp hBound
    change ProbabilityTheory.HasSubgaussianMGF
      (fun x => X x - ∫ y, X y ∂ν)
      (Real.toNNReal ((3*(2:ℝ)^12*Real.exp 2)*(c:ℝ)*ℓ)) ν
    refine ⟨hSmall.integrable_exp_mul, ?_⟩
    intro t
    have hSmallCoe : (Real.toNNReal (512*(8*(c:ℝ))*ℓ):ℝ) = 4096*(c:ℝ)*ℓ := by
      rw [Real.coe_toNNReal _ (by positivity)]
      ring
    have hLargeCoe : (Real.toNNReal ((3*(2:ℝ)^12*Real.exp 2)*(c:ℝ)*ℓ):ℝ) =
        (3*(2:ℝ)^12*Real.exp 2)*(c:ℝ)*ℓ := Real.coe_toNNReal _ (by positivity)
    have hCoefficient : (4096:ℝ) ≤ 3*(2:ℝ)^12*Real.exp 2 := by
      have h := Real.one_le_exp (show (0:ℝ) ≤ 2 by norm_num)
      rw [show 3*(2:ℝ)^12 = 12288 by norm_num]
      nlinarith
    calc
      _ ≤ Real.exp ((Real.toNNReal (512*(8*(c:ℝ))*ℓ):ℝ)*t^2/2) := hSmall.mgf_le t
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        rw [hSmallCoe, hLargeCoe]
        gcongr

end LOOConcentration.Revision
