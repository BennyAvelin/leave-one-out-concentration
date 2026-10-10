import LOOConcentrationManuscript.Internal.GaussianKernelQueryDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open ProbabilityTheory

/-- Global query sensitivity of the actual stabilized Gaussian predictor, with
its sample-normalized response magnitude and fixed source parameters. -/
theorem gaussianKernel_actualDataset_query_lipschitz_bound
    (h δ : ℝ) (hh : 0 < h) (hδ : 0 < δ) (r : ℕ)
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+1)) :
    let Kh := fun t : ℝ => gaussianPDFReal 0 1 (t/h)/h
    let W := (Real.sqrt (2*Real.pi))⁻¹/h
    let W₁ := (Real.sqrt (2*Real.pi))⁻¹/h^2
    let N := (r+1 : ℝ)
    let T := fun z : ℝ => (∑ i : Fin (r+1), Kh (z-(D i).1 0)*(D i).2 0)/
      ((∑ i : Fin (r+1), Kh (z-(D i).1 0))+N*δ)
    ∀ x x' : ℝ, |T x-T x'| ≤
      ((W₁/δ)*(1+W/δ)*((∑ i : Fin (r+1), |(D i).2 0|)/N))*|x-x'| := by
  intro Kh W W₁ N T
  let C := (W₁/δ)*(1+W/δ)*((∑ i : Fin (r+1), |(D i).2 0|)/N)
  have hC : 0 ≤ C := by dsimp [C,W,W₁,N]; positivity
  let Cnn : NNReal := ⟨C,hC⟩
  have hDiff : Differentiable ℝ T := fun x =>
    (gaussianKernel_actualDataset_query_hasDerivAt_and_bound h δ hh hδ r D x).1.differentiableAt
  have hBound (x : ℝ) : ‖deriv T x‖₊ ≤ Cnn := by
    obtain ⟨hDeriv,hBound⟩ := gaussianKernel_actualDataset_query_hasDerivAt_and_bound h δ hh hδ r D x
    apply (NNReal.coe_le_coe).1
    change |deriv T x| ≤ C
    rw [hDeriv.deriv]
    exact hBound
  have hLip : LipschitzWith Cnn T := lipschitzWith_of_nnnorm_deriv_le hDiff hBound
  intro x x'
  have hp := hLip.dist_le_mul x x'
  have hcc : (Cnn : ℝ) = C := NNReal.coe_mk C hC
  rw [Real.dist_eq,Real.dist_eq,hcc] at hp
  exact hp

end LOOConcentration.Manuscript.Internal
