import LOOConcentrationManuscript.Internal.GaussianKernelBoundsConsumer
import LOOConcentration.Frozen.Foundations.Dataset
import LOOConcentration.Frozen.Foundations.Observation

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open ProbabilityTheory

/-- The actual predictor is bounded by the sample average absolute response,
uniformly in the query. This yields the source expectation bound after averaging. -/
theorem gaussianKernel_actualDataset_response_mean_bound
    (h δ : ℝ) (hh : 0 < h) (hδ : 0 < δ) (r : ℕ)
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+1)) (x : ℝ) :
    let Kh := fun t : ℝ => gaussianPDFReal 0 1 (t/h)/h
    let W := (Real.sqrt (2*Real.pi))⁻¹/h
    let N := (r+1 : ℝ)
    let T := (∑ i : Fin (r+1), Kh (x-(D i).1 0)*(D i).2 0)/
      ((∑ i : Fin (r+1), Kh (x-(D i).1 0))+N*δ)
    |T| ≤ (W/δ)*((∑ i : Fin (r+1), |(D i).2 0|)/N) := by
  intro Kh W N T
  obtain ⟨_hSmooth,hNonneg,hBound,_hDeriv⟩ := gaussianScaledKernel_value_and_derivative_bounds h hh
  let A := ∑ i : Fin (r+1), Kh (x-(D i).1 0)*(D i).2 0
  let B := (∑ i : Fin (r+1), Kh (x-(D i).1 0))+N*δ
  let Y := ∑ i : Fin (r+1), |(D i).2 0|
  have hN : 0 < N := by dsimp [N]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hY : 0 ≤ Y := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hND : 0 < N*δ := mul_pos hN hδ
  have hLower : N*δ ≤ B := le_add_of_nonneg_left
    (Finset.sum_nonneg (fun i _ => hNonneg (x-(D i).1 0)))
  have hB : 0 < B := lt_of_lt_of_le hND hLower
  have hA : |A| ≤ W*Y := by
    calc
      _ ≤ ∑ i : Fin (r+1), |Kh (x-(D i).1 0)*(D i).2 0| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin (r+1), W*|(D i).2 0| := Finset.sum_le_sum (fun i _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hBound _) (abs_nonneg _))
      _ = W*Y := (Finset.mul_sum _ _ _).symm
  change |A/B| ≤ _
  rw [abs_div,abs_of_pos hB]
  calc
    _ ≤ W*Y/B := div_le_div_of_nonneg_right hA hB.le
    _ ≤ W*Y/(N*δ) := div_le_div_of_nonneg_left (mul_nonneg hW hY) hND hLower
    _ = (W/δ)*(Y/N) := by field_simp

end LOOConcentration.Manuscript.Internal
