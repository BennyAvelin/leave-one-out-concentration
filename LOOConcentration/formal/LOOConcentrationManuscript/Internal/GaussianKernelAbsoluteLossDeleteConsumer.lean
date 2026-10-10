import LOOConcentrationManuscript.Internal.GaussianKernelResponseMeanBound
import LOOConcentrationManuscript.Internal.GaussianKernelDeleteIdentity

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open ProbabilityTheory

/-- A uniform pointwise delete-one bound for the actual absolute fitted loss,
in terms of the held-out response and the remaining sample's mean magnitude. -/
theorem gaussianKernel_actualDataset_absoluteLoss_delete_bound
    (h δ : ℝ) (hh : 0 < h) (hδ : 0 < δ) (r : ℕ)
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+2))
    (x y : ℝ) (i : Fin (r+2)) :
    let Kh := fun t : ℝ => gaussianPDFReal 0 1 (t/h)/h
    let W := (Real.sqrt (2*Real.pi))⁻¹/h
    let Tfull := (∑ j : Fin (r+2), Kh (x-(D j).1 0)*(D j).2 0)/
      ((∑ j : Fin (r+2), Kh (x-(D j).1 0))+(r+2 : ℝ)*δ)
    let Tdel := (∑ j : Fin (r+1), Kh (x-(D (i.succAbove j)).1 0)*(D (i.succAbove j)).2 0)/
      ((∑ j : Fin (r+1), Kh (x-(D (i.succAbove j)).1 0))+(r+1 : ℝ)*δ)
    abs (abs (Tfull-y)-abs (Tdel-y)) ≤ (W/δ)/(r+2 : ℝ)*
      (|(D i).2 0|+(1+W/δ)*
        ((∑ j : Fin (r+1), |(D (i.succAbove j)).2 0|)/(r+1 : ℝ))) := by
  intro Kh W Tfull Tdel
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hT := gaussianKernel_actualDataset_response_mean_bound h δ hh hδ r
    (fun j => D (i.succAbove j)) x
  have hDel := (gaussianKernel_actualDataset_delete_identity_and_bound h δ hh hδ r D x i).2
  have hLoss : abs (abs (Tfull-y)-abs (Tdel-y)) ≤ |Tfull-Tdel| := by
    have h := abs_abs_sub_abs_le_abs_sub (Tfull-y) (Tdel-y)
    simpa only [sub_sub_sub_cancel_right] using h
  calc
    _ ≤ |Tfull-Tdel| := hLoss
    _ ≤ (W*|(D i).2 0|+(W+δ)*|Tdel|)/((r+2 : ℝ)*δ) := hDel
    _ ≤ (W*|(D i).2 0|+(W+δ)*((W/δ)*
        ((∑ j : Fin (r+1), |(D (i.succAbove j)).2 0|)/(r+1 : ℝ))))/((r+2 : ℝ)*δ) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hT (add_nonneg hW hδ.le))
    _ = _ := by field_simp; ring

end LOOConcentration.Manuscript.Internal
