import LOOConcentrationManuscript.Internal.GaussianKernelBoundsConsumer
import LOOConcentration.Frozen.Foundations.Observation
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open ProbabilityTheory

/-- The literal Gaussian predictor's ordered delete-one identity uses the
correct stabilization at both sample sizes and gives the source pointwise bound. -/
theorem gaussianKernel_actualDataset_delete_identity_and_bound
    (h δ : ℝ) (hh : 0 < h) (hδ : 0 < δ) (r : ℕ)
    (D : Fin (r+2) → LOOConcentration.Observation 1 1) (x : ℝ) (i : Fin (r+2)) :
    let Kh := fun t : ℝ => gaussianPDFReal 0 1 (t/h)/h
    let W := (Real.sqrt (2*Real.pi))⁻¹
    let w := fun j : Fin (r+2) => Kh (x-(D j).1 0)
    let A := ∑ j : Fin (r+1), w (i.succAbove j)*(D (i.succAbove j)).2 0
    let B := ∑ j : Fin (r+1), w (i.succAbove j)
    let Tfull := (∑ j : Fin (r+2), w j*(D j).2 0)/
      ((∑ j : Fin (r+2), w j)+(r+2 : ℝ)*δ)
    let Tdel := A/(B+(r+1 : ℝ)*δ)
    Tfull-Tdel = (w i*(D i).2 0-(w i+δ)*Tdel)/(B+w i+(r+2 : ℝ)*δ) ∧
      |Tfull-Tdel| ≤ ((W/h)*|(D i).2 0|+((W/h)+δ)*|Tdel|)/((r+2 : ℝ)*δ) := by
  intro Kh W w A B Tfull Tdel
  obtain ⟨_hSmooth,hNonneg,hBound,_hDeriv⟩ := gaussianScaledKernel_value_and_derivative_bounds h hh
  have hw (j : Fin (r+2)) : 0 ≤ w j := hNonneg _
  have hwW : w i ≤ W/h := (le_abs_self _).trans (hBound _)
  have hB : 0 ≤ B := Finset.sum_nonneg (fun j _ => hw (i.succAbove j))
  have hDel : 0 < B+(r+1 : ℝ)*δ := add_pos_of_nonneg_of_pos hB (mul_pos (by positivity) hδ)
  have hLower : (r+2 : ℝ)*δ ≤ B+w i+(r+2 : ℝ)*δ :=
    le_add_of_nonneg_left (add_nonneg hB (hw i))
  have hNδ : 0 < (r+2 : ℝ)*δ := mul_pos (by positivity) hδ
  have hFull : 0 < B+w i+(r+2 : ℝ)*δ := lt_of_lt_of_le hNδ hLower
  have hA : (∑ j : Fin (r+2), w j*(D j).2 0) = A+w i*(D i).2 0 := by
    simpa only [A,add_comm] using Fin.sum_univ_succAbove (fun j : Fin (r+2) => w j*(D j).2 0) i
  have hWeights : (∑ j : Fin (r+2), w j) = B+w i := by
    simpa only [B,add_comm] using Fin.sum_univ_succAbove w i
  have hIdentity : Tfull-Tdel =
      (w i*(D i).2 0-(w i+δ)*Tdel)/(B+w i+(r+2 : ℝ)*δ) := by
    dsimp [Tfull,Tdel]
    rw [hA,hWeights]
    field_simp [hDel.ne',hFull.ne']
    ring
  refine ⟨hIdentity,?_⟩
  have hNumerator : |w i*(D i).2 0-(w i+δ)*Tdel| ≤
      (W/h)*|(D i).2 0|+((W/h)+δ)*|Tdel| := by
    calc
      _ ≤ |w i*(D i).2 0|+|(w i+δ)*Tdel| := abs_sub _ _
      _ = w i*|(D i).2 0|+(w i+δ)*|Tdel| := by
        rw [abs_mul,abs_mul,abs_of_nonneg (hw i),abs_of_nonneg (add_nonneg (hw i) hδ.le)]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hwW (abs_nonneg _))
        (mul_le_mul_of_nonneg_right (add_le_add hwW (le_refl δ)) (abs_nonneg _))
  rw [hIdentity,abs_div,abs_of_pos hFull]
  calc
    _ ≤ ((W/h)*|(D i).2 0|+((W/h)+δ)*|Tdel|)/(B+w i+(r+2 : ℝ)*δ) :=
      div_le_div_of_nonneg_right hNumerator hFull.le
    _ ≤ _ := div_le_div_of_nonneg_left (by dsimp [W]; positivity) hNδ hLower

end LOOConcentration.Manuscript.Internal
