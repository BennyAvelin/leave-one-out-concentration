import LOOConcentrationManuscript.Internal.PositiveQuotientDerivative
import LOOConcentrationManuscript.Internal.GaussianKernelBoundsConsumer
import LOOConcentration.Frozen.Foundations.Observation
import LOOConcentration.Frozen.Foundations.Dataset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open ProbabilityTheory

/-- The actual Gaussian predictor's query derivative and its source finite-response bound. -/
theorem gaussianKernel_actualDataset_query_hasDerivAt_and_bound
    (h δ : ℝ) (hh : 0 < h) (hδ : 0 < δ) (r : ℕ)
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+1)) (x : ℝ) :
    let Kh := fun t : ℝ => gaussianPDFReal 0 1 (t/h)/h
    let W := (Real.sqrt (2*Real.pi))⁻¹/h
    let W₁ := (Real.sqrt (2*Real.pi))⁻¹/h^2
    let N := (r+1 : ℝ)
    let B := fun z : ℝ => (∑ i : Fin (r+1), Kh (z-(D i).1 0))+N*δ
    let T := fun z : ℝ => (∑ i : Fin (r+1), Kh (z-(D i).1 0)*(D i).2 0)/B z
    let S := ((∑ i : Fin (r+1), deriv Kh (x-(D i).1 0)*(D i).2 0)-
      T x*(∑ i : Fin (r+1), deriv Kh (x-(D i).1 0)))/B x
    HasDerivAt T S x ∧
      |S| ≤ (W₁/δ)*(1+W/δ)*((∑ i : Fin (r+1), |(D i).2 0|)/N) := by
  intro Kh W W₁ N B T S
  obtain ⟨_hSmooth,hNonneg,hBound,hDeriv⟩ := gaussianScaledKernel_value_and_derivative_bounds h hh
  have hN : 0 < N := by dsimp [N]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hW₁ : 0 ≤ W₁ := by dsimp [W₁]; positivity
  have hND : 0 < N*δ := mul_pos hN hδ
  have hLower : N*δ ≤ B x := le_add_of_nonneg_left
    (Finset.sum_nonneg (fun i _ => hNonneg (x-(D i).1 0)))
  have hB : 0 < B x := lt_of_lt_of_le hND hLower
  have hWeight (i : Fin (r+1)) :
      HasDerivAt (fun z : ℝ => Kh (z-(D i).1 0)) (deriv Kh (x-(D i).1 0)) x := by
    have hk := (hDeriv (x-(D i).1 0)).1.differentiableAt.hasDerivAt
    simpa only [Function.comp_def, mul_one] using
      hk.comp x ((hasDerivAt_id' x).sub_const ((D i).1 0))
  let A := fun z : ℝ => ∑ i : Fin (r+1), Kh (z-(D i).1 0)*(D i).2 0
  let DA := ∑ i : Fin (r+1), deriv Kh (x-(D i).1 0)*(D i).2 0
  let DB := ∑ i : Fin (r+1), deriv Kh (x-(D i).1 0)
  have hA : HasDerivAt A DA x :=
    HasDerivAt.fun_sum (u:=Finset.univ) (fun i _ => (hWeight i).mul_const ((D i).2 0))
  have hBD : HasDerivAt B DB x :=
    (HasDerivAt.fun_sum (u:=Finset.univ) (fun i _ => hWeight i)).add_const (N*δ)
  have hQ := (positiveDenominator_quotient_hasFDerivAt A B _ _ x
    hA.hasFDerivAt hBD.hasFDerivAt hB).hasDerivAt
  simp only [smul_apply,sub_apply,ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul,one_mul] at hQ
  change HasDerivAt T ((B x^2)⁻¹*(B x*DA-A x*DB)) x at hQ
  have hFormula : (B x^2)⁻¹*(B x*DA-A x*DB) = S := by
    dsimp [S,T,A,DA,DB]
    field_simp
  rw [hFormula] at hQ
  refine ⟨hQ,?_⟩
  let Y := ∑ i : Fin (r+1), |(D i).2 0|
  have hY : 0 ≤ Y := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hAx : |A x| ≤ W*Y := by
    calc
      _ ≤ ∑ i : Fin (r+1), |Kh (x-(D i).1 0)*(D i).2 0| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin (r+1), W*|(D i).2 0| := Finset.sum_le_sum (fun i _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hBound _) (abs_nonneg _))
      _ = W*Y := (Finset.mul_sum _ _ _).symm
  have hT : |T x| ≤ W*Y/(N*δ) := by
    change |A x/B x| ≤ _
    rw [abs_div,abs_of_pos hB]
    exact (div_le_div_of_nonneg_right hAx hB.le).trans
      (div_le_div_of_nonneg_left (mul_nonneg hW hY) hND hLower)
  have hDA : |DA| ≤ W₁*Y := by
    calc
      _ ≤ ∑ i : Fin (r+1), |deriv Kh (x-(D i).1 0)*(D i).2 0| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin (r+1), W₁*|(D i).2 0| := Finset.sum_le_sum (fun i _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hDeriv _).2 (abs_nonneg _))
      _ = W₁*Y := (Finset.mul_sum _ _ _).symm
  have hDB : |DB| ≤ N*W₁ := by
    calc
      _ ≤ ∑ i : Fin (r+1), |deriv Kh (x-(D i).1 0)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin (r+1), W₁ := Finset.sum_le_sum (fun i _ => (hDeriv _).2)
      _ = N*W₁ := by simp [N]
  have hNum : |DA-T x*DB| ≤ W₁*Y+(W*Y/(N*δ))*(N*W₁) :=
    (abs_sub _ _).trans (by
      rw [abs_mul]
      exact add_le_add hDA (mul_le_mul hT hDB (abs_nonneg _) (by positivity)))
  change |(DA-T x*DB)/B x| ≤ _
  rw [abs_div,abs_of_pos hB]
  calc
    _ ≤ (W₁*Y+(W*Y/(N*δ))*(N*W₁))/B x := div_le_div_of_nonneg_right hNum hB.le
    _ ≤ (W₁*Y+(W*Y/(N*δ))*(N*W₁))/(N*δ) :=
      div_le_div_of_nonneg_left (by positivity) hND hLower
    _ = (W₁/δ)*(1+W/δ)*(Y/N) := by field_simp

end LOOConcentration.Manuscript.Internal
