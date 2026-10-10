import LOOConcentrationManuscript.Internal.RidgeAddOneSlopeBound
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal

/-- The actual public stabilized predictor consumes the add-one slope bound.
The intercept retains raw responses, while only covariance responses are clipped. -/
theorem ridge_actual_add_one_predictor_difference_bound (b δ : {t : ℝ // 0 < t}) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℕ)
      (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1))
      (z : LOOConcentration.Observation 1 1) (x : ℝ),
    let N : ℝ := (r + 1 : ℝ)
    let X := fun i : Fin (r + 1) => (D i).1 0
    let a := (∑ i, X i) / N
    let v := (∑ i, (X i - a) ^ 2) / N
    let Xp := fun i : Fin (r + 2) => ((Fin.snoc D z : Fin (r + 2) → LOOConcentration.Observation 1 1) i).1 0
    let ap := (∑ i, Xp i) / (N + 1)
    let d := z.1 0 - a
    let ybar := (∑ i : Fin (r+1), (D i).2 0)/N
    |(LOOConcentration.Manuscript.stabilizedLinearEstimator b δ (r+1)
        (Fin.snoc D z) (fun _ : Fin 1 => x)) 0 -
      (LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r D
        (fun _ : Fin 1 => x)) 0| ≤
      |z.2 0-ybar|/(N+1) +
      C/(N+1)*(Real.sqrt v+|d|+v+d^2)*|x-ap| +
      (b.val/(2*Real.sqrt δ.val))*|d|/(N+1) := by
  classical
  obtain ⟨C,hC,hSlope⟩ := ridge_actual_add_one_slope_bound b δ
  refine ⟨C,hC,?_⟩
  intro r D z x N X a v Xp ap d ybar
  let U := fun i : Fin (r + 1) => LOOConcentration.Manuscript.coordinateClip ⟨b.val, b.property.le⟩ ((D i).2 0)
  let c := (∑ i, U i) / N
  let s := (∑ i, (X i - a) * (U i - c)) / N
  let Up := fun i : Fin (r + 2) => LOOConcentration.Manuscript.coordinateClip ⟨b.val, b.property.le⟩ (((Fin.snoc D z : Fin (r + 2) → LOOConcentration.Observation 1 1) i).2 0)
  let cp := (∑ i, Up i) / (N + 1)
  let vp := (∑ i, (Xp i - ap) ^ 2) / (N + 1)
  let sp := (∑ i, (Xp i - ap) * (Up i - cp)) / (N + 1)
  have hN : 0 < N := by dsimp [N]; positivity
  have hP : 0 < N+1 := by linarith
  have hSlopeActual : |sp/(vp+δ.val)-s/(v+δ.val)| ≤
      C/(N+1)*(Real.sqrt v+|d|+v+d^2) := hSlope r D z
  have hBound : |s/(v+δ.val)| ≤ b.val/(2*Real.sqrt δ.val) := by
    simpa only [N,X,U,a,c,v,s,LOOConcentration.Manuscript.coordinateClip] using
      (clippedDataset_covariance_and_ridgeSlope_bound r D b.val δ.val b.property.le δ.property).2.2
  have hSumX : (∑ i : Fin (r+2), Xp i) = (∑ i : Fin (r+1), X i)+z.1 0 := by
    rw [Fin.sum_univ_castSucc]
    simp only [Xp,X,Fin.snoc_castSucc,Fin.snoc_last]
  have hA : ap-a=d/(N+1) := by
    dsimp [ap,d,a]
    rw [hSumX]
    field_simp [hN.ne',hP.ne']
    ring
  have hSumY : (∑ i : Fin (r+2), ((Fin.snoc D z : Fin (r+2) → LOOConcentration.Observation 1 1) i).2 0) =
      (∑ i : Fin (r+1), (D i).2 0)+z.2 0 := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc,Fin.snoc_last]
  have hOld : (LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r D
      (fun _ : Fin 1 => x)) 0 = ybar+s/(v+δ.val)*(x-a) := by
    dsimp [LOOConcentration.Manuscript.stabilizedLinearEstimator,N,X,U,a,c,v,s,ybar,
      LOOConcentration.Manuscript.coordinateClip]
    simp only [inv_mul_eq_div]
  have hNew : (LOOConcentration.Manuscript.stabilizedLinearEstimator b δ (r+1)
      (Fin.snoc D z) (fun _ : Fin 1 => x)) 0 =
      ((∑ i : Fin (r+1), (D i).2 0)+z.2 0)/(N+1)+sp/(vp+δ.val)*(x-ap) := by
    dsimp [LOOConcentration.Manuscript.stabilizedLinearEstimator,N,Xp,Up,ap,cp,vp,sp,
      LOOConcentration.Manuscript.coordinateClip]
    simp only [Nat.cast_add,Nat.cast_one,inv_mul_eq_div]
    rw [hSumY]
  have hDiff : (LOOConcentration.Manuscript.stabilizedLinearEstimator b δ (r+1)
      (Fin.snoc D z) (fun _ : Fin 1 => x)) 0 -
      (LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r D
      (fun _ : Fin 1 => x)) 0 =
      (z.2 0-ybar)/(N+1) +
      (sp/(vp+δ.val)-s/(v+δ.val))*(x-ap) -
      (s/(v+δ.val))*(d/(N+1)) := by
    rw [hOld,hNew]
    have hAx : a=ap-d/(N+1) := by linarith [hA]
    rw [hAx]
    dsimp [ybar]
    field_simp [hN.ne',hP.ne']
    ring
  rw [hDiff]
  calc
    _ ≤ |(z.2 0-ybar)/(N+1) + (sp/(vp+δ.val)-s/(v+δ.val))*(x-ap)| +
        |(s/(v+δ.val))*(d/(N+1))| := by
      simpa only [sub_eq_add_neg,abs_neg] using (abs_add_le
        ((z.2 0-ybar)/(N+1)+(sp/(vp+δ.val)-s/(v+δ.val))*(x-ap))
        (-((s/(v+δ.val))*(d/(N+1)))))
    _ ≤ |(z.2 0-ybar)/(N+1)| + |(sp/(vp+δ.val)-s/(v+δ.val))*(x-ap)| +
        |(s/(v+δ.val))*(d/(N+1))| :=
      add_le_add (abs_add_le _ _) (le_refl _)
    _ ≤ _ := by
      simp only [abs_div,abs_mul,abs_of_pos hP]
      apply add_le_add
      · exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hSlopeActual (abs_nonneg _))
      · simpa only [mul_div_assoc,abs_div] using
          mul_le_mul_of_nonneg_right hBound (div_nonneg (abs_nonneg d) hP.le)

end LOOConcentration.Manuscript.Internal
