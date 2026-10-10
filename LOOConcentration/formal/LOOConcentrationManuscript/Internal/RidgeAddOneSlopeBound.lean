import LOOConcentrationManuscript.Internal.RidgeAddOneUpdates
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal

private theorem updated_slope_bound
    (N b δ v s d e : ℝ) (hN : 0 < N) (hb : 0 < b) (hδ : 0 < δ)
    (hv : 0 ≤ v) (hs : |s| ≤ b * Real.sqrt v) (he : |e| ≤ 2*b)
    (hβ : |s/(v+δ)| ≤ b/(2*Real.sqrt δ)) :
    let vp := N/(N+1)*v + N/(N+1)^2*d^2
    let sp := N/(N+1)*s + N/(N+1)^2*d*e
    |sp/(vp+δ)-s/(v+δ)| ≤
      ((3*b+b/(2*Real.sqrt δ))/δ)/(N+1)*(Real.sqrt v+|d|+v+d^2) := by
  intro vp sp
  let S := b/(2*Real.sqrt δ)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hP : 0 < N+1 := by linarith
  have hvp : 0 ≤ vp := by dsimp [vp]; positivity
  have hpδ : 0 < vp+δ := by linarith
  have hvδ : 0 < v+δ := by linarith
  have hq : 0 ≤ N/(N+1)^2 := by positivity
  have hq' : N/(N+1)^2 ≤ 1/(N+1) := by
    apply (div_le_iff₀ (sq_pos_of_pos hP)).2
    field_simp [hP.ne']
    linarith
  have hsp : sp-s = -s/(N+1) + (N/(N+1)^2)*(d*e) := by
    dsimp [sp]
    field_simp [hP.ne']
    ring
  have hvp' : vp-v = -v/(N+1) + (N/(N+1)^2)*d^2 := by
    dsimp [vp]
    field_simp [hP.ne']
    ring
  have hsDiff : |sp-s| ≤ (b*Real.sqrt v + 2*b*|d|)/(N+1) := by
    rw [hsp]
    calc
      _ ≤ |-s/(N+1)| + |(N/(N+1)^2)*(d*e)| := abs_add_le _ _
      _ = |s|/(N+1) + (N/(N+1)^2)*|d| *|e| := by
        rw [abs_div, abs_neg, abs_of_pos hP, abs_mul, abs_of_nonneg hq, abs_mul]
        ring
      _ ≤ (b*Real.sqrt v)/(N+1) + (1/(N+1))*|d| *(2*b) := by
        apply add_le_add
        · exact div_le_div_of_nonneg_right hs hP.le
        · exact mul_le_mul (mul_le_mul_of_nonneg_right hq' (abs_nonneg d)) he
            (abs_nonneg e) (by positivity)
      _ = _ := by ring
  have hvDiff : |vp-v| ≤ (v+d^2)/(N+1) := by
    rw [hvp']
    calc
      _ ≤ |-v/(N+1)| + |(N/(N+1)^2)*d^2| := abs_add_le _ _
      _ = v/(N+1) + (N/(N+1)^2)*d^2 := by
        rw [abs_div, abs_neg, abs_of_nonneg hv, abs_of_pos hP,
          abs_mul, abs_of_nonneg hq, abs_of_nonneg (sq_nonneg d)]
      _ ≤ v/(N+1) + (1/(N+1))*d^2 :=
        add_le_add_right (mul_le_mul_of_nonneg_right hq' (sq_nonneg d)) _
      _ = _ := by ring
  have hIdentity : sp/(vp+δ)-s/(v+δ) =
      ((sp-s)-(s/(v+δ))*(vp-v))/(vp+δ) := by
    field_simp [hpδ.ne',hvδ.ne']
    ring
  have hNum : |(sp-s)-(s/(v+δ))*(vp-v)| ≤
      (b*Real.sqrt v + 2*b*|d| + S*(v+d^2))/(N+1) := by
    calc
      _ ≤ |sp-s| + |(s/(v+δ))*(vp-v)| := by simpa only [sub_eq_add_neg, abs_neg] using (abs_add_le (sp-s) (-(s/(v+δ)*(vp-v))))
      _ ≤ (b*Real.sqrt v + 2*b*|d|)/(N+1) + S*((v+d^2)/(N+1)) := by
        apply add_le_add hsDiff
        rw [abs_mul]
        exact mul_le_mul hβ hvDiff (abs_nonneg _) hS
      _ = _ := by ring
  have hDom : b*Real.sqrt v + 2*b*|d| + S*(v+d^2) ≤
      (3*b+S)*(Real.sqrt v+|d|+v+d^2) := by
    nlinarith [mul_nonneg hS (Real.sqrt_nonneg v), mul_nonneg hb.le (abs_nonneg d),
      mul_nonneg hb.le hv, mul_nonneg hb.le (sq_nonneg d),
      mul_nonneg hS (abs_nonneg d),mul_nonneg hb.le (Real.sqrt_nonneg v)]
  rw [hIdentity,abs_div,abs_of_pos hpδ]
  calc
    _ ≤ ((b*Real.sqrt v + 2*b*|d| + S*(v+d^2))/(N+1))/δ :=
      div_le_div₀ (by positivity) hNum hδ (by linarith)
    _ ≤ (((3*b+S)*(Real.sqrt v+|d|+v+d^2))/(N+1))/δ := by
      apply div_le_div_of_nonneg_right _ hδ.le
      exact div_le_div_of_nonneg_right hDom hP.le
    _ = _ := by dsimp [S]; ring

/-- The actual clipped-data add-one slopes satisfy the manuscript's shared
sample-size-independent bound. Every numerical bound is discharged internally. -/
theorem ridge_actual_add_one_slope_bound (b δ : {t : ℝ // 0 < t}) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℕ)
      (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1))
      (z : LOOConcentration.Observation 1 1),
    let N : ℝ := (r + 1 : ℝ)
    let X := fun i : Fin (r + 1) => (D i).1 0
    let U := fun i : Fin (r + 1) => LOOConcentration.Manuscript.coordinateClip ⟨b.val, b.property.le⟩ ((D i).2 0)
    let a := (∑ i, X i) / N
    let c := (∑ i, U i) / N
    let v := (∑ i, (X i - a) ^ 2) / N
    let s := (∑ i, (X i - a) * (U i - c)) / N
    let Xp := fun i : Fin (r + 2) => ((Fin.snoc D z : Fin (r + 2) → LOOConcentration.Observation 1 1) i).1 0
    let Up := fun i : Fin (r + 2) => LOOConcentration.Manuscript.coordinateClip ⟨b.val, b.property.le⟩ (((Fin.snoc D z : Fin (r + 2) → LOOConcentration.Observation 1 1) i).2 0)
    let ap := (∑ i, Xp i) / (N + 1)
    let cp := (∑ i, Up i) / (N + 1)
    let vp := (∑ i, (Xp i - ap) ^ 2) / (N + 1)
    let sp := (∑ i, (Xp i - ap) * (Up i - cp)) / (N + 1)
    let d := z.1 0 - a
    |sp/(vp+δ.val)-s/(v+δ.val)| ≤
      C/(N+1)*(Real.sqrt v+|d|+v+d^2) := by
  have hb : 0 < b.val := b.property
  have hδ : 0 < δ.val := δ.property
  let C := (3*b.val+b.val/(2*Real.sqrt δ.val))/δ.val
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro r D z N X U a c v s Xp Up ap cp vp sp d
  let e := LOOConcentration.Manuscript.coordinateClip ⟨b.val, b.property.le⟩ (z.2 0) - c
  have hN : 0 < N := by dsimp [N]; positivity
  have hU : ∀ i, |U i| ≤ b.val := by
    intro i
    exact (scalarClipping_lipschitz_and_bound b.val b.property.le).2 ((D i).2 0)
  have hc : |c| ≤ b.val := by
    dsimp [c]
    rw [abs_div, abs_of_pos hN]
    apply (div_le_iff₀ hN).2
    calc
      |∑ i, U i| ≤ ∑ i, |U i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin (r+1), b.val := Finset.sum_le_sum (fun i _ => hU i)
      _ = b.val*N := by simp [N,mul_comm]
  have he : |e| ≤ 2*b.val := by
    dsimp [e]
    calc
      _ ≤ |LOOConcentration.Manuscript.coordinateClip ⟨b.val,b.property.le⟩ (z.2 0)|+|c| := by simpa only [sub_eq_add_neg, abs_neg] using (abs_add_le (LOOConcentration.Manuscript.coordinateClip ⟨b.val,b.property.le⟩ (z.2 0)) (-c))
      _ ≤ b.val+b.val := add_le_add
        ((scalarClipping_lipschitz_and_bound b.val b.property.le).2 (z.2 0)) hc
      _ = _ := by ring
  have hBounds : 0 ≤ v ∧ |s| ≤ b.val*Real.sqrt v ∧
      |s/(v+δ.val)| ≤ b.val/(2*Real.sqrt δ.val) := by
    simpa only [N,X,U,a,c,v,s,LOOConcentration.Manuscript.coordinateClip] using
      clippedDataset_covariance_and_ridgeSlope_bound r D b.val δ.val b.property.le δ.property
  have hUpdates : sp=N/(N+1)*s+N/(N+1)^2*d*e ∧
      vp=N/(N+1)*v+N/(N+1)^2*d^2 := by
    simpa only [N,X,U,a,c,v,s,Xp,Up,ap,cp,vp,sp,d,e] using
      ridge_actual_add_one_empirical_updates r D z b
  rw [hUpdates.1,hUpdates.2]
  exact updated_slope_bound N b.val δ.val v s d e hN b.property δ.property
    hBounds.1 hBounds.2.1 he hBounds.2.2

end LOOConcentration.Manuscript.Internal
