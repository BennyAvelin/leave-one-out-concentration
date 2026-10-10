import LOOConcentrationManuscript.Internal.PositiveQuotientDerivative
import LOOConcentrationManuscript.Internal.GaussianKernelBoundsConsumer
import LOOConcentration.Frozen.Foundations.Observation
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Algebra.BigOperators.Field

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open ProbabilityTheory

/-- Conditional calculus calculation for a general kernel at the selected feature;
the actual Gaussian consumer below supplies the analytic premises. -/
private theorem kernelFeature_coordinate_hasDerivAt
    (Kh : ℝ → ℝ) (hNonneg : ∀ t, 0 ≤ Kh t) (δ : ℝ) (hδ : 0 < δ)
    (r : ℕ) (X Y : Fin (r+1) → ℝ) (x : ℝ) (j : Fin (r+1))
    (kp : ℝ) (hkp : HasDerivAt Kh kp (x-X j)) :
    let B := (∑ i : Fin (r+1), Kh (x-X i))+(r+1 : ℝ)*δ
    let A := ∑ i : Fin (r+1), Kh (x-X i)*Y i
    HasDerivAt (fun t : ℝ =>
      (∑ i : Fin (r+1), Kh (x-Function.update X j t i)*Y i) /
        ((∑ i : Fin (r+1), Kh (x-Function.update X j t i))+(r+1 : ℝ)*δ))
      ((kp/B)*(-Y j+A/B)) (X j) := by
  classical
  intro B A
  have hB : 0 < B := add_pos_of_nonneg_of_pos
    (Finset.sum_nonneg (fun i _ => hNonneg _)) (mul_pos (by positivity) hδ)
  have hWeight (i : Fin (r+1)) : HasDerivAt
      (fun t : ℝ => Kh (x-Function.update X j t i))
      (if i=j then -kp else 0) (X j) := by
    by_cases hij : i=j
    · subst i
      have hd := hkp.comp (X j) ((hasDerivAt_const (X j) x).sub (hasDerivAt_id' (X j)))
      simpa only [Function.update_self, sub_self, zero_sub, mul_neg_one,
        if_pos rfl, ite_true, Function.comp_def] using hd
    · simpa only [Function.update_of_ne hij, if_neg hij] using
        hasDerivAt_const (X j) (Kh (x-X i))
  have hNum : HasDerivAt (fun t : ℝ =>
      ∑ i : Fin (r+1), Kh (x-Function.update X j t i)*Y i) (-kp*Y j) (X j) := by
    simpa only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] using
      HasDerivAt.fun_sum (u:=Finset.univ) (fun i _ => (hWeight i).mul_const (Y i))
  have hDen : HasDerivAt (fun t : ℝ =>
      (∑ i : Fin (r+1), Kh (x-Function.update X j t i))+(r+1 : ℝ)*δ) (-kp) (X j) := by
    simpa only [Finset.sum_ite_eq', Finset.mem_univ, if_true] using
      (HasDerivAt.fun_sum (u:=Finset.univ) (fun i _ => hWeight i)).add_const ((r+1 : ℝ)*δ)
  have hAt : Function.update X j (X j) = X := Function.update_eq_self j X
  have hDiv := positiveDenominator_quotient_hasFDerivAt _ _ _ _ (X j)
    hNum.hasFDerivAt hDen.hasFDerivAt (by simpa only [hAt] using hB)
  have hc : (B^2)⁻¹*(B*(-kp*Y j)-A*(-kp)) = (kp/B)*(-Y j+A/B) := by
    field_simp
    ring
  have hScalar := hDiv.hasDerivAt
  simp only [hAt, smul_apply, sub_apply, ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul, one_mul] at hScalar
  change HasDerivAt _ ((B^2)⁻¹*(B*(-kp*Y j)-A*(-kp))) (X j) at hScalar
  rw [hc] at hScalar
  exact hScalar

/-- The exact Gaussian predictor feature derivative on the scalar source sample.
Kernel differentiation and denominator positivity are derived from source parameters. -/
theorem gaussianKernel_feature_coordinate_hasDerivAt
    (h δ : ℝ) (hh : 0 < h) (hδ : 0 < δ) (r : ℕ)
    (X Y : Fin (r+1) → ℝ) (x : ℝ) (j : Fin (r+1)) :
    let Kh := fun t : ℝ => gaussianPDFReal 0 1 (t/h)/h
    let B := (∑ i : Fin (r+1), Kh (x-X i))+(r+1 : ℝ)*δ
    let A := ∑ i : Fin (r+1), Kh (x-X i)*Y i
    HasDerivAt (fun t : ℝ =>
      (∑ i : Fin (r+1), Kh (x-Function.update X j t i)*Y i) /
        ((∑ i : Fin (r+1), Kh (x-Function.update X j t i))+(r+1 : ℝ)*δ))
      ((deriv Kh (x-X j)/B)*(-Y j+A/B)) (X j) := by
  intro Kh B A
  obtain ⟨_hSmooth,hNonneg,_hBound,hDeriv⟩ := gaussianScaledKernel_value_and_derivative_bounds h hh
  have hD : HasDerivAt Kh (deriv Kh (x-X j)) (x-X j) :=
    (hDeriv _).1.differentiableAt.hasDerivAt
  exact kernelFeature_coordinate_hasDerivAt Kh hNonneg δ hδ r X Y x j _ hD

/-- Literal actual-dataset feature variation preserves all responses, yielding
exactly the manuscript's stabilized Gaussian feature derivative. -/
theorem gaussianKernel_actualDataset_feature_hasDerivAt
    (h δ : ℝ) (hh : 0 < h) (hδ : 0 < δ) (r : ℕ)
    (D : Fin (r+1) → LOOConcentration.Observation 1 1) (x : ℝ) (j : Fin (r+1)) :
    let Kh := fun t : ℝ => gaussianPDFReal 0 1 (t/h)/h
    let B := (∑ i : Fin (r+1), Kh (x-(D i).1 0))+(r+1 : ℝ)*δ
    let T := fun E : Fin (r+1) → LOOConcentration.Observation 1 1 =>
      (∑ i : Fin (r+1), Kh (x-(E i).1 0)*(E i).2 0) /
        ((∑ i : Fin (r+1), Kh (x-(E i).1 0))+(r+1 : ℝ)*δ)
    HasDerivAt (fun t : ℝ => T (Function.update D j ((fun _ : Fin 1 => t),(D j).2)))
      ((deriv Kh (x-(D j).1 0)/B)*(-(D j).2 0+T D)) ((D j).1 0) := by
  intro Kh B T
  have hFeature (t : ℝ) (i : Fin (r+1)) :
      (Function.update D j ((fun _ : Fin 1 => t),(D j).2) i).1 0 =
        Function.update (fun i : Fin (r+1) => (D i).1 0) j t i := by
    by_cases hij : i=j <;> simp [hij, Function.update_of_ne]
  have hResponse (t : ℝ) (i : Fin (r+1)) :
      (Function.update D j ((fun _ : Fin 1 => t),(D j).2) i).2 0 = (D i).2 0 := by
    by_cases hij : i=j <;> simp [hij, Function.update_of_ne]
  have hF : (fun t : ℝ => T (Function.update D j ((fun _ : Fin 1 => t),(D j).2))) =
      (fun t : ℝ =>
        (∑ i : Fin (r+1), Kh (x-Function.update (fun i => (D i).1 0) j t i)*(D i).2 0) /
          ((∑ i : Fin (r+1), Kh (x-Function.update (fun i => (D i).1 0) j t i))+(r+1 : ℝ)*δ)) := by
    funext t
    dsimp [T]
    simp only [hFeature,hResponse]
  rw [hF]
  exact gaussianKernel_feature_coordinate_hasDerivAt h δ hh hδ r
    (fun i => (D i).1 0) (fun i => (D i).2 0) x j

end LOOConcentration.Manuscript.Internal
