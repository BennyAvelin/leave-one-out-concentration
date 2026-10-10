import LOOConcentrationManuscript.Internal.EuclideanClipping
import LOOConcentration.Frozen.Foundations.Dataset
import LOOConcentration.Frozen.Foundations.Observation
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal

/-- A bounded response vector gives the exact source covariance and ridge-slope bounds.
The concrete clipped-response consumer derives the response bound internally. -/
theorem boundedResponse_covariance_and_ridgeSlope_bound
    (N : ℕ) (hN : 0 < N) (X U : Fin N → ℝ)
    (b : ℝ) (hb : 0 ≤ b) (hU : ∀ i, |U i| ≤ b)
    (δ : ℝ) (hδ : 0 < δ) :
    let a := (∑ i : Fin N, X i) / (N : ℝ)
    let c := (∑ i : Fin N, U i) / (N : ℝ)
    let v := (∑ i : Fin N, (X i - a)^2) / (N : ℝ)
    let s := (∑ i : Fin N, (X i-a)*(U i-c)) / (N : ℝ)
    0 ≤ v ∧ |s| ≤ b * Real.sqrt v ∧ |s / (v+δ)| ≤ b / (2*Real.sqrt δ) := by
  classical
  intro a c v s
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hXsq : 0 ≤ ∑ i : Fin N, (X i-a)^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hv : 0 ≤ v := div_nonneg hXsq hNr.le
  have hCenter : ∑ i : Fin N, (X i-a) = 0 := by
    dsimp [a]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  have hRaw : (∑ i : Fin N, (X i-a)*(U i-c)) = ∑ i : Fin N, (X i-a)*U i := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hCenter, zero_mul, sub_zero]
  have hU2 : (∑ i : Fin N, (U i)^2) ≤ (N : ℝ)*b^2 := by
    calc
      _ ≤ ∑ _i : Fin N, b^2 := Finset.sum_le_sum (fun i _ => by
        have hi := (sq_le_sq₀ (abs_nonneg (U i)) hb).2 (hU i)
        simpa only [sq_abs] using hi)
      _ = _ := by simp
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i : Fin N => X i-a) U
  have hSS : (∑ i : Fin N, (X i-a)*(U i-c))^2 ≤
      (∑ i : Fin N, (X i-a)^2)*((N : ℝ)*b^2) := by
    rw [hRaw]
    exact hCS.trans (mul_le_mul_of_nonneg_left hU2 hXsq)
  have hsSq : s^2 ≤ b^2*v := by
    dsimp [s, v]
    rw [div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos hNr)).2
    calc
      _ ≤ (∑ i : Fin N, (X i-a)^2)*((N : ℝ)*b^2) := hSS
      _ = _ := by field_simp
  have hsBound : |s| ≤ b*Real.sqrt v := by
    apply (sq_le_sq₀ (abs_nonneg s) (mul_nonneg hb (Real.sqrt_nonneg v))).1
    simpa only [sq_abs, mul_pow, Real.sq_sqrt hv] using hsSq
  refine ⟨hv, hsBound, ?_⟩
  have hd : 0 < v+δ := by linarith
  have hsqrt : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hAM : 2*Real.sqrt v*Real.sqrt δ ≤ v+δ := by
    nlinarith [sq_nonneg (Real.sqrt v-Real.sqrt δ), Real.sq_sqrt hv, Real.sq_sqrt hδ.le]
  rw [abs_div, abs_of_pos hd]
  apply (div_le_div_iff₀ hd (by positivity : 0 < 2*Real.sqrt δ)).2
  calc
    |s| * (2*Real.sqrt δ) ≤ (b*Real.sqrt v)*(2*Real.sqrt δ) :=
      mul_le_mul_of_nonneg_right hsBound (by positivity)
    _ = b*(2*Real.sqrt v*Real.sqrt δ) := by ring
    _ ≤ b*(v+δ) := mul_le_mul_of_nonneg_left hAM hb

/-- The manuscript's literal clipped responses discharge every conditional bound
in the covariance calculation, with the exact shared variance and covariance. -/
theorem clippedDataset_covariance_and_ridgeSlope_bound
    (r : ℕ) (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+1))
    (b δ : ℝ) (hb : 0 ≤ b) (hδ : 0 < δ) :
    let X := fun i : Fin (r+1) => (D i).1 0
    let U := fun i : Fin (r+1) => max (min ((D i).2 0) b) (-b)
    let a := (∑ i : Fin (r+1), X i) / (r+1 : ℝ)
    let c := (∑ i : Fin (r+1), U i) / (r+1 : ℝ)
    let v := (∑ i : Fin (r+1), (X i-a)^2) / (r+1 : ℝ)
    let s := (∑ i : Fin (r+1), (X i-a)*(U i-c)) / (r+1 : ℝ)
    0 ≤ v ∧ |s| ≤ b*Real.sqrt v ∧ |s/(v+δ)| ≤ b/(2*Real.sqrt δ) := by
  intro X U
  simpa only [Nat.cast_add, Nat.cast_one] using
    boundedResponse_covariance_and_ridgeSlope_bound (r+1) (by omega) X U b hb
    (fun i => (scalarClipping_lipschitz_and_bound b hb).2 ((D i).2 0)) δ hδ

end LOOConcentration.Manuscript.Internal
