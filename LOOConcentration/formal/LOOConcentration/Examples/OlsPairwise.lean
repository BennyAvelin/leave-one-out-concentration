import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
import LOOConcentration.Examples.OlsDesign

set_option autoImplicit false

namespace LOOConcentration

/-!
# Pairwise OLS control on samples with good design

All vector norms in this file are the unnormalized Euclidean norms given by
finite sums of squares. The estimates compare arbitrary endpoints satisfying
the stated design and norm bounds; no segment condition is used.
-/

/-- The finite-dimensional mean of a real vector. -/
private noncomputable def olsVecMean {r : ℕ} (x : Fin r → ℝ) : ℝ :=
  (∑ i : Fin r, x i) / (r : ℝ)

/-- Center a real vector by subtracting its finite-dimensional mean. -/
private noncomputable def olsVecCenter {r : ℕ} (x : Fin r → ℝ) : Fin r → ℝ :=
  fun i => x i - olsVecMean x

/-- Squared Euclidean norm of a real vector. -/
private def olsVecNormSq {r : ℕ} (x : Fin r → ℝ) : ℝ :=
  ∑ i : Fin r, x i ^ 2

/-- Euclidean norm of a real vector. -/
private noncomputable def olsVecNorm {r : ℕ} (x : Fin r → ℝ) : ℝ :=
  Real.sqrt (olsVecNormSq x)

/-- Euclidean inner product of two real vectors. -/
private def olsVecDot {r : ℕ} (x y : Fin r → ℝ) : ℝ :=
  ∑ i : Fin r, x i * y i

/-- Noise-coordinate Euclidean distance between two samples. -/
noncomputable def olsPairDistance {r : ℕ} (S S' : Fin r → ℝ × ℝ) : ℝ :=
  olsNoiseNorm (fun i => S i - S' i)

/-- Noise-coordinate fitted slope predictor in the notation of the source. -/
noncomputable def olsNoisePredictor {r : ℕ} (S : Fin r → ℝ × ℝ) (u : ℝ) : ℝ :=
  olsEBar S + olsNoiseSlope S * (u - olsXBar S)

private lemma olsVecNormSq_nonneg {r : ℕ} (x : Fin r → ℝ) : 0 ≤ olsVecNormSq x := by
  unfold olsVecNormSq
  exact Finset.sum_nonneg fun i _ => sq_nonneg (x i)

private lemma olsVecMean_sub {r : ℕ} (hr : 0 < r) (x y : Fin r → ℝ) :
    olsVecMean x - olsVecMean y = olsVecMean (fun i => x i - y i) := by
  unfold olsVecMean
  rw [Finset.sum_sub_distrib]
  have hne : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  field_simp [hne]

private lemma olsVecCenter_sub {r : ℕ} (hr : 0 < r) (x y : Fin r → ℝ) :
    (fun i => olsVecCenter x i - olsVecCenter y i) =
      olsVecCenter (fun i => x i - y i) := by
  funext i
  simp only [olsVecCenter]
  calc
    x i - olsVecMean x - (y i - olsVecMean y) =
        x i - y i - (olsVecMean x - olsVecMean y) := by ring
    _ = x i - y i - olsVecMean (fun i => x i - y i) := by
      rw [olsVecMean_sub hr]

private lemma olsVecCenter_normSq_eq {r : ℕ} (hr : 0 < r) (x : Fin r → ℝ) :
    olsVecNormSq (olsVecCenter x) =
      olsVecNormSq x - (∑ i : Fin r, x i) ^ 2 / (r : ℝ) := by
  let c : ℝ := (∑ i : Fin r, x i) / (r : ℝ)
  have hsumCross : (∑ i : Fin r, 2 * x i * c) =
      2 * c * (∑ i : Fin r, x i) := by
    calc
      _ = ∑ i : Fin r, c * (2 * x i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = c * ∑ i : Fin r, 2 * x i := by rw [Finset.mul_sum]
      _ = 2 * c * ∑ i : Fin r, x i := by rw [← Finset.mul_sum]; ring
  have hsumConst : (∑ _i : Fin r, c ^ 2) = (r : ℝ) * c ^ 2 := by
    simp [Finset.sum_const, nsmul_eq_mul]
  unfold olsVecNormSq olsVecCenter olsVecMean
  calc
    _ = ∑ i : Fin r,
        (x i ^ 2 - 2 * x i * ((∑ j : Fin r, x j) / (r : ℝ)) +
          ((∑ j : Fin r, x j) / (r : ℝ)) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (∑ i : Fin r, x i ^ 2) -
        2 * ((∑ j : Fin r, x j) / (r : ℝ)) * (∑ i : Fin r, x i) +
        (r : ℝ) * ((∑ j : Fin r, x j) / (r : ℝ)) ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hsumCross, hsumConst]
    _ = (∑ i : Fin r, x i ^ 2) - (∑ i : Fin r, x i) ^ 2 / (r : ℝ) := by
      have hne : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
      field_simp [hne]
      ring

private lemma olsVecCenter_normSq_le {r : ℕ} (hr : 0 < r) (x : Fin r → ℝ) :
    olsVecNormSq (olsVecCenter x) ≤ olsVecNormSq x := by
  rw [olsVecCenter_normSq_eq hr]
  exact sub_le_self _ (div_nonneg (sq_nonneg _) (by positivity))

private lemma olsVecNorm_nonneg {r : ℕ} (x : Fin r → ℝ) : 0 ≤ olsVecNorm x :=
  Real.sqrt_nonneg _

private lemma olsVecNorm_center_le {r : ℕ} (hr : 0 < r) (x : Fin r → ℝ) :
    olsVecNorm (olsVecCenter x) ≤ olsVecNorm x := by
  unfold olsVecNorm
  exact Real.sqrt_le_sqrt (olsVecCenter_normSq_le hr x)

private lemma olsVecNormSq_x_le_data {r : ℕ} (S : Fin r → ℝ × ℝ) :
    olsVecNormSq (fun i => (S i).1) ≤ olsNoiseNormSq S := by
  unfold olsVecNormSq olsNoiseNormSq
  exact Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (S i).2]

private lemma olsVecNormSq_e_le_data {r : ℕ} (S : Fin r → ℝ × ℝ) :
    olsVecNormSq (fun i => (S i).2) ≤ olsNoiseNormSq S := by
  unfold olsVecNormSq olsNoiseNormSq
  exact Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (S i).1]

private lemma olsVecNorm_x_le_data {r : ℕ} (S : Fin r → ℝ × ℝ) :
    olsVecNorm (fun i => (S i).1) ≤ olsNoiseNorm S := by
  unfold olsVecNorm olsNoiseNorm
  exact Real.sqrt_le_sqrt (olsVecNormSq_x_le_data S)

private lemma olsVecNorm_e_le_data {r : ℕ} (S : Fin r → ℝ × ℝ) :
    olsVecNorm (fun i => (S i).2) ≤ olsNoiseNorm S := by
  unfold olsVecNorm olsNoiseNorm
  exact Real.sqrt_le_sqrt (olsVecNormSq_e_le_data S)

private lemma olsVecDot_abs_le {r : ℕ} (x y : Fin r → ℝ) :
    |olsVecDot x y| ≤ olsVecNorm x * olsVecNorm y := by
  have hcs : (olsVecDot x y) ^ 2 ≤ olsVecNormSq x * olsVecNormSq y := by
    simpa [olsVecDot, olsVecNormSq] using
      (Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ) x y)
  apply (sq_le_sq₀ (abs_nonneg (olsVecDot x y))
    (mul_nonneg (olsVecNorm_nonneg x) (olsVecNorm_nonneg y))).1
  rw [sq_abs, mul_pow, olsVecNorm, olsVecNorm,
    Real.sq_sqrt (olsVecNormSq_nonneg x), Real.sq_sqrt (olsVecNormSq_nonneg y)]
  exact hcs

private lemma olsVecNormSq_add_le {r : ℕ} (x y : Fin r → ℝ) :
    olsVecNormSq (fun i => x i + y i) ≤ 2 * (olsVecNormSq x + olsVecNormSq y) := by
  unfold olsVecNormSq
  calc
    _ ≤ ∑ i : Fin r, (2 * x i ^ 2 + 2 * y i ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      nlinarith only [sq_nonneg (x i - y i)]
    _ = 2 * ((∑ i : Fin r, x i ^ 2) + (∑ i : Fin r, y i ^ 2)) := by
      simp [Finset.sum_add_distrib, ← Finset.mul_sum]
      ring

private lemma olsVecNorm_add_le {r : ℕ} {N : ℕ} (hN : 0 < N)
    (x y : Fin r → ℝ) (hx : olsVecNorm x ≤ 3 * Real.sqrt (N : ℝ))
    (hy : olsVecNorm y ≤ 3 * Real.sqrt (N : ℝ)) :
    olsVecNorm (fun i => x i + y i) ≤ 6 * Real.sqrt (N : ℝ) := by
  have hNreal : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
  have hsqrtN : (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) := Real.sq_sqrt hNreal
  have hxSq : olsVecNormSq x ≤ 9 * (N : ℝ) := by
    have hxNonneg : 0 ≤ olsVecNorm x := olsVecNorm_nonneg x
    have hRhs : 0 ≤ 3 * Real.sqrt (N : ℝ) := by positivity
    have := (sq_le_sq₀ hxNonneg hRhs).2 hx
    calc
      olsVecNormSq x = olsVecNorm x ^ 2 := by
        simp [olsVecNorm, Real.sq_sqrt (olsVecNormSq_nonneg x)]
      _ ≤ (3 * Real.sqrt (N : ℝ)) ^ 2 := this
      _ = 9 * (N : ℝ) := by rw [mul_pow, hsqrtN]; norm_num
  have hySq : olsVecNormSq y ≤ 9 * (N : ℝ) := by
    have hyNonneg : 0 ≤ olsVecNorm y := olsVecNorm_nonneg y
    have hRhs : 0 ≤ 3 * Real.sqrt (N : ℝ) := by positivity
    have := (sq_le_sq₀ hyNonneg hRhs).2 hy
    calc
      olsVecNormSq y = olsVecNorm y ^ 2 := by
        simp [olsVecNorm, Real.sq_sqrt (olsVecNormSq_nonneg y)]
      _ ≤ (3 * Real.sqrt (N : ℝ)) ^ 2 := this
      _ = 9 * (N : ℝ) := by rw [mul_pow, hsqrtN]; norm_num
  have hsumSq := olsVecNormSq_add_le x y
  have hsumSq' : olsVecNormSq (fun i => x i + y i) ≤ (6 * Real.sqrt (N : ℝ)) ^ 2 := by
    nlinarith [hNreal, hxSq, hySq]
  exact (Real.sqrt_le_iff).2 ⟨by positivity, hsumSq'⟩

private lemma olsVecNorm_center_x_le_data {r : ℕ} (hr : 0 < r)
    (S : Fin r → ℝ × ℝ) :
    olsVecNorm (olsVecCenter fun i => (S i).1) ≤ olsNoiseNorm S := by
  exact (olsVecNorm_center_le hr _).trans (olsVecNorm_x_le_data S)

private lemma olsVecNorm_center_e_le_data {r : ℕ} (hr : 0 < r)
    (S : Fin r → ℝ × ℝ) :
    olsVecNorm (olsVecCenter fun i => (S i).2) ≤ olsNoiseNorm S := by
  exact (olsVecNorm_center_le hr _).trans (olsVecNorm_e_le_data S)

private lemma olsVecNorm_center_x_sub_le_dist {r : ℕ} (hr : 0 < r)
    (S S' : Fin r → ℝ × ℝ) :
    olsVecNorm (fun i => olsVecCenter (fun j => (S j).1) i -
      olsVecCenter (fun j => (S' j).1) i) ≤ olsPairDistance S S' := by
  rw [olsVecCenter_sub hr]
  change olsVecNorm (olsVecCenter (fun i => (S i).1 - (S' i).1)) ≤
    olsNoiseNorm (fun i => S i - S' i)
  unfold olsVecNorm olsNoiseNorm
  apply Real.sqrt_le_sqrt
  calc
    olsVecNormSq (olsVecCenter fun i => (S i).1 - (S' i).1) ≤
        olsVecNormSq (fun i => (S i).1 - (S' i).1) :=
      olsVecCenter_normSq_le hr _
    _ ≤ olsNoiseNormSq (fun i => S i - S' i) := by
      unfold olsVecNormSq olsNoiseNormSq
      exact Finset.sum_le_sum fun i _ => by
        change ((S i).1 - (S' i).1) ^ 2 ≤
          ((S i).1 - (S' i).1) ^ 2 + ((S i).2 - (S' i).2) ^ 2
        exact le_add_of_nonneg_right (sq_nonneg _)

private lemma olsVecNorm_center_e_sub_le_dist {r : ℕ} (hr : 0 < r)
    (S S' : Fin r → ℝ × ℝ) :
    olsVecNorm (fun i => olsVecCenter (fun j => (S j).2) i -
      olsVecCenter (fun j => (S' j).2) i) ≤ olsPairDistance S S' := by
  rw [olsVecCenter_sub hr]
  change olsVecNorm (olsVecCenter (fun i => (S i).2 - (S' i).2)) ≤
    olsNoiseNorm (fun i => S i - S' i)
  unfold olsVecNorm olsNoiseNorm
  apply Real.sqrt_le_sqrt
  calc
    olsVecNormSq (olsVecCenter fun i => (S i).2 - (S' i).2) ≤
        olsVecNormSq (fun i => (S i).2 - (S' i).2) :=
      olsVecCenter_normSq_le hr _
    _ ≤ olsNoiseNormSq (fun i => S i - S' i) := by
      unfold olsVecNormSq olsNoiseNormSq
      exact Finset.sum_le_sum fun i _ => by
        change ((S i).2 - (S' i).2) ^ 2 ≤
          ((S i).1 - (S' i).1) ^ 2 + ((S i).2 - (S' i).2) ^ 2
        exact le_add_of_nonneg_left (sq_nonneg _)

private lemma olsVecDot_sub_mul {r : ℕ} (x x' y y' : Fin r → ℝ) :
    olsVecDot x y - olsVecDot x' y' =
      olsVecDot (fun i => x i - x' i) y + olsVecDot x' (fun i => y i - y' i) := by
  unfold olsVecDot
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

private lemma olsCenteredCross_sub_eq {r : ℕ}
    (S S' : Fin r → ℝ × ℝ) :
    olsCenteredCross S - olsCenteredCross S' =
      olsVecDot
        (fun i => olsVecCenter (fun j => (S j).1) i -
          olsVecCenter (fun j => (S' j).1) i)
        (olsVecCenter fun j => (S j).2) +
      olsVecDot (olsVecCenter fun j => (S' j).1)
        (fun i => olsVecCenter (fun j => (S j).2) i -
          olsVecCenter (fun j => (S' j).2) i) := by
  rw [show olsCenteredCross S =
      olsVecDot (olsVecCenter fun j => (S j).1) (olsVecCenter fun j => (S j).2) by rfl]
  rw [show olsCenteredCross S' =
      olsVecDot (olsVecCenter fun j => (S' j).1) (olsVecCenter fun j => (S' j).2) by rfl]
  exact olsVecDot_sub_mul _ _ _ _

theorem ols_centeredCross_difference_bound {N r : ℕ} (hr : 0 < r)
    (S S' : Fin r → ℝ × ℝ)
    (hS : olsNoiseNorm S ≤ 3 * Real.sqrt (N : ℝ))
    (hS' : olsNoiseNorm S' ≤ 3 * Real.sqrt (N : ℝ)) :
    |olsCenteredCross S - olsCenteredCross S'| ≤
      6 * Real.sqrt (N : ℝ) * olsPairDistance S S' := by
  have hidentity := olsCenteredCross_sub_eq S S'
  rw [hidentity]
  have hdx := olsVecNorm_center_x_sub_le_dist hr S S'
  have hde := olsVecNorm_center_e_sub_le_dist hr S S'
  have hW := (olsVecNorm_center_e_le_data hr S).trans hS
  have hUp := (olsVecNorm_center_x_le_data hr S').trans hS'
  have hnonnegDist : 0 ≤ olsPairDistance S S' := Real.sqrt_nonneg _
  have hbound1 : |olsVecDot
      (fun i => olsVecCenter (fun j => (S j).1) i -
        olsVecCenter (fun j => (S' j).1) i)
      (olsVecCenter fun j => (S j).2)| ≤
        olsPairDistance S S' * (3 * Real.sqrt (N : ℝ)) := by
    calc
      _ ≤ olsVecNorm (fun i => olsVecCenter (fun j => (S j).1) i -
          olsVecCenter (fun j => (S' j).1) i) *
          olsVecNorm (olsVecCenter fun j => (S j).2) := olsVecDot_abs_le _ _
      _ ≤ olsPairDistance S S' * (3 * Real.sqrt (N : ℝ)) := by
        exact mul_le_mul hdx hW (olsVecNorm_nonneg _) (by positivity)
  have hbound2 : |olsVecDot (olsVecCenter fun j => (S' j).1)
      (fun i => olsVecCenter (fun j => (S j).2) i -
        olsVecCenter (fun j => (S' j).2) i)| ≤
        (3 * Real.sqrt (N : ℝ)) * olsPairDistance S S' := by
    calc
      _ ≤ olsVecNorm (olsVecCenter fun j => (S' j).1) *
          olsVecNorm (fun i => olsVecCenter (fun j => (S j).2) i -
            olsVecCenter (fun j => (S' j).2) i) := olsVecDot_abs_le _ _
      _ ≤ (3 * Real.sqrt (N : ℝ)) * olsPairDistance S S' := by
        exact mul_le_mul hUp hde (olsVecNorm_nonneg _) (by positivity)
  calc
    _ ≤ |olsVecDot
        (fun i => olsVecCenter (fun j => (S j).1) i -
          olsVecCenter (fun j => (S' j).1) i)
        (olsVecCenter fun j => (S j).2)| +
      |olsVecDot (olsVecCenter fun j => (S' j).1)
          (fun i => olsVecCenter (fun j => (S j).2) i -
          olsVecCenter (fun j => (S' j).2) i)| := abs_add_le _ _
    _ ≤ olsPairDistance S S' * (3 * Real.sqrt (N : ℝ)) +
        (3 * Real.sqrt (N : ℝ)) * olsPairDistance S S' := add_le_add hbound1 hbound2
    _ = 6 * Real.sqrt (N : ℝ) * olsPairDistance S S' := by ring

private lemma olsVecNormSq_sub_eq_dot {r : ℕ} (x y : Fin r → ℝ) :
    olsVecNormSq x - olsVecNormSq y =
      olsVecDot (fun i => x i - y i) (fun i => x i + y i) := by
  unfold olsVecNormSq olsVecDot
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem ols_centeredDesign_difference_bound {N r : ℕ} (hN : 0 < N) (hr : 0 < r)
    (S S' : Fin r → ℝ × ℝ)
    (hS : olsNoiseNorm S ≤ 3 * Real.sqrt (N : ℝ))
    (hS' : olsNoiseNorm S' ≤ 3 * Real.sqrt (N : ℝ)) :
    |olsCenteredDesign S - olsCenteredDesign S'| ≤
      6 * Real.sqrt (N : ℝ) * olsPairDistance S S' := by
  have hidentity : olsCenteredDesign S - olsCenteredDesign S' =
      olsVecDot
        (fun i => olsVecCenter (fun j => (S j).1) i -
          olsVecCenter (fun j => (S' j).1) i)
        (fun i => olsVecCenter (fun j => (S j).1) i +
          olsVecCenter (fun j => (S' j).1) i) := by
    rw [show olsCenteredDesign S =
        olsVecNormSq (olsVecCenter fun j => (S j).1) by rfl]
    rw [show olsCenteredDesign S' =
        olsVecNormSq (olsVecCenter fun j => (S' j).1) by rfl]
    exact olsVecNormSq_sub_eq_dot _ _
  rw [hidentity]
  have hdx := olsVecNorm_center_x_sub_le_dist hr S S'
  have hplus := olsVecNorm_add_le hN _ _
    ((olsVecNorm_center_x_le_data hr S).trans hS)
    ((olsVecNorm_center_x_le_data hr S').trans hS')
  have hbound : |olsVecDot
      (fun i => olsVecCenter (fun j => (S j).1) i -
        olsVecCenter (fun j => (S' j).1) i)
      (fun i => olsVecCenter (fun j => (S j).1) i +
        olsVecCenter (fun j => (S' j).1) i)| ≤
        olsPairDistance S S' * (6 * Real.sqrt (N : ℝ)) := by
    calc
      _ ≤ olsVecNorm (fun i => olsVecCenter (fun j => (S j).1) i -
          olsVecCenter (fun j => (S' j).1) i) *
          olsVecNorm (fun i => olsVecCenter (fun j => (S j).1) i +
            olsVecCenter (fun j => (S' j).1) i) := olsVecDot_abs_le _ _
      _ ≤ olsPairDistance S S' * (6 * Real.sqrt (N : ℝ)) := by
        exact mul_le_mul hdx hplus (olsVecNorm_nonneg _) (Real.sqrt_nonneg _)
  calc
    _ ≤ olsPairDistance S S' * (6 * Real.sqrt (N : ℝ)) := hbound
    _ = 6 * Real.sqrt (N : ℝ) * olsPairDistance S S' := by ring

end LOOConcentration
