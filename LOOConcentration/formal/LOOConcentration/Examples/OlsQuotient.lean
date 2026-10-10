import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
import LOOConcentration.Examples.OlsPairwise

set_option autoImplicit false

namespace LOOConcentration

private noncomputable def olsQMean {r : ℕ} (x : Fin r → ℝ) : ℝ :=
  (∑ i : Fin r, x i) / (r : ℝ)

private noncomputable def olsQCenter {r : ℕ} (x : Fin r → ℝ) : Fin r → ℝ :=
  fun i => x i - olsQMean x

private def olsQNormSq {r : ℕ} (x : Fin r → ℝ) : ℝ :=
  ∑ i : Fin r, x i ^ 2

private lemma olsQCenter_normSq_eq {r : ℕ} (hr : 0 < r) (x : Fin r → ℝ) :
    olsQNormSq (olsQCenter x) =
      olsQNormSq x - (∑ i : Fin r, x i) ^ 2 / (r : ℝ) := by
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
  unfold olsQNormSq olsQCenter olsQMean
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

private lemma olsQCenter_normSq_le {r : ℕ} (hr : 0 < r) (x : Fin r → ℝ) :
    olsQNormSq (olsQCenter x) ≤ olsQNormSq x := by
  rw [olsQCenter_normSq_eq hr]
  exact sub_le_self _ (div_nonneg (sq_nonneg _) (by positivity))

private lemma olsQData_normSq_nonneg {r : ℕ} (S : Fin r → ℝ × ℝ) :
    0 ≤ olsNoiseNormSq S := by
  unfold olsNoiseNormSq
  exact Finset.sum_nonneg fun i _ => add_nonneg (sq_nonneg _) (sq_nonneg _)

private lemma olsQData_normSq_bound {N r : ℕ} (S : Fin r → ℝ × ℝ)
    (hS : olsNoiseNorm S ≤ 3 * Real.sqrt (N : ℝ)) :
    olsNoiseNormSq S ≤ 9 * (N : ℝ) := by
  have hsq := (sq_le_sq₀ (Real.sqrt_nonneg (olsNoiseNormSq S))
      (by positivity : 0 ≤ 3 * Real.sqrt (N : ℝ))).2 hS
  rw [Real.sq_sqrt (olsQData_normSq_nonneg S)] at hsq
  calc
    olsNoiseNormSq S ≤ (3 * Real.sqrt (N : ℝ)) ^ 2 := hsq
    _ = 9 * (N : ℝ) := by
      rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (N : ℝ))]
      ring

private lemma olsQX_raw_normSq_le {r : ℕ} (S : Fin r → ℝ × ℝ) :
    olsQNormSq (fun i => (S i).1) ≤ olsNoiseNormSq S := by
  unfold olsQNormSq olsNoiseNormSq
  exact Finset.sum_le_sum fun i _ => le_add_of_nonneg_right (sq_nonneg (S i).2)

private lemma olsQE_raw_normSq_le {r : ℕ} (S : Fin r → ℝ × ℝ) :
    olsQNormSq (fun i => (S i).2) ≤ olsNoiseNormSq S := by
  unfold olsQNormSq olsNoiseNormSq
  exact Finset.sum_le_sum fun i _ => le_add_of_nonneg_left (sq_nonneg (S i).1)

private lemma olsQX_center_normSq_le {r : ℕ} (hr : 0 < r)
    (S : Fin r → ℝ × ℝ) :
    olsQNormSq (olsQCenter fun i => (S i).1) ≤ olsNoiseNormSq S :=
  (olsQCenter_normSq_le hr _).trans (olsQX_raw_normSq_le S)

private lemma olsQE_center_normSq_le {r : ℕ} (hr : 0 < r)
    (S : Fin r → ℝ × ℝ) :
    olsQNormSq (olsQCenter fun i => (S i).2) ≤ olsNoiseNormSq S :=
  (olsQCenter_normSq_le hr _).trans (olsQE_raw_normSq_le S)

private lemma olsQCenteredCross_sq_le {r : ℕ} (S : Fin r → ℝ × ℝ) :
    olsCenteredCross S ^ 2 ≤
      olsQNormSq (olsQCenter fun i => (S i).1) *
        olsQNormSq (olsQCenter fun i => (S i).2) := by
  simpa [olsCenteredCross, olsQNormSq, olsQCenter, olsQMean, olsXBar, olsEBar] using
    (Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
      (fun i : Fin r => (S i).1 - olsXBar S)
      (fun i : Fin r => (S i).2 - olsEBar S))

theorem ols_centeredCross_abs_le {N r : ℕ} (hr : 0 < r)
    (S : Fin r → ℝ × ℝ)
    (hS : olsNoiseNorm S ≤ 3 * Real.sqrt (N : ℝ)) :
    |olsCenteredCross S| ≤ 9 * (N : ℝ) := by
  have hdata := olsQData_normSq_bound S hS
  have hcx : olsQNormSq (olsQCenter fun i => (S i).1) ≤ 9 * (N : ℝ) :=
    (olsQX_center_normSq_le hr S).trans hdata
  have hce : olsQNormSq (olsQCenter fun i => (S i).2) ≤ 9 * (N : ℝ) :=
    (olsQE_center_normSq_le hr S).trans hdata
  have hceNonneg : 0 ≤ olsQNormSq (olsQCenter fun i => (S i).2) := by
    unfold olsQNormSq
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hprod :
      olsQNormSq (olsQCenter fun i => (S i).1) *
          olsQNormSq (olsQCenter fun i => (S i).2) ≤
        (9 * (N : ℝ)) * (9 * (N : ℝ)) := by
    calc
      _ ≤ (9 * (N : ℝ)) *
          olsQNormSq (olsQCenter fun i => (S i).2) :=
        mul_le_mul_of_nonneg_right hcx hceNonneg
      _ ≤ (9 * (N : ℝ)) * (9 * (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hce (by positivity)
  apply (sq_le_sq₀ (abs_nonneg (olsCenteredCross S)) (by positivity)).1
  rw [sq_abs]
  exact (olsQCenteredCross_sq_le S).trans (by simpa [pow_two] using hprod)

private lemma olsQuotient_difference_bound {N : ℕ} (hN : 0 < N)
    {a a' d d' Δ : ℝ}
    (hΔ : 0 ≤ Δ)
    (hnum : |a - a'| ≤ 6 * Real.sqrt (N : ℝ) * Δ)
    (hden : |d - d'| ≤ 6 * Real.sqrt (N : ℝ) * Δ)
    (hcross : |a'| ≤ 9 * (N : ℝ))
    (hd : (N : ℝ) / 4 ≤ d) (hd' : (N : ℝ) / 4 ≤ d') :
    |a / d - a' / d'| ≤ 888 * Δ / Real.sqrt (N : ℝ) := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have htpos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNpos
  have htSq : (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hquarterPos : 0 < (N : ℝ) / 4 := by positivity
  have hdpos : 0 < d := lt_of_lt_of_le hquarterPos hd
  have hd'pos : 0 < d' := lt_of_lt_of_le hquarterPos hd'
  have hdenPos : 0 < d * d' := mul_pos hdpos hd'pos
  have hdecomp : a / d - a' / d' =
      (a - a') / d + a' * (d' - d) / (d * d') := by
    field_simp [hdpos.ne', hd'pos.ne']
    ring
  have hnumNonneg : 0 ≤ 6 * Real.sqrt (N : ℝ) * Δ := by positivity
  have hcrossNonneg : 0 ≤ 9 * (N : ℝ) := by positivity
  have hdenDiffAbs : |d' - d| ≤ 6 * Real.sqrt (N : ℝ) * Δ := by
    simpa [abs_sub_comm] using hden
  have hfirst : |a - a'| / d ≤
      (6 * Real.sqrt (N : ℝ) * Δ) / ((N : ℝ) / 4) := by
    exact (div_le_div_of_nonneg_right hnum (le_of_lt hdpos)).trans
      (div_le_div_of_nonneg_left hnumNonneg hquarterPos hd)
  have hsecondNumerator : |a'| * |d' - d| ≤
      (9 * (N : ℝ)) * (6 * Real.sqrt (N : ℝ) * Δ) := by
    exact mul_le_mul hcross hdenDiffAbs (abs_nonneg _) hcrossNonneg
  have hquarterProduct : ((N : ℝ) / 4) * ((N : ℝ) / 4) ≤ d * d' := by
    calc
      _ ≤ d * ((N : ℝ) / 4) :=
        mul_le_mul_of_nonneg_right hd (le_of_lt hquarterPos)
      _ ≤ d * d' := mul_le_mul_of_nonneg_left hd' (le_of_lt hdpos)
  have hquarterProductPos : 0 < ((N : ℝ) / 4) * ((N : ℝ) / 4) :=
    mul_pos hquarterPos hquarterPos
  have hsecond : (|a'| * |d' - d|) / (d * d') ≤
      ((9 * (N : ℝ)) * (6 * Real.sqrt (N : ℝ) * Δ)) /
        (((N : ℝ) / 4) * ((N : ℝ) / 4)) := by
    exact (div_le_div_of_nonneg_right hsecondNumerator (le_of_lt hdenPos)).trans
      (div_le_div_of_nonneg_left
        (mul_nonneg hcrossNonneg hnumNonneg) hquarterProductPos hquarterProduct)
  have hfirstExact :
      (6 * Real.sqrt (N : ℝ) * Δ) / ((N : ℝ) / 4) =
        24 * Δ / Real.sqrt (N : ℝ) := by
    rw [← htSq]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos htpos]
    field_simp [htpos.ne']
    ring_nf
  have hsecondExact :
      ((9 * (N : ℝ)) * (6 * Real.sqrt (N : ℝ) * Δ)) /
        (((N : ℝ) / 4) * ((N : ℝ) / 4)) =
        864 * Δ / Real.sqrt (N : ℝ) := by
    rw [← htSq]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos htpos]
    field_simp [htpos.ne']
    ring_nf
  calc
    |a / d - a' / d'| ≤
        |(a - a') / d| + |a' * (d' - d) / (d * d')| := by
          rw [hdecomp]
          exact abs_add_le _ _
    _ = |a - a'| / d + (|a'| * |d' - d|) / (d * d') := by
      simp only [abs_div, abs_mul, abs_of_pos hdpos, abs_of_pos hdenPos]
    _ ≤ ((6 * Real.sqrt (N : ℝ) * Δ) / ((N : ℝ) / 4)) +
        (((9 * (N : ℝ)) * (6 * Real.sqrt (N : ℝ) * Δ)) /
          (((N : ℝ) / 4) * ((N : ℝ) / 4))) := add_le_add hfirst hsecond
    _ = 888 * Δ / Real.sqrt (N : ℝ) := by rw [hfirstExact, hsecondExact]; ring

theorem ols_noiseSlope_abs_le {N r : ℕ} (hN : 0 < N) (hr : 0 < r)
    (S : Fin r → ℝ × ℝ)
    (hS : olsNoiseNorm S ≤ 3 * Real.sqrt (N : ℝ))
    (hd : (N : ℝ) / 4 ≤ olsCenteredDesign S) :
    |olsNoiseSlope S| ≤ 6 := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hDpos : 0 < olsCenteredDesign S :=
    lt_of_lt_of_le (by positivity) hd
  have hDnonneg : 0 ≤ olsCenteredDesign S := hDpos.le
  have hDsq : (Real.sqrt (olsCenteredDesign S)) ^ 2 = olsCenteredDesign S :=
    Real.sq_sqrt hDnonneg
  have hNsq : (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hEcenter :
      olsQNormSq (olsQCenter fun i => (S i).2) ≤ 9 * (N : ℝ) :=
    (olsQE_center_normSq_le hr S).trans (olsQData_normSq_bound S hS)
  have hEcenterNonneg :
      0 ≤ olsQNormSq (olsQCenter fun i => (S i).2) := by
    unfold olsQNormSq
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hCS := olsQCenteredCross_sq_le S
  have hXcenterEq :
      olsQNormSq (olsQCenter fun i => (S i).1) = olsCenteredDesign S := by rfl
  have hcrossSq : olsCenteredCross S ^ 2 ≤
      olsCenteredDesign S * (9 * (N : ℝ)) := by
    calc
      _ ≤ olsQNormSq (olsQCenter fun i => (S i).1) *
          olsQNormSq (olsQCenter fun i => (S i).2) := hCS
      _ = olsCenteredDesign S * olsQNormSq (olsQCenter fun i => (S i).2) := by
        rw [hXcenterEq]
      _ ≤ olsCenteredDesign S * (9 * (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hEcenter hDnonneg
  have hcrossAbs : |olsCenteredCross S| ≤
      Real.sqrt (olsCenteredDesign S) * (3 * Real.sqrt (N : ℝ)) := by
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).1
    rw [sq_abs]
    calc
      _ ≤ olsCenteredDesign S * (9 * (N : ℝ)) := hcrossSq
      _ = (Real.sqrt (olsCenteredDesign S) * (3 * Real.sqrt (N : ℝ))) ^ 2 := by
        rw [mul_pow, hDsq, mul_pow, hNsq]
        ring
  have hrootPos : 0 < Real.sqrt (olsCenteredDesign S) := Real.sqrt_pos.2 hDpos
  have hrootBound : 3 * Real.sqrt (N : ℝ) ≤
      6 * Real.sqrt (olsCenteredDesign S) := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).1
    rw [mul_pow, hNsq, mul_pow, hDsq]
    nlinarith only [hd]
  have hcancel :
      (Real.sqrt (olsCenteredDesign S) * (3 * Real.sqrt (N : ℝ))) /
          olsCenteredDesign S =
        (3 * Real.sqrt (N : ℝ)) / Real.sqrt (olsCenteredDesign S) := by
    rw [← hDsq]
    field_simp [hrootPos.ne']
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hrootPos]
  unfold olsNoiseSlope
  rw [abs_div, abs_of_pos hDpos]
  calc
    |olsCenteredCross S| / olsCenteredDesign S ≤
        (Real.sqrt (olsCenteredDesign S) * (3 * Real.sqrt (N : ℝ))) /
          olsCenteredDesign S :=
      div_le_div_of_nonneg_right hcrossAbs hDpos.le
    _ = 3 * Real.sqrt (N : ℝ) / Real.sqrt (olsCenteredDesign S) := hcancel
    _ ≤ 6 := (div_le_iff₀ hrootPos).2 hrootBound

theorem ols_noiseSlope_pairwise_bound {N r : ℕ} (hN : 0 < N) (hr : 0 < r)
    (S S' : Fin r → ℝ × ℝ)
    (hS : olsNoiseNorm S ≤ 3 * Real.sqrt (N : ℝ))
    (hS' : olsNoiseNorm S' ≤ 3 * Real.sqrt (N : ℝ))
    (hd : (N : ℝ) / 4 ≤ olsCenteredDesign S)
    (hd' : (N : ℝ) / 4 ≤ olsCenteredDesign S') :
    |olsNoiseSlope S - olsNoiseSlope S'| ≤
      888 * olsPairDistance S S' / Real.sqrt (N : ℝ) := by
  apply olsQuotient_difference_bound hN (Real.sqrt_nonneg _)
    (ols_centeredCross_difference_bound hr S S' hS hS')
    (ols_centeredDesign_difference_bound hN hr S S' hS hS')
    (ols_centeredCross_abs_le hr S' hS') hd hd'

private lemma olsQMean_sq_le {r : ℕ} (x : Fin r → ℝ) :
    olsQMean x ^ 2 ≤ olsQNormSq x / (r : ℝ) := by
  have h := sum_div_card_sq_le_sum_sq_div_card
    (s := Finset.univ) (f := x)
  simpa [olsQMean, olsQNormSq] using h

private lemma olsQMean_sub {r : ℕ} (hr : 0 < r) (x y : Fin r → ℝ) :
    olsQMean x - olsQMean y = olsQMean (fun i => x i - y i) := by
  unfold olsQMean
  rw [Finset.sum_sub_distrib]
  have hne : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  field_simp [hne]

private lemma olsQMean_abs_le_five {N r : ℕ} (hN : 0 < N) (hr : 0 < r)
    (hNr : (N : ℝ) ≤ 2 * (r : ℝ)) (x : Fin r → ℝ)
    (hRaw : olsQNormSq x ≤ 9 * (N : ℝ)) : |olsQMean x| ≤ 5 := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast hr
  have hRatio : (N : ℝ) / (r : ℝ) ≤ 2 := (div_le_iff₀ hrpos).2 hNr
  have hMeanSq : olsQMean x ^ 2 ≤ 25 := by
    calc
      _ ≤ olsQNormSq x / (r : ℝ) := olsQMean_sq_le x
      _ ≤ (9 * (N : ℝ)) / (r : ℝ) :=
        div_le_div_of_nonneg_right hRaw (le_of_lt hrpos)
      _ = 9 * ((N : ℝ) / (r : ℝ)) := by ring
      _ ≤ 9 * 2 := mul_le_mul_of_nonneg_left hRatio (by norm_num)
      _ ≤ 25 := by norm_num
  apply (sq_le_sq₀ (abs_nonneg _) (by norm_num : 0 ≤ (5 : ℝ))).1
  rw [sq_abs]
  nlinarith only [hMeanSq]

private lemma olsQPairDistance_sq {r : ℕ} (S S' : Fin r → ℝ × ℝ) :
    olsPairDistance S S' ^ 2 =
      olsNoiseNormSq (fun i => S i - S' i) := by
  unfold olsPairDistance olsNoiseNorm
  exact Real.sq_sqrt (olsQData_normSq_nonneg _)

private lemma olsQDiffX_normSq_le_distance_sq {r : ℕ}
    (S S' : Fin r → ℝ × ℝ) :
    olsQNormSq (fun i => (S i).1 - (S' i).1) ≤ olsPairDistance S S' ^ 2 := by
  rw [olsQPairDistance_sq]
  unfold olsQNormSq olsNoiseNormSq
  exact Finset.sum_le_sum fun i _ =>
    le_add_of_nonneg_right (sq_nonneg ((S i).2 - (S' i).2))

private lemma olsQDiffE_normSq_le_distance_sq {r : ℕ}
    (S S' : Fin r → ℝ × ℝ) :
    olsQNormSq (fun i => (S i).2 - (S' i).2) ≤ olsPairDistance S S' ^ 2 := by
  rw [olsQPairDistance_sq]
  unfold olsQNormSq olsNoiseNormSq
  exact Finset.sum_le_sum fun i _ =>
    le_add_of_nonneg_left (sq_nonneg ((S i).1 - (S' i).1))

private lemma olsQMean_difference_bound {N r : ℕ} (hN : 0 < N) (hr : 0 < r)
    (hNr : (N : ℝ) ≤ 2 * (r : ℝ)) (x y : Fin r → ℝ)
    (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hxy : olsQNormSq (fun i => x i - y i) ≤ Δ ^ 2) :
    |olsQMean x - olsQMean y| ≤ 2 * Δ / Real.sqrt (N : ℝ) := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast hr
  have htpos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNpos
  have htSq : (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) := Real.sq_sqrt (by positivity)
  have hratio : Δ ^ 2 / (r : ℝ) ≤ 2 * Δ ^ 2 / (N : ℝ) := by
    rw [div_le_div_iff₀ hrpos hNpos]
    have hmul := mul_le_mul_of_nonneg_right hNr (sq_nonneg Δ)
    nlinarith only [hmul]
  have hscale : 2 * Δ ^ 2 / (N : ℝ) ≤ 4 * Δ ^ 2 / (N : ℝ) := by
    apply div_le_div_of_nonneg_right _ (le_of_lt hNpos)
    nlinarith only [sq_nonneg Δ]
  have htargetSq : 4 * Δ ^ 2 / (N : ℝ) =
      (2 * Δ / Real.sqrt (N : ℝ)) ^ 2 := by
    rw [div_pow, mul_pow, htSq]
    field_simp [hNpos.ne']
    ring
  have hmeanEq := olsQMean_sub hr x y
  have hmeanSq : (olsQMean x - olsQMean y) ^ 2 ≤
      (2 * Δ / Real.sqrt (N : ℝ)) ^ 2 := by
    rw [hmeanEq]
    calc
      _ ≤ olsQNormSq (fun i => x i - y i) / (r : ℝ) :=
        olsQMean_sq_le _
      _ ≤ Δ ^ 2 / (r : ℝ) :=
        div_le_div_of_nonneg_right hxy (le_of_lt hrpos)
      _ ≤ 2 * Δ ^ 2 / (N : ℝ) := hratio
      _ ≤ 4 * Δ ^ 2 / (N : ℝ) := hscale
      _ = (2 * Δ / Real.sqrt (N : ℝ)) ^ 2 := htargetSq
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).1
  rw [sq_abs]
  exact hmeanSq

private lemma olsXBar_abs_le_five {N r : ℕ} (hN : 0 < N) (hr : 0 < r)
    (hNr : (N : ℝ) ≤ 2 * (r : ℝ)) (S : Fin r → ℝ × ℝ)
    (hS : olsNoiseNorm S ≤ 3 * Real.sqrt (N : ℝ)) : |olsXBar S| ≤ 5 := by
  apply olsQMean_abs_le_five hN hr hNr _
  exact (olsQX_raw_normSq_le S).trans (olsQData_normSq_bound S hS)

private lemma olsXBar_difference_bound {N r : ℕ} (hN : 0 < N) (hr : 0 < r)
    (hNr : (N : ℝ) ≤ 2 * (r : ℝ)) (S S' : Fin r → ℝ × ℝ) :
    |olsXBar S - olsXBar S'| ≤
      2 * olsPairDistance S S' / Real.sqrt (N : ℝ) := by
  have h := olsQMean_difference_bound hN hr hNr
    (fun i => (S i).1) (fun i => (S' i).1) (olsPairDistance S S')
    (Real.sqrt_nonneg _) (olsQDiffX_normSq_le_distance_sq S S')
  simpa [olsXBar, olsQMean] using h

private lemma olsEBar_difference_bound {N r : ℕ} (hN : 0 < N) (hr : 0 < r)
    (hNr : (N : ℝ) ≤ 2 * (r : ℝ)) (S S' : Fin r → ℝ × ℝ) :
    |olsEBar S - olsEBar S'| ≤
      2 * olsPairDistance S S' / Real.sqrt (N : ℝ) := by
  have h := olsQMean_difference_bound hN hr hNr
    (fun i => (S i).2) (fun i => (S' i).2) (olsPairDistance S S')
    (Real.sqrt_nonneg _) (olsQDiffE_normSq_le_distance_sq S S')
  simpa [olsEBar, olsQMean] using h

theorem ols_noisePredictor_pairwise_bound {N r : ℕ} (hN : 0 < N) (hr : 0 < r)
    (hNr : (N : ℝ) ≤ 2 * (r : ℝ))
    (S S' : Fin r → ℝ × ℝ)
    (hS : olsNoiseNorm S ≤ 3 * Real.sqrt (N : ℝ))
    (hS' : olsNoiseNorm S' ≤ 3 * Real.sqrt (N : ℝ))
    (hd : (N : ℝ) / 4 ≤ olsCenteredDesign S)
    (hd' : (N : ℝ) / 4 ≤ olsCenteredDesign S') (u : ℝ) :
    |olsNoisePredictor S u - olsNoisePredictor S' u| ≤
      6000 * (1 + |u|) * olsPairDistance S S' / Real.sqrt (N : ℝ) := by
  let Δ : ℝ := olsPairDistance S S'
  have hΔ : 0 ≤ Δ := Real.sqrt_nonneg _
  have hqDiff := ols_noiseSlope_pairwise_bound hN hr S S' hS hS' hd hd'
  have hq : |olsNoiseSlope S| ≤ 6 := ols_noiseSlope_abs_le hN hr S hS hd
  have hq' : |olsNoiseSlope S'| ≤ 6 := ols_noiseSlope_abs_le hN hr S' hS' hd'
  have hx : |olsXBar S| ≤ 5 := olsXBar_abs_le_five hN hr hNr S hS
  have heDiff : |olsEBar S - olsEBar S'| ≤ 2 * Δ / Real.sqrt (N : ℝ) := by
    simpa [Δ] using olsEBar_difference_bound hN hr hNr S S'
  have hxDiff : |olsXBar S - olsXBar S'| ≤ 2 * Δ / Real.sqrt (N : ℝ) := by
    simpa [Δ] using olsXBar_difference_bound hN hr hNr S S'
  have hxu : |u - olsXBar S| ≤ |u| + 5 := by
    calc
      _ ≤ |u| + |olsXBar S| := by
        simpa only [sub_eq_add_neg, abs_neg] using abs_add_le u (-olsXBar S)
      _ = |olsXBar S| + |u| := by ring
      _ ≤ 5 + |u| := by nlinarith only [hx]
      _ = |u| + 5 := by ring
  have hqTerm :
      |(olsNoiseSlope S - olsNoiseSlope S') * (u - olsXBar S)| ≤
        (888 * Δ / Real.sqrt (N : ℝ)) * (|u| + 5) := by
    rw [abs_mul]
    exact mul_le_mul hqDiff hxu (abs_nonneg _) (by positivity)
  have hq'Term :
      |olsNoiseSlope S' * (olsXBar S' - olsXBar S)| ≤
        6 * (2 * Δ / Real.sqrt (N : ℝ)) := by
    rw [abs_mul]
    have hxDiff' : |olsXBar S' - olsXBar S| ≤
        2 * Δ / Real.sqrt (N : ℝ) := by simpa [abs_sub_comm] using hxDiff
    exact mul_le_mul hq' hxDiff' (abs_nonneg _) (by positivity)
  have hfac : 0 ≤ Δ / Real.sqrt (N : ℝ) := by positivity
  have hcoeff : 2 + 888 * (|u| + 5) + 12 ≤ 6000 * (1 + |u|) := by
    have hu : 0 ≤ |u| := abs_nonneg u
    nlinarith only [hu]
  have hpredIdentity : olsNoisePredictor S u - olsNoisePredictor S' u =
      (olsEBar S - olsEBar S') +
        (olsNoiseSlope S - olsNoiseSlope S') * (u - olsXBar S) +
        olsNoiseSlope S' * (olsXBar S' - olsXBar S) := by
    unfold olsNoisePredictor
    ring
  have htri :
      |(olsEBar S - olsEBar S') +
          (olsNoiseSlope S - olsNoiseSlope S') * (u - olsXBar S) +
          olsNoiseSlope S' * (olsXBar S' - olsXBar S)| ≤
        |olsEBar S - olsEBar S'| +
          |(olsNoiseSlope S - olsNoiseSlope S') * (u - olsXBar S)| +
          |olsNoiseSlope S' * (olsXBar S' - olsXBar S)| := by
    calc
      _ ≤ |(olsEBar S - olsEBar S') +
          (olsNoiseSlope S - olsNoiseSlope S') * (u - olsXBar S)| +
            |olsNoiseSlope S' * (olsXBar S' - olsXBar S)| := abs_add_le _ _
      _ ≤ (|olsEBar S - olsEBar S'| +
            |(olsNoiseSlope S - olsNoiseSlope S') * (u - olsXBar S)|) +
            |olsNoiseSlope S' * (olsXBar S' - olsXBar S)| := by
          have hab := abs_add_le (olsEBar S - olsEBar S')
            ((olsNoiseSlope S - olsNoiseSlope S') * (u - olsXBar S))
          nlinarith only [hab]
  calc
    |olsNoisePredictor S u - olsNoisePredictor S' u| ≤
        |olsEBar S - olsEBar S'| +
          |(olsNoiseSlope S - olsNoiseSlope S') * (u - olsXBar S)| +
          |olsNoiseSlope S' * (olsXBar S' - olsXBar S)| := by
      rw [hpredIdentity]
      exact htri
    _ ≤ 2 * Δ / Real.sqrt (N : ℝ) +
          (888 * Δ / Real.sqrt (N : ℝ)) * (|u| + 5) +
          6 * (2 * Δ / Real.sqrt (N : ℝ)) := by
      exact add_le_add (add_le_add heDiff hqTerm) hq'Term
    _ = (2 + 888 * (|u| + 5) + 12) * (Δ / Real.sqrt (N : ℝ)) := by ring
    _ ≤ 6000 * (1 + |u|) * (Δ / Real.sqrt (N : ℝ)) :=
      mul_le_mul_of_nonneg_right hcoeff hfac
    _ = 6000 * (1 + |u|) * Δ / Real.sqrt (N : ℝ) := by ring

theorem ols_goodSet_noisePredictor_pairwise {n : ℕ}
    (hn : 192 ≤ n + 2) (S S' : Fin (n + 2) → ℝ × ℝ)
    (hS : S ∈ olsGoodSet n) (hS' : S' ∈ olsGoodSet n) (u : ℝ) :
    |olsNoisePredictor S u - olsNoisePredictor S' u| ≤
      6000 * (1 + |u|) * olsPairDistance S S' / Real.sqrt (n + 2 : ℝ) := by
  have hN : 0 < n + 2 := by omega
  have hNr : ((n + 2 : ℕ) : ℝ) ≤ 2 * ((n + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show n + 2 ≤ 2 * (n + 2) by omega)
  have hNrCast : ((n + 2 : ℕ) : ℝ) ≤ 2 * ((n + 2 : ℕ) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hNr
  have hD : (n + 2 : ℝ) / 4 ≤ olsCenteredDesign S := by
    have hNnonneg : 0 ≤ (n + 2 : ℝ) := by positivity
    exact (by nlinarith only [hNnonneg] :
      (n + 2 : ℝ) / 4 ≤ (n + 2 : ℝ) / 2).trans hS.2.1
  have hD' : (n + 2 : ℝ) / 4 ≤ olsCenteredDesign S' := by
    have hNnonneg : 0 ≤ (n + 2 : ℝ) := by positivity
    exact (by nlinarith only [hNnonneg] :
      (n + 2 : ℝ) / 4 ≤ (n + 2 : ℝ) / 2).trans hS'.2.1
  have hSnorm : olsNoiseNorm S ≤ 3 * Real.sqrt ((n + 2 : ℕ) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hS.1
  have hS'norm : olsNoiseNorm S' ≤ 3 * Real.sqrt ((n + 2 : ℕ) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hS'.1
  have hDcast : ((n + 2 : ℕ) : ℝ) / 4 ≤ olsCenteredDesign S := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hD
  have hD'cast : ((n + 2 : ℕ) : ℝ) / 4 ≤ olsCenteredDesign S' := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hD'
  have hpair := ols_noisePredictor_pairwise_bound (N := n + 2) (r := n + 2)
    hN (by omega) hNrCast S S' hSnorm hS'norm hDcast hD'cast u
  simpa using hpair

theorem ols_deletedGoodSet_noisePredictor_pairwise {n : ℕ}
    (hn : 192 ≤ n + 2) (S S' : Fin (n + 2) → ℝ × ℝ)
    (hS : S ∈ olsGoodSet n) (hS' : S' ∈ olsGoodSet n)
    (i : Fin (n + 2)) (u : ℝ) :
    |olsNoisePredictor (deleteAt S i) u - olsNoisePredictor (deleteAt S' i) u| ≤
      6000 * (1 + |u|) * olsPairDistance S S' / Real.sqrt (n + 2 : ℝ) := by
  have hN : 0 < n + 2 := by omega
  have hnorm : olsNoiseNorm (deleteAt S i) ≤ 3 * Real.sqrt (n + 2 : ℝ) :=
    (ols_deletedNoiseNorm_le S i).trans hS.1
  have hnorm' : olsNoiseNorm (deleteAt S' i) ≤ 3 * Real.sqrt (n + 2 : ℝ) :=
    (ols_deletedNoiseNorm_le S' i).trans hS'.1
  have hdesign := ols_deletedCenteredDesign_lower_bound hn S hS i
  have hdesign' := ols_deletedCenteredDesign_lower_bound hn S' hS' i
  have hdistDel :
      olsPairDistance (deleteAt S i) (deleteAt S' i) ≤ olsPairDistance S S' := by
    unfold olsPairDistance
    have heq : (fun j => deleteAt S i j - deleteAt S' i j) =
        deleteAt (fun j => S j - S' j) i := by
      funext j
      rfl
    rw [heq]
    exact ols_deletedNoiseNorm_le (fun j => S j - S' j) i
  have hNr : ((n + 2 : ℕ) : ℝ) ≤ 2 * ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show n + 2 ≤ 2 * (n + 1) by omega)
  have hNrCast : ((n + 2 : ℕ) : ℝ) ≤ 2 * ((n + 1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hNr
  have hnormCast : olsNoiseNorm (deleteAt S i) ≤
      3 * Real.sqrt ((n + 2 : ℕ) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hnorm
  have hnorm'Cast : olsNoiseNorm (deleteAt S' i) ≤
      3 * Real.sqrt ((n + 2 : ℕ) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hnorm'
  have hdesignCast : ((n + 2 : ℕ) : ℝ) / 4 ≤ olsCenteredDesign (deleteAt S i) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hdesign
  have hdesign'Cast : ((n + 2 : ℕ) : ℝ) / 4 ≤ olsCenteredDesign (deleteAt S' i) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hdesign'
  have hpair := ols_noisePredictor_pairwise_bound (N := n + 2) (r := n + 1)
    hN (by omega) hNrCast (deleteAt S i) (deleteAt S' i)
    hnormCast hnorm'Cast hdesignCast hdesign'Cast u
  have hpair' :
      |olsNoisePredictor (deleteAt S i) u - olsNoisePredictor (deleteAt S' i) u| ≤
        6000 * (1 + |u|) *
          olsPairDistance (deleteAt S i) (deleteAt S' i) / Real.sqrt (n + 2 : ℝ) := by
    simpa using hpair
  have hcoef : 0 ≤ 6000 * (1 + |u|) / Real.sqrt (n + 2 : ℝ) := by positivity
  calc
    _ ≤ 6000 * (1 + |u|) *
          olsPairDistance (deleteAt S i) (deleteAt S' i) /
          Real.sqrt (n + 2 : ℝ) := hpair'
    _ = (6000 * (1 + |u|) / Real.sqrt (n + 2 : ℝ)) *
          olsPairDistance (deleteAt S i) (deleteAt S' i) := by ring
    _ ≤ (6000 * (1 + |u|) / Real.sqrt (n + 2 : ℝ)) *
          olsPairDistance S S' := mul_le_mul_of_nonneg_left hdistDel hcoef
    _ = 6000 * (1 + |u|) * olsPairDistance S S' /
          Real.sqrt (n + 2 : ℝ) := by ring

end LOOConcentration
