import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

/-!
Coordinate derivative of the empirical feature variance in the stabilized
regression source. This is an analytic ingredient for the ridge calculation;
it does not state the full estimator gradient.
-/

namespace LOOConcentrationManuscript.Internal

private noncomputable abbrev normalizedMean {N : ℕ} (X : Fin N → ℝ) : ℝ :=
  (∑ i, X i) * (N : ℝ)⁻¹

private noncomputable abbrev normalizedVariance {N : ℕ} (X : Fin N → ℝ) : ℝ :=
  (∑ i, (X i - normalizedMean X) ^ 2) * (N : ℝ)⁻¹

private theorem centered_sum_eq_zero {N : ℕ} (hN : 0 < N) (X : Fin N → ℝ) :
    ∑ i, (X i - normalizedMean X) = 0 := by
  have hconst : ∑ _i : Fin N, normalizedMean X = (N : ℝ) * normalizedMean X := by
    simp
  rw [Finset.sum_sub_distrib, hconst, normalizedMean]
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  field_simp [hN0]
  ring

set_option linter.style.haveILetI false in
private theorem square_hasDerivAt {f : ℝ → ℝ} {f' x : ℝ}
    (h : HasDerivAt f f' x) :
    HasDerivAt (fun t : ℝ => f t ^ 2) (2 * f x * f') x := by
  have hslopeSq : Filter.Tendsto (slope (fun t : ℝ => f t ^ 2) x)
      (nhdsWithin x {x}ᶜ) (nhds (2 * f x * f')) := by
    letI : NormedSpace ℝ ℝ := NormedAlgebra.toNormedSpace ℝ
    have hAlgebra : HasDerivAt f f' x :=
      (hasDerivAt_iff_tendsto_slope).2 h.tendsto_slope
    have hsquare : HasDerivAt (fun t : ℝ => f t ^ 2) (2 * f x * f') x := by
      simpa [pow_one, mul_assoc] using
        (hAlgebra.pow 2).congr_of_eventuallyEq (by filter_upwards with t; rfl)
    exact hsquare.tendsto_slope
  exact (hasDerivAt_iff_tendsto_slope).2 hslopeSq

private theorem updatedCoordinate_hasDerivAt {N : ℕ} (X : Fin N → ℝ)
    (j i : Fin N) :
    HasDerivAt (fun s : ℝ => Function.update X j s i)
      (if i = j then 1 else 0) (X j) := by
  by_cases hij : i = j
  · subst i
    simpa [Function.update_self] using (hasDerivAt_id' (X j))
  · have hji : j ≠ i := Ne.symm hij
    simpa [hji, hij] using (hasDerivAt_const (X j) (X i))

private theorem updatedMean_hasDerivAt {N : ℕ} (_hN : 0 < N)
    (X : Fin N → ℝ) (j : Fin N) :
    HasDerivAt (fun s : ℝ => normalizedMean (Function.update X j s))
      ((N : ℝ)⁻¹) (X j) := by
  let nInv : ℝ := (N : ℝ)⁻¹
  have hsum : HasDerivAt (fun s : ℝ => ∑ i, Function.update X j s i)
      1 (X j) := by
    have hraw := HasDerivAt.fun_sum (u := Finset.univ)
      (fun i _ => updatedCoordinate_hasDerivAt X j i)
    have hselect : ∑ i : Fin N, (if i = j then 1 else 0 : ℝ) = 1 := by
      simp
    simpa [hselect] using hraw
  have hmean := hsum.hasFDerivAt.mul_const nInv |>.hasDerivAt
  have hmean_eq : (fun s : ℝ => normalizedMean (Function.update X j s)) =
      (fun s => (∑ i, Function.update X j s i) * nInv) := by
    funext s
    rfl
  rw [hmean_eq]
  simpa [nInv] using hmean

private theorem normalizedVariance_update_hasDerivAt {N : ℕ} (hN : 0 < N)
    (X : Fin N → ℝ) (j : Fin N) :
    HasDerivAt (fun s : ℝ => normalizedVariance (Function.update X j s))
      (2 * (X j - normalizedMean X) * (N : ℝ)⁻¹) (X j) := by
  let nInv : ℝ := (N : ℝ)⁻¹
  have hmean := updatedMean_hasDerivAt hN X j
  have hterms : ∀ i : Fin N,
      HasDerivAt
        (fun s : ℝ =>
          (Function.update X j s i - normalizedMean (Function.update X j s)) ^ 2)
        (2 * (X i - normalizedMean X) * ((if i = j then 1 else 0) - nInv))
        (X j) := by
    intro i
    have hcentered : HasDerivAt
        (fun s : ℝ =>
          Function.update X j s i - normalizedMean (Function.update X j s))
        ((if i = j then 1 else 0) - nInv) (X j) := by
      exact ((updatedCoordinate_hasDerivAt X j i).sub hmean).congr_of_eventuallyEq
        (by filter_upwards with s; rfl)
    have hsquare := square_hasDerivAt hcentered
    simpa [normalizedMean, nInv, pow_one, mul_comm, mul_left_comm, mul_assoc] using hsquare
  have hsum : HasDerivAt
      (fun s : ℝ =>
        ∑ i, (Function.update X j s i - normalizedMean (Function.update X j s)) ^ 2)
      (∑ i, 2 * (X i - normalizedMean X) * ((if i = j then 1 else 0) - nInv))
      (X j) := by
    exact HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hterms i)
  have hcentered := centered_sum_eq_zero hN X
  have hselected :
      (∑ i : Fin N, 2 * (X i - normalizedMean X) * (if i = j then 1 else 0)) =
        2 * (X j - normalizedMean X) := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [hij]
    · simp
  have hderiv_sum :
      (∑ i : Fin N, 2 * (X i - normalizedMean X) *
        ((if i = j then 1 else 0) - nInv)) = 2 * (X j - normalizedMean X) := by
    calc
      _ = (∑ i : Fin N, 2 * (X i - normalizedMean X) *
          (if i = j then 1 else 0)) -
          2 * nInv * ∑ i : Fin N, (X i - normalizedMean X) := by
            calc
              _ = ∑ i : Fin N,
                  (2 * (X i - normalizedMean X) * (if i = j then 1 else 0) -
                    2 * (X i - normalizedMean X) * nInv) := by
                      apply Finset.sum_congr rfl
                      intro i _
                      ring
              _ = (∑ i : Fin N, 2 * (X i - normalizedMean X) *
                    (if i = j then 1 else 0)) -
                  ∑ i : Fin N, 2 * (X i - normalizedMean X) * nInv := by
                    rw [Finset.sum_sub_distrib]
              _ = _ := by
                    have hfactor :
                        (∑ i : Fin N, 2 * (X i - normalizedMean X) * nInv) =
                          (2 * nInv) * ∑ i : Fin N, (X i - normalizedMean X) := by
                      calc
                        _ = ∑ i : Fin N, (2 * nInv) * (X i - normalizedMean X) := by
                          apply Finset.sum_congr rfl
                          intro i _
                          ring
                        _ = _ := by rw [Finset.mul_sum]
                    rw [hfactor]
      _ = 2 * (X j - normalizedMean X) := by rw [hselected, hcentered]; ring
  have hscaled := hsum.mul_const nInv
  have hvariance_eq :
      (fun s : ℝ => normalizedVariance (Function.update X j s)) =
        (fun s => (∑ i,
          (Function.update X j s i - normalizedMean (Function.update X j s)) ^ 2) * nInv) := by
    funext s
    rfl
  have hvariance : HasDerivAt
      (fun s : ℝ => normalizedVariance (Function.update X j s))
      ((∑ i, 2 * (X i - normalizedMean X) *
        ((if i = j then 1 else 0) - nInv)) * nInv) (X j) := by
    rw [hvariance_eq]
    exact hscaled
  rw [hderiv_sum] at hvariance
  simpa [nInv, mul_comm, mul_left_comm, mul_assoc] using hvariance

/-- The literal empirical variance of an updated feature vector has the
source-coordinate derivative at the original feature value. The positive
sample-size premise is part of the source-facing statement. -/
theorem coordinateUpdatedVariance_hasDerivAt {N : ℕ} (hN : 0 < N)
    (X : Fin N → ℝ) (j : Fin N) :
    HasDerivAt
      (fun t : ℝ =>
        (∑ i : Fin N,
          (Function.update X j t i -
            (∑ k : Fin N, Function.update X j t k) * (N : ℝ)⁻¹) ^ 2) *
          (N : ℝ)⁻¹)
      (2 * (X j - (∑ k : Fin N, X k) * (N : ℝ)⁻¹) * (N : ℝ)⁻¹)
      (X j) := by
  simpa [normalizedVariance, normalizedMean] using
    normalizedVariance_update_hasDerivAt hN X j

end LOOConcentrationManuscript.Internal
