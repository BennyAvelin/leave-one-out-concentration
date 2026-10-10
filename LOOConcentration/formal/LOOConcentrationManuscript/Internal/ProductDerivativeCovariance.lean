import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

/-!
The product-rule derivative of the empirical centered covariance when one
feature coordinate varies and the response vector is fixed.
-/

namespace LOOConcentrationManuscript.Internal

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- Generic algebraic normalized sum `(∑ i, X i) * N⁻¹`, for any natural `N`.
This implementation abbreviation has no empirical-mean interpretation at `N = 0`. -/
private noncomputable abbrev normalizedSum {N : ℕ} (X : Fin N → 𝕜) : 𝕜 :=
  (∑ i, X i) * (N : 𝕜)⁻¹

/-- Generic algebraic normalized centered sum for any natural `N`; it is not a
source-object covariance carrier, and at `N = 0` has only its algebraic meaning. -/
private noncomputable abbrev normalizedCenteredCovariance {N : ℕ}
    (X U : Fin N → 𝕜) : 𝕜 :=
  (∑ i, (X i - normalizedSum X) * (U i - normalizedSum U)) * (N : 𝕜)⁻¹

private theorem sum_centered_eq_zero {N : ℕ} [CharZero 𝕜]
    (hN : 0 < N) (U : Fin N → 𝕜) :
    ∑ i, (U i - normalizedSum U) = 0 := by
  have hconst : ∑ _i : Fin N, normalizedSum U = (N : 𝕜) * normalizedSum U := by
    simp
  rw [Finset.sum_sub_distrib, hconst, normalizedSum]
  have hN0 : (N : 𝕜) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  field_simp [hN0]
  ring

private theorem updatedCoordinate_hasDerivAt {N : ℕ} (X : Fin N → 𝕜)
    (j i : Fin N) :
    HasDerivAt (fun s : 𝕜 => Function.update X j s i)
      (if i = j then 1 else 0) (X j) := by
  by_cases hij : i = j
  · subst i
    simpa [Function.update_self] using (hasDerivAt_id' (X j))
  · have hji : j ≠ i := Ne.symm hij
    simpa [hji, hij] using (hasDerivAt_const (X j) (X i))

private theorem updatedMean_hasDerivAt {N : ℕ} (_hN : 0 < N)
    (X : Fin N → 𝕜) (j : Fin N) :
    HasDerivAt (fun s : 𝕜 => normalizedSum (Function.update X j s))
      ((N : 𝕜)⁻¹) (X j) := by
  let nInv : 𝕜 := (N : 𝕜)⁻¹
  have hsum : HasDerivAt (fun s : 𝕜 => ∑ i, Function.update X j s i)
      1 (X j) := by
    have hraw := HasDerivAt.fun_sum (u := Finset.univ)
      (fun i _ => updatedCoordinate_hasDerivAt X j i)
    have hselect : ∑ i : Fin N, (if i = j then 1 else 0 : 𝕜) = 1 := by
      simp
    simpa [hselect] using hraw
  have hmeanF := hsum.hasFDerivAt.mul_const nInv
  have hmean := hmeanF.hasDerivAt
  have hmean_eq : (fun s : 𝕜 => normalizedSum (Function.update X j s)) =
      (fun s => (∑ i, Function.update X j s i) * nInv) := by
    funext s
    rfl
  rw [hmean_eq]
  simpa [nInv] using hmean

/-- Private algebraic product-rule calculation for the generic normalized-sum
implementation abbreviations. -/
private theorem normalizedCenteredCovariance_update_hasDerivAt_aux {N : ℕ} [CharZero 𝕜] (hN : 0 < N)
    (X U : Fin N → 𝕜) (j : Fin N) :
    HasDerivAt (fun s : 𝕜 => normalizedCenteredCovariance (Function.update X j s) U)
      ((U j - normalizedSum U) / (N : 𝕜)) (X j) := by
  let nInv : 𝕜 := (N : 𝕜)⁻¹
  have hmean := updatedMean_hasDerivAt hN X j
  have hterms : ∀ i : Fin N,
      HasDerivAt
        (fun s : 𝕜 =>
          (Function.update X j s i - normalizedSum (Function.update X j s)) *
            (U i - normalizedSum U))
        (((if i = j then 1 else 0) - nInv) * (U i - normalizedSum U)) (X j) := by
    intro i
    have hcentered := (updatedCoordinate_hasDerivAt X j i).sub hmean
    have hproductF := hcentered.hasFDerivAt.mul_const (U i - normalizedSum U)
    have hproduct := hproductF.hasDerivAt
    have hproduct := hproduct.congr_of_eventuallyEq
      (by filter_upwards with s; rfl)
    simpa [nInv, Function.update_self, mul_comm] using hproduct
  have hsum :
      HasDerivAt
        (fun s : 𝕜 =>
          ∑ i, (Function.update X j s i - normalizedSum (Function.update X j s)) *
            (U i - normalizedSum U))
        (∑ i, ((if i = j then 1 else 0) - nInv) * (U i - normalizedSum U)) (X j) := by
    exact HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hterms i)
  have hcentered := sum_centered_eq_zero hN U
  have hselected :
      ∑ i : Fin N, (if i = j then 1 else 0) * (U i - normalizedSum U) =
        U j - normalizedSum U := by
    classical
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [hij]
    · simp
  have hderiv_sum :
      (∑ i : Fin N, ((if i = j then 1 else 0) - nInv) *
        (U i - normalizedSum U)) = U j - normalizedSum U := by
    calc
      _ = ∑ i : Fin N,
          ((if i = j then 1 else 0) * (U i - normalizedSum U) -
            nInv * (U i - normalizedSum U)) := by
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = (∑ i : Fin N, (if i = j then 1 else 0) *
          (U i - normalizedSum U)) -
          ∑ i : Fin N, nInv * (U i - normalizedSum U) := by
            rw [Finset.sum_sub_distrib]
      _ = (∑ i : Fin N, (if i = j then 1 else 0) *
          (U i - normalizedSum U)) -
          nInv * ∑ i : Fin N, (U i - normalizedSum U) := by
            rw [← Finset.mul_sum]
      _ = U j - normalizedSum U := by rw [hselected, hcentered]; ring
  have hcov0 := hsum.mul_const nInv
  have hcov_eq :
      (fun s : 𝕜 => normalizedCenteredCovariance (Function.update X j s) U) =
        (fun s => (∑ i,
          (Function.update X j s i - normalizedSum (Function.update X j s)) *
            (U i - normalizedSum U)) * nInv) := by
    funext s
    rfl
  have hcov : HasDerivAt
      (fun s : 𝕜 => normalizedCenteredCovariance (Function.update X j s) U)
      ((∑ i,
        ((if i = j then 1 else 0) - nInv) * (U i - normalizedSum U)) * nInv)
      (X j) := by
    rw [hcov_eq]
    exact hcov0
  rw [hderiv_sum] at hcov
  simpa [nInv, div_eq_mul_inv, mul_comm] using hcov


/-- Product-rule derivative of the literal finite-sum centered covariance under
one coordinate update. The sums are displayed in the statement so its carrier
and normalization remain explicit; the private normalized-sum abbreviations
have only generic algebraic scope. -/
theorem centeredCovariance_update_hasDerivAt {N : ℕ} [CharZero 𝕜] (hN : 0 < N)
    (X U : Fin N → 𝕜) (j : Fin N) :
    HasDerivAt
      (fun s : 𝕜 =>
        (∑ i : Fin N,
          (Function.update X j s i - (∑ k : Fin N, Function.update X j s k) * (N : 𝕜)⁻¹) *
            (U i - (∑ k : Fin N, U k) * (N : 𝕜)⁻¹)) * (N : 𝕜)⁻¹)
      ((U j - (∑ k : Fin N, U k) * (N : 𝕜)⁻¹) / (N : 𝕜)) (X j) := by
  simpa [normalizedCenteredCovariance, normalizedSum, div_eq_mul_inv] using
    (normalizedCenteredCovariance_update_hasDerivAt_aux hN X U j)

end LOOConcentrationManuscript.Internal
