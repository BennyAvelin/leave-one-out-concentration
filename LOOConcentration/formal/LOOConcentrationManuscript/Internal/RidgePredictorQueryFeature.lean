import LOOConcentrationManuscript.Internal.RidgeSlopeFeatureDerivative
import LOOConcentrationManuscript.Internal.RidgeSlopeBound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

/-!
Actual query and feature-coordinate calculations for the manuscript's
stabilized ridge predictor.  The predictor is kept literal in each theorem:
its intercept is the raw response mean and its slope uses clipped responses.
-/

namespace LOOConcentrationManuscript.Internal

/-- The actual source predictor has query derivative equal to its ridge slope;
the same accepted finite-sample bound controls that derivative uniformly. -/
theorem ridgePredictor_actual_query_derivative_and_slope_bound (r : ℕ)
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1))
    (b δ : ℝ) (hb : 0 < b) (hδ : 0 < δ) :
    let N : ℝ := ((r + 1 : ℕ) : ℝ)
    let X := LOOConcentrationManuscript.featureValues D
    let U := LOOConcentrationManuscript.clippedResponseValues D b
    let a : ℝ := (∑ i : Fin (r + 1), X i) / N
    let c : ℝ := (∑ i : Fin (r + 1), U i) / N
    let d : ℝ := (∑ i : Fin (r + 1), (D i).2 0) * N⁻¹
    let v : ℝ := (∑ i : Fin (r + 1), (X i - a) ^ 2) / N
    let s : ℝ := (∑ i : Fin (r + 1), (X i - a) * (U i - c)) / N
    let beta : ℝ := s / (v + δ)
    let T := fun x : ℝ => d + beta * (x - a)
    ∀ x : ℝ, HasDerivAt T beta x ∧ |beta| ≤ b / (2 * Real.sqrt δ) := by
  classical
  let N : ℝ := ((r + 1 : ℕ) : ℝ)
  let X := LOOConcentrationManuscript.featureValues D
  let U := LOOConcentrationManuscript.clippedResponseValues D b
  let a : ℝ := (∑ i : Fin (r + 1), X i) / N
  let c : ℝ := (∑ i : Fin (r + 1), U i) / N
  let d : ℝ := (∑ i : Fin (r + 1), (D i).2 0) * N⁻¹
  let v : ℝ := (∑ i : Fin (r + 1), (X i - a) ^ 2) / N
  let s : ℝ := (∑ i : Fin (r + 1), (X i - a) * (U i - c)) / N
  let beta : ℝ := s / (v + δ)
  let T := fun x : ℝ => d + beta * (x - a)
  change ∀ z : ℝ, HasDerivAt T beta z ∧ |beta| ≤ b / (2 * Real.sqrt δ)
  have hbound := LOOConcentration.Manuscript.Internal.clippedDataset_covariance_and_ridgeSlope_bound
    r D b δ hb.le hδ
  have hslope : |beta| ≤ b / (2 * Real.sqrt δ) := by
    simpa [X, U, a, c, v, s, beta, N,
      LOOConcentrationManuscript.featureValues,
      LOOConcentrationManuscript.clippedResponseValues,
      Nat.cast_add, Nat.cast_one] using hbound.2.2
  intro x
  constructor
  · change HasDerivAt (fun z : ℝ => d + beta * (z - a)) beta x
    have hlinear : HasDerivAt (fun z : ℝ => beta * z + (d - beta * a)) beta x := by
      simpa using
        ((hasDerivAt_id x).const_mul beta).add_const (d - beta * a)
    exact hlinear.congr_of_eventuallyEq (by
      filter_upwards with z
      ring)
  · exact hslope

/-- The actual source predictor is globally query-Lipschitz, with the bound
depending only on the fixed clipping and stabilization parameters. -/
theorem ridgePredictor_actual_query_lipschitz (r : ℕ)
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1))
    (b δ : ℝ) (hb : 0 < b) (hδ : 0 < δ) :
    let N : ℝ := ((r + 1 : ℕ) : ℝ)
    let X := LOOConcentrationManuscript.featureValues D
    let U := LOOConcentrationManuscript.clippedResponseValues D b
    let a : ℝ := (∑ i : Fin (r + 1), X i) * N⁻¹
    let c : ℝ := (∑ i : Fin (r + 1), U i) * N⁻¹
    let d : ℝ := (∑ i : Fin (r + 1), (D i).2 0) * N⁻¹
    let v : ℝ := (∑ i : Fin (r + 1), (X i - a) ^ 2) * N⁻¹
    let s : ℝ := (∑ i : Fin (r + 1), (X i - a) * (U i - c)) * N⁻¹
    let beta : ℝ := s / (v + δ)
    let T := fun x : ℝ => d + beta * (x - a)
    ∀ x x' : ℝ, |T x - T x'| ≤ b / (2 * Real.sqrt δ) * |x - x'| := by
  classical
  let N : ℝ := ((r + 1 : ℕ) : ℝ)
  let X := LOOConcentrationManuscript.featureValues D
  let U := LOOConcentrationManuscript.clippedResponseValues D b
  let a : ℝ := (∑ i : Fin (r + 1), X i) * N⁻¹
  let c : ℝ := (∑ i : Fin (r + 1), U i) * N⁻¹
  let d : ℝ := (∑ i : Fin (r + 1), (D i).2 0) * N⁻¹
  let v : ℝ := (∑ i : Fin (r + 1), (X i - a) ^ 2) * N⁻¹
  let s : ℝ := (∑ i : Fin (r + 1), (X i - a) * (U i - c)) * N⁻¹
  let beta : ℝ := s / (v + δ)
  let T := fun x : ℝ => d + beta * (x - a)
  change ∀ z z' : ℝ, |T z - T z'| ≤ b / (2 * Real.sqrt δ) * |z - z'|
  intro x x'
  have hregular := ridgePredictor_actual_query_derivative_and_slope_bound
    r D b δ hb hδ
  change ∀ z : ℝ, HasDerivAt T beta z ∧
      |beta| ≤ b / (2 * Real.sqrt δ) at hregular
  have hregular' : ∀ z : ℝ, HasDerivAt T beta z ∧
      |beta| ≤ b / (2 * Real.sqrt δ) := by
    exact hregular
  have hbeta : |beta| ≤ b / (2 * Real.sqrt δ) := by
    exact (hregular' x).2
  calc
    |T x - T x'| = |beta| * |x - x'| := by
      dsimp [T]
      rw [show d + beta * (x - a) - (d + beta * (x' - a)) = beta * (x - x') by ring,
        abs_mul]
    _ ≤ (b / (2 * Real.sqrt δ)) * |x - x'| :=
      mul_le_mul_of_nonneg_right hbeta (abs_nonneg _)

private theorem ridge_update_coordinate_hasDerivAt {N : ℕ}
    (X : Fin N → ℝ) (j i : Fin N) :
    HasDerivAt (fun t : ℝ => Function.update X j t i)
      (if i = j then 1 else 0) (X j) := by
  by_cases hij : i = j
  · subst i
    simpa [Function.update_self] using (hasDerivAt_id' (X j))
  · have hji : j ≠ i := Ne.symm hij
    simpa [hji, hij] using (hasDerivAt_const (X j) (X i))

private theorem ridge_update_mean_hasDerivAt {N : ℕ} (_hN : 0 < N)
    (X : Fin N → ℝ) (j : Fin N) :
    HasDerivAt (fun t : ℝ => (∑ i : Fin N, Function.update X j t i) * (N : ℝ)⁻¹)
      ((N : ℝ)⁻¹) (X j) := by
  let nInv : ℝ := (N : ℝ)⁻¹
  have hsum : HasDerivAt (fun t : ℝ => ∑ i : Fin N, Function.update X j t i)
      1 (X j) := by
    have hraw := HasDerivAt.fun_sum (u := Finset.univ)
      (fun i _ => ridge_update_coordinate_hasDerivAt X j i)
    have hselect : ∑ i : Fin N, (if i = j then 1 else 0 : ℝ) = 1 := by simp
    simpa [hselect] using hraw
  have hmean := hsum.hasFDerivAt.mul_const nInv |>.hasDerivAt
  simpa [nInv] using hmean

private theorem ridge_featureValues_varyFeature {N : ℕ}
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) N)
    (j : Fin N) (t : ℝ) :
    LOOConcentrationManuscript.featureValues
      (LOOConcentrationManuscript.varyFeature D j t) =
      Function.update (LOOConcentrationManuscript.featureValues D) j t := by
  funext i
  by_cases hij : i = j
  · subst i
    simp [LOOConcentrationManuscript.featureValues,
      LOOConcentrationManuscript.varyFeature]
  · dsimp [LOOConcentrationManuscript.featureValues,
      LOOConcentrationManuscript.varyFeature]
    rw [Function.update_of_ne hij, Function.update_of_ne hij]
    rfl

private theorem ridge_clippedResponses_varyFeature {N : ℕ}
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) N)
    (j : Fin N) (t b : ℝ) :
    LOOConcentrationManuscript.clippedResponseValues
      (LOOConcentrationManuscript.varyFeature D j t) b =
      LOOConcentrationManuscript.clippedResponseValues D b := by
  funext i
  by_cases hij : i = j
  · subst i
    simp [LOOConcentrationManuscript.clippedResponseValues,
      LOOConcentrationManuscript.varyFeature]
  · dsimp [LOOConcentrationManuscript.clippedResponseValues,
      LOOConcentrationManuscript.varyFeature]
    rw [Function.update_of_ne hij]

private theorem ridge_responseValues_varyFeature {N : ℕ}
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) N)
    (j : Fin N) (t : ℝ) :
    (fun i : Fin N => (LOOConcentrationManuscript.varyFeature D j t i).2 0) =
      (fun i : Fin N => (D i).2 0) := by
  funext i
  by_cases hij : i = j
  · subst i
    simp [LOOConcentrationManuscript.varyFeature]
  · simp [LOOConcentrationManuscript.varyFeature, hij]

/-- Actual feature-coordinate derivative of the full stabilized ridge
predictor. Varying a feature leaves every raw and clipped response fixed. -/
theorem ridgePredictor_actual_feature_hasDerivAt (r : ℕ)
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1))
    (j : Fin (r + 1)) (b δ x : ℝ) (_hb : 0 < b) (hδ : 0 < δ) :
    let N : ℝ := ((r + 1 : ℕ) : ℝ)
    let X := LOOConcentrationManuscript.featureValues D
    let U := LOOConcentrationManuscript.clippedResponseValues D b
    let a : ℝ := (∑ i : Fin (r + 1), X i) * N⁻¹
    let c : ℝ := (∑ i : Fin (r + 1), U i) * N⁻¹
    let v : ℝ := (∑ i : Fin (r + 1), (X i - a) ^ 2) * N⁻¹
    let s : ℝ := (∑ i : Fin (r + 1), (X i - a) * (U i - c)) * N⁻¹
    let beta : ℝ := s / (v + δ)
    HasDerivAt
      (fun t : ℝ =>
        let Dt := LOOConcentrationManuscript.varyFeature D j t
        let Xt := LOOConcentrationManuscript.featureValues Dt
        let Ut := LOOConcentrationManuscript.clippedResponseValues Dt b
        let aT := (∑ i : Fin (r + 1), Xt i) * N⁻¹
        let ct := (∑ i : Fin (r + 1), Ut i) * N⁻¹
        let vt := (∑ i : Fin (r + 1), (Xt i - aT) ^ 2) * N⁻¹
        let st := (∑ i : Fin (r + 1), (Xt i - aT) * (Ut i - ct)) * N⁻¹
        (∑ i : Fin (r + 1), (Dt i).2 0) * N⁻¹ +
          (st / (vt + δ)) * (x - aT))
      ((x - a) * (U j - c - 2 * beta * (X j - a)) /
          (N * (v + δ)) - beta / N)
      (X j) := by
  classical
  let N : ℝ := ((r + 1 : ℕ) : ℝ)
  let X := LOOConcentrationManuscript.featureValues D
  let U := LOOConcentrationManuscript.clippedResponseValues D b
  let a : ℝ := (∑ i : Fin (r + 1), X i) * N⁻¹
  let c : ℝ := (∑ i : Fin (r + 1), U i) * N⁻¹
  let d : ℝ := (∑ i : Fin (r + 1), (D i).2 0) * N⁻¹
  let v : ℝ := (∑ i : Fin (r + 1), (X i - a) ^ 2) * N⁻¹
  let s : ℝ := (∑ i : Fin (r + 1), (X i - a) * (U i - c)) * N⁻¹
  let beta : ℝ := s / (v + δ)
  let A : ℝ → ℝ := fun t => (∑ i : Fin (r + 1), Function.update X j t i) * N⁻¹
  let B : ℝ → ℝ := fun t =>
    let Dt := LOOConcentrationManuscript.varyFeature D j t
    let Xt := LOOConcentrationManuscript.featureValues Dt
    let Ut := LOOConcentrationManuscript.clippedResponseValues Dt b
    let aT := (∑ i : Fin (r + 1), Xt i) * N⁻¹
    let cT := (∑ i : Fin (r + 1), Ut i) * N⁻¹
    let vT := (∑ i : Fin (r + 1), (Xt i - aT) ^ 2) * N⁻¹
    let sT := (∑ i : Fin (r + 1), (Xt i - aT) * (Ut i - cT)) * N⁻¹
    sT / (vT + δ)
  let Q : ℝ → ℝ := fun t =>
    let Dt := LOOConcentrationManuscript.varyFeature D j t
    let Xt := LOOConcentrationManuscript.featureValues Dt
    let Ut := LOOConcentrationManuscript.clippedResponseValues Dt b
    let aT := (∑ i : Fin (r + 1), Xt i) * N⁻¹
    let ct := (∑ i : Fin (r + 1), Ut i) * N⁻¹
    let vt := (∑ i : Fin (r + 1), (Xt i - aT) ^ 2) * N⁻¹
    let st := (∑ i : Fin (r + 1), (Xt i - aT) * (Ut i - ct)) * N⁻¹
    (∑ i : Fin (r + 1), (Dt i).2 0) * N⁻¹ + (st / (vt + δ)) * (x - aT)
  change HasDerivAt Q
    ((x - a) * (U j - c - 2 * beta * (X j - a)) / (N * (v + δ)) - beta / N)
    (X j)
  have hXupdate (t : ℝ) :
      LOOConcentrationManuscript.featureValues
        (LOOConcentrationManuscript.varyFeature D j t) = Function.update X j t :=
    ridge_featureValues_varyFeature D j t
  have hUfixed (t : ℝ) :
      LOOConcentrationManuscript.clippedResponseValues
        (LOOConcentrationManuscript.varyFeature D j t) b = U :=
    ridge_clippedResponses_varyFeature D j t b
  have hYfixed (t : ℝ) :
      (fun i : Fin (r + 1) =>
        (LOOConcentrationManuscript.varyFeature D j t i).2 0) =
        (fun i : Fin (r + 1) => (D i).2 0) :=
    ridge_responseValues_varyFeature D j t
  have hB : HasDerivAt B
      ((U j - c - 2 * beta * (X j - a)) / (N * (v + δ))) (X j) := by
    simpa [B, X, U, a, c, v, s, beta, N] using
      LOOConcentration.Manuscript.Internal.clippedDataset_ridgeSlope_feature_hasDerivAt
        r D j b δ hδ
  have hA : HasDerivAt A N⁻¹ (X j) := by
    simpa [A, N, X] using ridge_update_mean_hasDerivAt (by
      positivity) (LOOConcentrationManuscript.featureValues D) j
  have hupdate0 : Function.update X j (X j) = X := by
    funext i
    by_cases hij : i = j
    · subst i
      simp
    · simp [Function.update_of_ne hij]
  have hD0 : LOOConcentrationManuscript.varyFeature D j (X j) = D := by
    funext i
    by_cases hij : i = j
    · subst i
      simp [X, LOOConcentrationManuscript.featureValues,
        LOOConcentrationManuscript.varyFeature]
    · simp [LOOConcentrationManuscript.varyFeature, hij]
  have hA0 : A (X j) = a := by
    change (∑ i : Fin (r + 1), Function.update X j (X j) i) * N⁻¹ =
      (∑ i : Fin (r + 1), X i) * N⁻¹
    rw [hupdate0]
  have hB0 : B (X j) = beta := by
    dsimp [B]
    rw [hD0]
  have hQ : Q = fun t : ℝ => d + B t * (x - A t) := by
    funext t
    dsimp [Q, A, B]
    rw [hXupdate t, hUfixed t, hYfixed t]
  rw [hQ]
  have hdiff : HasDerivAt (fun t : ℝ => x - A t) (-N⁻¹) (X j) := by
    have hneg := hA.neg.add_const x
    exact hneg.congr_of_eventuallyEq (by
      filter_upwards with t
      simp only [Pi.neg_apply]
      ring)
  have hprod := hB.mul hdiff
  have hsum := hprod.add_const d
  have hsum' : HasDerivAt (fun t : ℝ => d + B t * (x - A t))
      ((U j - c - 2 * beta * (X j - a)) / (N * (v + δ)) *
        (x - A (X j)) + B (X j) * -N⁻¹) (X j) := by
    exact hsum.congr_of_eventuallyEq (by
      filter_upwards with t
      simpa only [Pi.mul_apply] using (add_comm d (B t * (x - A t))))
  have hcoeff :
      (U j - c - 2 * beta * (X j - a)) / (N * (v + δ)) *
        (x - A (X j)) + B (X j) * -N⁻¹ =
      (x - a) * (U j - c - 2 * beta * (X j - a)) /
        (N * (v + δ)) - beta / N := by
    rw [hA0, hB0]
    dsimp [N]
    ring
  rw [hcoeff] at hsum'
  exact hsum'

end LOOConcentrationManuscript.Internal
