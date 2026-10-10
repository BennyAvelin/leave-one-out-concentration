import LOOConcentration.Frozen.Foundations.Dataset
import LOOConcentration.Frozen.Foundations.Observation
import LOOConcentrationManuscript.Internal.EuclideanClipping
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

/-!
Finite response-coordinate updates for the manuscript's stabilized scalar
ridge predictor. The intercept is the raw response mean; only the covariance
slope uses clipped responses. This is a finite-difference ingredient, not a
full dataset-gradient estimate.
-/

namespace LOOConcentrationManuscript.Internal

private noncomputable abbrev ridgeMean {N : ℕ} (F : Fin N → ℝ) : ℝ :=
  (∑ i, F i) / (N : ℝ)

private noncomputable abbrev ridgeCovariance {N : ℕ}
    (X U : Fin N → ℝ) : ℝ :=
  (∑ i, (X i - ridgeMean X) * (U i - ridgeMean U)) / (N : ℝ)

private theorem ridge_centered_feature_sum_eq_zero {N : ℕ} (hN : 0 < N)
    (X : Fin N → ℝ) :
    ∑ i, (X i - ridgeMean X) = 0 := by
  rw [Finset.sum_sub_distrib]
  have hconst : ∑ _i : Fin N, ridgeMean X = (N : ℝ) * ridgeMean X := by
    simp
  rw [hconst, ridgeMean]
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  field_simp
  ring

private theorem ridge_covariance_eq_raw_sum {N : ℕ} (hN : 0 < N)
    (X U : Fin N → ℝ) :
    ridgeCovariance X U =
      (∑ i, (X i - ridgeMean X) * U i) / (N : ℝ) := by
  unfold ridgeCovariance
  congr 1
  have hcenter := ridge_centered_feature_sum_eq_zero hN X
  calc
    (∑ i, (X i - ridgeMean X) * (U i - ridgeMean U)) =
        ∑ i, ((X i - ridgeMean X) * U i - (X i - ridgeMean X) * ridgeMean U) := by
          apply Finset.sum_congr rfl
          intro i _hi
          ring
    _ = (∑ i, (X i - ridgeMean X) * U i) -
        (∑ i, (X i - ridgeMean X) * ridgeMean U) := by
          rw [Finset.sum_sub_distrib]
    _ = ∑ i, (X i - ridgeMean X) * U i := by
          rw [← Finset.sum_mul, hcenter]
          ring

private theorem ridge_weighted_update_sum {N : ℕ}
    (X U : Fin N → ℝ) (j : Fin N) (q : ℝ) :
    (∑ i, (X i - ridgeMean X) * Function.update U j q i) =
      (∑ i, (X i - ridgeMean X) * U i) +
        (X j - ridgeMean X) * (q - U j) := by
  have hdelta :
      (∑ i, (X i - ridgeMean X) * (Function.update U j q i - U i)) =
        (X j - ridgeMean X) * (q - U j) := by
    rw [Finset.sum_eq_single j]
    · simp only [Function.update_self]
    · intro i _hi hij
      simp [Function.update_of_ne hij]
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  calc
    _ = (∑ i, (X i - ridgeMean X) * U i) +
        ∑ i, (X i - ridgeMean X) * (Function.update U j q i - U i) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _hi
          ring
    _ = _ := by rw [hdelta]

private theorem ridge_covariance_update {N : ℕ} (hN : 0 < N)
    (X U : Fin N → ℝ) (j : Fin N) (q : ℝ) :
    ridgeCovariance X (Function.update U j q) = ridgeCovariance X U +
      (X j - ridgeMean X) * (q - U j) / (N : ℝ) := by
  rw [ridge_covariance_eq_raw_sum hN X (Function.update U j q),
    ridge_covariance_eq_raw_sum hN X U, ridge_weighted_update_sum]
  ring

private theorem ridge_sum_update_diff {N : ℕ}
    (F : Fin N → ℝ) (j : Fin N) (q : ℝ) :
    (∑ i, (Function.update F j q i - F i)) = q - F j := by
  rw [Finset.sum_eq_single j]
  · simp only [Function.update_self]
  · intro i _hi hij
    simp [Function.update_of_ne hij]
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

private theorem ridge_mean_update {N : ℕ}
    (F : Fin N → ℝ) (j : Fin N) (q : ℝ) :
    ridgeMean (Function.update F j q) = ridgeMean F + (q - F j) / (N : ℝ) := by
  unfold ridgeMean
  rw [show (∑ i, Function.update F j q i) =
      (∑ i, F i) + (q - F j) by
        have h := ridge_sum_update_diff F j q
        rw [Finset.sum_sub_distrib] at h
        linarith]
  ring

private abbrev ridgeClip (b y : ℝ) : ℝ := max (min y b) (-b)

/-- The actual scalar ridge predictor changes by the exact raw-intercept and
clipped-covariance response-coordinate formula. Its absolute finite difference
is bounded at every clipping kink by the corresponding response increment. -/
theorem ridgePredictor_actual_response_update_exact_and_bound (r : ℕ)
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1))
    (j : Fin (r + 1)) (b δ x t s : ℝ) (hb : 0 < b) (hδ : 0 < δ) :
    let N : ℝ := ((r + 1 : ℕ) : ℝ)
    let Dₜ := Function.update D j ((D j).1, fun _ : Fin 1 => t)
    let Dₛ := Function.update D j ((D j).1, fun _ : Fin 1 => s)
    let feature := fun E : LOOConcentration.Dataset
        (LOOConcentration.Observation 1 1) (r + 1) =>
      fun i : Fin (r + 1) => (E i).1 0
    let rawResponse := fun E : LOOConcentration.Dataset
        (LOOConcentration.Observation 1 1) (r + 1) =>
      fun i : Fin (r + 1) => (E i).2 0
    let clippedResponse := fun E : LOOConcentration.Dataset
        (LOOConcentration.Observation 1 1) (r + 1) =>
      fun i : Fin (r + 1) => max (min (rawResponse E i) b) (-b)
    let predictor := fun E : LOOConcentration.Dataset
        (LOOConcentration.Observation 1 1) (r + 1) => fun z : ℝ =>
      let X := feature E
      let Y := rawResponse E
      let U := clippedResponse E
      let a := (∑ i : Fin (r + 1), X i) / N
      let c := (∑ i : Fin (r + 1), U i) / N
      let v := (∑ i : Fin (r + 1), (X i - a) ^ 2) / N
      let cov := (∑ i : Fin (r + 1), (X i - a) * (U i - c)) / N
      (∑ i : Fin (r + 1), Y i) / N + (cov / (v + δ)) * (z - a)
    let X := fun i : Fin (r + 1) => (D i).1 0
    let a := (∑ i : Fin (r + 1), X i) / N
    let v := (∑ i : Fin (r + 1), (X i - a) ^ 2) / N
    (predictor Dₜ x - predictor Dₛ x =
      (t - s) / N + (x - a) * (X j - a) *
        (max (min t b) (-b) - max (min s b) (-b)) / (N * (v + δ))) ∧
    |predictor Dₜ x - predictor Dₛ x| ≤
      (1 / N + |x - a| * |X j - a| / (N * (v + δ))) * |t - s| := by
  classical
  let N : ℝ := ((r + 1 : ℕ) : ℝ)
  let X : Fin (r + 1) → ℝ := fun i => (D i).1 0
  let Y : Fin (r + 1) → ℝ := fun i => (D i).2 0
  let U : Fin (r + 1) → ℝ := fun i => ridgeClip b (Y i)
  let a : ℝ := ridgeMean X
  let v : ℝ := (∑ i : Fin (r + 1), (X i - a) ^ 2) / N
  let Dₜ : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) :=
    Function.update D j ((D j).1, fun _ : Fin 1 => t)
  let Dₛ : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) :=
    Function.update D j ((D j).1, fun _ : Fin 1 => s)
  let feature := fun E : LOOConcentration.Dataset
      (LOOConcentration.Observation 1 1) (r + 1) =>
    fun i : Fin (r + 1) => (E i).1 0
  let rawResponse := fun E : LOOConcentration.Dataset
      (LOOConcentration.Observation 1 1) (r + 1) =>
    fun i : Fin (r + 1) => (E i).2 0
  let clippedResponse := fun E : LOOConcentration.Dataset
      (LOOConcentration.Observation 1 1) (r + 1) =>
    fun i : Fin (r + 1) => ridgeClip b (rawResponse E i)
  let predictor := fun E : LOOConcentration.Dataset
      (LOOConcentration.Observation 1 1) (r + 1) => fun z : ℝ =>
    let XE := feature E
    let YE := rawResponse E
    let UE := clippedResponse E
    let aE := (∑ i : Fin (r + 1), XE i) / N
    let cE := (∑ i : Fin (r + 1), UE i) / N
    let vE := (∑ i : Fin (r + 1), (XE i - aE) ^ 2) / N
    let covE := (∑ i : Fin (r + 1), (XE i - aE) * (UE i - cE)) / N
    (∑ i : Fin (r + 1), YE i) / N + (covE / (vE + δ)) * (z - aE)
  change (predictor Dₜ x - predictor Dₛ x =
      (t - s) / N + (x - a) * (X j - a) *
        (ridgeClip b t - ridgeClip b s) / (N * (v + δ))) ∧
    |predictor Dₜ x - predictor Dₛ x| ≤
      (1 / N + |x - a| * |X j - a| / (N * (v + δ))) * |t - s|
  have hN : 0 < r + 1 := by omega
  have hNr : 0 < N := by dsimp [N]; positivity
  have hfeature (q : ℝ) :
      feature (Function.update D j ((D j).1, fun _ : Fin 1 => q)) = X := by
    funext i
    by_cases hij : i = j
    · subst i
      simp [feature, X]
    · simp [feature, Function.update_of_ne hij, X]
  have hraw (q : ℝ) :
      rawResponse (Function.update D j ((D j).1, fun _ : Fin 1 => q)) =
        Function.update Y j q := by
    funext i
    by_cases hij : i = j
    · subst i
      simp [rawResponse, Y]
    · simp [rawResponse, Function.update_of_ne hij, Y]
  have hclip (q : ℝ) :
      clippedResponse (Function.update D j ((D j).1, fun _ : Fin 1 => q)) =
        Function.update U j (ridgeClip b q) := by
    funext i
    by_cases hij : i = j
    · subst i
      simp [clippedResponse, rawResponse, U, Y]
    · simp [clippedResponse, rawResponse, Function.update_of_ne hij, U, Y]
  have hmeanX : ridgeMean X = a := rfl
  have hcov_update :
      ridgeCovariance X (Function.update U j (ridgeClip b t)) -
        ridgeCovariance X (Function.update U j (ridgeClip b s)) =
      (X j - a) * (ridgeClip b t - ridgeClip b s) / N := by
    rw [ridge_covariance_update hN X U j (ridgeClip b t),
      ridge_covariance_update hN X U j (ridgeClip b s)]
    rw [hmeanX]
    ring
  have hraw_update :
      ridgeMean (Function.update Y j t) - ridgeMean (Function.update Y j s) =
        (t - s) / N := by
    rw [ridge_mean_update Y j t, ridge_mean_update Y j s]
    ring
  have hpredictor (q : ℝ) :
      predictor (Function.update D j ((D j).1, fun _ : Fin 1 => q)) x =
        ridgeMean (Function.update Y j q) +
          (ridgeCovariance X (Function.update U j (ridgeClip b q)) /
            (v + δ)) * (x - a) := by
    dsimp only [predictor]
    rw [hfeature q, hraw q, hclip q]
  have hidentity : predictor Dₜ x - predictor Dₛ x =
      (t - s) / N + (x - a) * (X j - a) *
        (ridgeClip b t - ridgeClip b s) / (N * (v + δ)) := by
    rw [show Dₜ = Function.update D j ((D j).1, fun _ : Fin 1 => t) by rfl,
      show Dₛ = Function.update D j ((D j).1, fun _ : Fin 1 => s) by rfl,
      hpredictor t, hpredictor s]
    have hdenom : v + δ ≠ 0 := by
      have hv : 0 ≤ v := by
        dsimp [v, a, X, N]
        apply div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) (le_of_lt hNr)
      linarith
    calc
      _ = ridgeMean (Function.update Y j t) - ridgeMean (Function.update Y j s) +
          (ridgeCovariance X (Function.update U j (ridgeClip b t)) -
            ridgeCovariance X (Function.update U j (ridgeClip b s))) /
            (v + δ) * (x - a) := by ring
      _ = (t - s) / N + (x - a) * (X j - a) *
          (ridgeClip b t - ridgeClip b s) / (N * (v + δ)) := by
            rw [hraw_update, hcov_update]
            field_simp [hdenom, ne_of_gt hNr]
  refine ⟨hidentity, ?_⟩
  rw [hidentity]
  have hClipLip : LipschitzWith 1 (ridgeClip b) :=
    (LOOConcentration.Manuscript.Internal.scalarClipping_lipschitz_and_bound b hb.le).1
  have hclipBound : |ridgeClip b t - ridgeClip b s| ≤ |t - s| := by
    simpa only [ridgeClip, Real.norm_eq_abs, NNReal.coe_one, one_mul] using
      hClipLip.norm_sub_le t s
  have hv : 0 ≤ v := by
    dsimp [v, a, X, N]
    apply div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) (le_of_lt hNr)
  have hdenom : 0 < N * (v + δ) := by
    exact mul_pos hNr (by linarith)
  calc
    |(t - s) / N + (x - a) * (X j - a) *
        (ridgeClip b t - ridgeClip b s) / (N * (v + δ))| ≤
      |(t - s) / N| +
        |(x - a) * (X j - a) *
          (ridgeClip b t - ridgeClip b s) / (N * (v + δ))| := by
            exact abs_add_le _ _
    _ = |t - s| / N +
        (|x - a| * |X j - a| *
          |ridgeClip b t - ridgeClip b s|) / (N * (v + δ)) := by
          rw [abs_div, abs_of_pos hNr, abs_div, abs_of_pos hdenom]
          simp only [abs_mul]
    _ ≤ |t - s| / N +
        (|x - a| * |X j - a| * |t - s|) / (N * (v + δ)) := by
          apply add_le_add le_rfl
          apply div_le_div_of_nonneg_right _ hdenom.le
          exact mul_le_mul_of_nonneg_left hclipBound
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = (1 / N + |x - a| * |X j - a| / (N * (v + δ))) * |t - s| := by
          field_simp

end LOOConcentrationManuscript.Internal
