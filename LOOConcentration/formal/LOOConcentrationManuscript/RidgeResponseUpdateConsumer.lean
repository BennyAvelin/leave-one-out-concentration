import LOOConcentrationManuscript.Internal.RidgeResponseUpdate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

/-!
The actual absolute fitted-loss consequence of the finite response-coordinate
update. The target response remains arbitrary and the predictor keeps its raw
response mean as intercept.
-/

namespace LOOConcentrationManuscript

/-- The absolute fitted loss of the literal scalar ridge predictor obeys the
same response-coordinate finite-difference bound, for every target response. -/
theorem ridgePredictor_actual_absoluteFittedLoss_response_update_bound (r : ℕ)
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1))
    (j : Fin (r + 1)) (b δ x t s y : ℝ) (hb : 0 < b) (hδ : 0 < δ) :
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
    abs (abs (predictor Dₜ x - y) - abs (predictor Dₛ x - y)) ≤
      (1 / N + |x - a| * |X j - a| / (N * (v + δ))) * |t - s| := by
  classical
  let N : ℝ := ((r + 1 : ℕ) : ℝ)
  let X : Fin (r + 1) → ℝ := fun i => (D i).1 0
  let a : ℝ := (∑ i : Fin (r + 1), X i) / N
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
    fun i : Fin (r + 1) => max (min (rawResponse E i) b) (-b)
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
  change abs (abs (predictor Dₜ x - y) - abs (predictor Dₛ x - y)) ≤
    (1 / N + |x - a| * |X j - a| / (N * (v + δ))) * |t - s|
  have hproducer :=
    LOOConcentrationManuscript.Internal.ridgePredictor_actual_response_update_exact_and_bound
      r D j b δ x t s hb hδ
  have hexact := hproducer.1
  have hclipLip :=
    (LOOConcentration.Manuscript.Internal.scalarClipping_lipschitz_and_bound b hb.le).1
  have hclip : |max (min t b) (-b) - max (min s b) (-b)| ≤ |t - s| := by
    simpa only [Real.norm_eq_abs, NNReal.coe_one, one_mul] using
      hclipLip.norm_sub_le t s
  have hN : 0 < N := by dsimp [N]; positivity
  have hv : 0 ≤ v := by
    dsimp [v, a, X, N]
    apply div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) (le_of_lt hN)
  have hdenom : 0 < N * (v + δ) := mul_pos hN (by linarith)
  have hpredictor :
      |predictor Dₜ x - predictor Dₛ x| ≤
        (1 / N + |x - a| * |X j - a| / (N * (v + δ))) * |t - s| := by
    rw [hexact]
    calc
      |(t - s) / N + (x - a) * (X j - a) *
          (max (min t b) (-b) - max (min s b) (-b)) / (N * (v + δ))| ≤
        |(t - s) / N| +
          |(x - a) * (X j - a) *
            (max (min t b) (-b) - max (min s b) (-b)) / (N * (v + δ))| := by
              exact abs_add_le _ _
      _ = |t - s| / N +
          (|x - a| * |X j - a| *
            |max (min t b) (-b) - max (min s b) (-b)|) / (N * (v + δ)) := by
              rw [abs_div, abs_of_pos hN, abs_div, abs_of_pos hdenom]
              simp only [abs_mul]
      _ ≤ |t - s| / N +
          (|x - a| * |X j - a| * |t - s|) / (N * (v + δ)) := by
            apply add_le_add le_rfl
            apply div_le_div_of_nonneg_right _ hdenom.le
            exact mul_le_mul_of_nonneg_left hclip
              (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = (1 / N + |x - a| * |X j - a| / (N * (v + δ))) * |t - s| := by
            field_simp
  calc
    abs (abs (predictor Dₜ x - y) - abs (predictor Dₛ x - y)) ≤
        |(predictor Dₜ x - y) - (predictor Dₛ x - y)| :=
          abs_abs_sub_abs_le_abs_sub _ _
    _ = |predictor Dₜ x - predictor Dₛ x| := by
      congr 1
      ring
    _ ≤ (1 / N + |x - a| * |X j - a| / (N * (v + δ))) * |t - s| :=
      hpredictor

end LOOConcentrationManuscript
