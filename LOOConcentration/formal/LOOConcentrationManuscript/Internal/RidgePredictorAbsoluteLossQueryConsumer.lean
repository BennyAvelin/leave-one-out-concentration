import LOOConcentrationManuscript.Internal.RidgePredictorQueryFeature

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

/-!
The actual stabilized ridge predictor's source absolute loss is regular in
both test coordinates, with the query constant controlled by the ridge slope.
-/

namespace LOOConcentrationManuscript.Internal

/-- The literal source absolute fitted loss is jointly Lipschitz in the query
feature and response, uniformly over every finite actual scalar dataset. -/
theorem ridgePredictor_absoluteLoss_actual_query_lipschitz (r : ℕ)
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
    ∀ x x' y y' : ℝ,
      abs (abs (T x - y) - abs (T x' - y')) ≤
        b / (2 * Real.sqrt δ) * |x - x'| + |y - y'| := by
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
  change ∀ x x' y y' : ℝ,
    abs (abs (T x - y) - abs (T x' - y')) ≤
      b / (2 * Real.sqrt δ) * |x - x'| + |y - y'|
  have hquery := ridgePredictor_actual_query_lipschitz r D b δ hb hδ
  change ∀ x x' : ℝ,
      |T x - T x'| ≤ b / (2 * Real.sqrt δ) * |x - x'| at hquery
  intro x x' y y'
  have hresidual := abs_abs_sub_abs_le_abs_sub (T x - y) (T x' - y')
  have hsplit : (T x - y) - (T x' - y') = (T x - T x') - (y - y') := by ring
  rw [hsplit] at hresidual
  calc
    abs (abs (T x - y) - abs (T x' - y')) ≤
      |(T x - T x') - (y - y')| := hresidual
    _ ≤ |T x - T x'| + |y - y'| := by
      simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (T x - T x') 0 (y - y')
    _ ≤ b / (2 * Real.sqrt δ) * |x - x'| + |y - y'| :=
      add_le_add (hquery x x') le_rfl

end LOOConcentrationManuscript.Internal
