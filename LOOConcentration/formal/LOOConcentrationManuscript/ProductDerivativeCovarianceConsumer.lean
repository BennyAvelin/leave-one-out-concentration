import LOOConcentration.Frozen.Foundations.Dataset
import LOOConcentration.Frozen.Foundations.Observation
import LOOConcentrationManuscript.Internal.ProductDerivativeCovariance

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

/-!
The actual scalar-data consumer of the centered-covariance feature derivative
for the stabilized regression numerator.
-/

namespace LOOConcentrationManuscript

open LOOConcentrationManuscript.Internal

/-- The scalar feature coordinates of a dataset of scalar observations. -/
def featureValues {N : ℕ}
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) N) :
    Fin N → ℝ := fun i => (D i).1 0

/-- The literal clipped scalar responses used in the stabilized covariance. -/
def clippedResponseValues {N : ℕ}
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) N)
    (b : ℝ) : Fin N → ℝ :=
  fun i => max (min ((D i).2 0) b) (-b)

/-- Replace one scalar feature coordinate while keeping its response fixed. -/
def varyFeature {N : ℕ}
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) N)
    (j : Fin N) (s : ℝ) :
    LOOConcentration.Dataset (LOOConcentration.Observation 1 1) N :=
  Function.update D j (Function.update (D j).1 0 s, (D j).2)

private theorem featureValues_varyFeature {N : ℕ}
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) N)
    (j : Fin N) (s : ℝ) :
    featureValues (varyFeature D j s) = Function.update (featureValues D) j s := by
  funext i
  by_cases hij : i = j
  · subst i
    simp [featureValues, varyFeature]
  · dsimp [featureValues, varyFeature]
    rw [Function.update_of_ne hij, Function.update_of_ne hij]
    rfl

private theorem clippedResponseValues_varyFeature {N : ℕ}
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) N)
    (j : Fin N) (s b : ℝ) :
    clippedResponseValues (varyFeature D j s) b = clippedResponseValues D b := by
  funext i
  by_cases hij : i = j
  · subst i
    simp [clippedResponseValues, varyFeature]
  · dsimp [clippedResponseValues, varyFeature]
    rw [Function.update_of_ne hij]

/-- Derivative of the actual source covariance for a scalar dataset of size
`r + 1`. The complete centered covariance formula is exposed here, including
both empirical centers and the outer normalization. -/
theorem clippedDatasetCovariance_feature_hasDerivAt (r : ℕ)
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1))
    (j : Fin (r + 1)) (b : ℝ) :
    HasDerivAt
      (fun s : ℝ =>
        (∑ i : Fin (r + 1),
          (featureValues (varyFeature D j s) i -
            (∑ k : Fin (r + 1), featureValues (varyFeature D j s) k) *
              ((r + 1 : ℕ) : ℝ)⁻¹) *
          (clippedResponseValues (varyFeature D j s) b i -
            (∑ k : Fin (r + 1), clippedResponseValues (varyFeature D j s) b k) *
              ((r + 1 : ℕ) : ℝ)⁻¹)) * ((r + 1 : ℕ) : ℝ)⁻¹)
      ((clippedResponseValues D b j -
          (∑ k : Fin (r + 1), clippedResponseValues D b k) *
            ((r + 1 : ℕ) : ℝ)⁻¹) / ((r + 1 : ℕ) : ℝ))
      (featureValues D j) := by
  have hgeneric := centeredCovariance_update_hasDerivAt
    (N := r + 1) (by omega) (featureValues D) (clippedResponseValues D b) j
  simpa only [featureValues_varyFeature, clippedResponseValues_varyFeature] using hgeneric

end LOOConcentrationManuscript
