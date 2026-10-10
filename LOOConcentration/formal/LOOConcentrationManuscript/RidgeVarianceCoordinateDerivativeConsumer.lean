import LOOConcentration.Frozen.Foundations.Dataset
import LOOConcentration.Frozen.Foundations.Observation
import LOOConcentrationManuscript.Internal.RidgeVarianceCoordinateDerivative
import LOOConcentrationManuscript.ProductDerivativeCovarianceConsumer

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

/-!
The source-shaped scalar-dataset consumer of the coordinate variance
derivative, with the response coordinate preserved by `varyFeature`.
-/

namespace LOOConcentrationManuscript

open LOOConcentrationManuscript.Internal

private theorem featureValues_varyFeature_for_variance {N : ℕ}
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

/-- The same source-literal feature variance derivative for the actual scalar
dataset `Observation 1 1`, varying one feature while preserving its response. -/
theorem actualDatasetFeatureVariance_feature_hasDerivAt (r : ℕ)
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1))
    (j : Fin (r + 1)) :
    HasDerivAt
      (fun s : ℝ =>
        (∑ i : Fin (r + 1),
          (featureValues (varyFeature D j s) i -
            (∑ k : Fin (r + 1), featureValues (varyFeature D j s) k) *
              ((r + 1 : ℕ) : ℝ)⁻¹) ^ 2) * ((r + 1 : ℕ) : ℝ)⁻¹)
      (2 * (featureValues D j -
          (∑ k : Fin (r + 1), featureValues D k) * ((r + 1 : ℕ) : ℝ)⁻¹) *
        ((r + 1 : ℕ) : ℝ)⁻¹)
      (featureValues D j) := by
  have hgeneric := coordinateUpdatedVariance_hasDerivAt
    (N := r + 1) (by omega) (featureValues D) j
  have hupdate (s : ℝ) :
      featureValues (varyFeature D j s) = Function.update (featureValues D) j s :=
    featureValues_varyFeature_for_variance D j s
  simpa only [hupdate] using hgeneric

end LOOConcentrationManuscript
