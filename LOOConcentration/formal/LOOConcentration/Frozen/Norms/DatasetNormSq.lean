import LOOConcentration.Frozen.Foundations.Dataset
import LOOConcentration.Frozen.Norms.ObservationNormSq

/-!
# Squared Euclidean norm of a dataset

Source: `LOOConcentration/v3/BeLa-LOOConcentration-referee-revision.tex`, lines 268–269.
-/

set_option autoImplicit false

namespace LOOConcentration

/-- Squared Euclidean norm of all coordinates in an ordered dataset. -/
def datasetNormSq {k m n : ℕ} (D : Dataset (Observation k m) n) : ℝ :=
  ∑ i : Fin n, observationNormSq (D i)

end LOOConcentration
