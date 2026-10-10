import Mathlib.Analysis.SpecialFunctions.Sqrt
import LOOConcentration.Frozen.Norms.DatasetNormSq

/-!
# Euclidean norm of a dataset

Source: `LOOConcentration/v3/BeLa-LOOConcentration-referee-revision.tex`, lines 268–269.
-/

set_option autoImplicit false

namespace LOOConcentration

/-- Euclidean norm of all coordinates in an ordered dataset. -/
noncomputable def datasetNorm {k m n : ℕ}
    (D : Dataset (Observation k m) n) : ℝ :=
  Real.sqrt (datasetNormSq D)

end LOOConcentration
