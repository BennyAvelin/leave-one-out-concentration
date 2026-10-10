import Mathlib.Topology.ContinuousMap.Basic
import LOOConcentration.Frozen.Foundations.Dataset
import LOOConcentration.Frozen.Foundations.Observation

/-!
# Continuous fitted predictors

Source: `LOOConcentration/v3/BeLa-LOOConcentration-referee-revision.tex`, lines 247–250.
-/

set_option autoImplicit false

namespace LOOConcentration

/-- A continuous predictor fitted to a data set of length `n`. -/
abbrev Estimator (k m n : ℕ) :=
  Dataset (Observation k m) n → ContinuousMap (Features k) (Responses m)

end LOOConcentration
