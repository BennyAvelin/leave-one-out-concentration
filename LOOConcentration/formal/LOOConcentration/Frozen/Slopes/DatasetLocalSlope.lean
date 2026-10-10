import LOOConcentration.Frozen.Norms.DatasetNorm
import Mathlib.Order.Filter.ENNReal

/-!
# Euclidean local slope on dataset space

Source: `LOOConcentration/v3/BeLa-LOOConcentration-referee-revision.tex`, lines 268–285, 335–345.
Author rulings: `k,m ≥ 1`; real slope on locally Lipschitz functions.
-/

set_option autoImplicit false

open Filter
open scoped Topology

namespace LOOConcentration

/-- Real local slope of a locally Euclidean-Lipschitz dataset function. -/
noncomputable def datasetLocalSlope {k m n : ℕ}
    (f : {g : Dataset (Observation (k + 1) (m + 1)) (n + 1) → ℝ //
      ∀ D, ∃ U ∈ 𝓝 D, ∃ C : ℝ, 0 ≤ C ∧
        ∀ E ∈ U, ∀ F ∈ U,
          |g E - g F| ≤ C * datasetNorm (E - F)})
    (D : Dataset (Observation (k + 1) (m + 1)) (n + 1)) : ℝ :=
  limsup
    (fun E : Dataset (Observation (k + 1) (m + 1)) (n + 1) =>
      |f.1 E - f.1 D| / datasetNorm (E - D))
    (𝓝[≠] D)

end LOOConcentration
