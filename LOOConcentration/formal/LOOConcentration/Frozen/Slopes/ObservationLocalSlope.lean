import LOOConcentration.Frozen.Norms.ObservationNorm
import Mathlib.Order.Filter.ENNReal

/-!
# Euclidean local slope on observation space

Source: `LOOConcentration/v3/BeLa-LOOConcentration-referee-revision.tex`, lines 268–285.
Author rulings: `k,m ≥ 1`; real slope on locally Lipschitz functions.
-/

set_option autoImplicit false

open Filter
open scoped Topology

namespace LOOConcentration

/-- Real local slope of a locally Euclidean-Lipschitz observation function. -/
noncomputable def observationLocalSlope {k m : ℕ}
    (f : {g : Observation (k + 1) (m + 1) → ℝ //
      ∀ z, ∃ U ∈ 𝓝 z, ∃ C : ℝ, 0 ≤ C ∧
        ∀ w ∈ U, ∀ v ∈ U,
          |g w - g v| ≤ C * observationNorm (w - v)})
    (z : Observation (k + 1) (m + 1)) : ℝ :=
  limsup
    (fun w : Observation (k + 1) (m + 1) =>
      |f.1 w - f.1 z| / observationNorm (w - z))
    (𝓝[≠] z)

end LOOConcentration
