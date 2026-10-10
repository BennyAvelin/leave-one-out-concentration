import LOOConcentration.Frozen.Slopes.ObservationLocalSlope
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Fixed-constant logarithmic Sobolev inequality

Source: `LOOConcentration/v3/BeLa-LOOConcentration-referee-revision.tex`, lines 273–289.
Author ruling: finite energy means integrable squared local slope; square
integrability of the function follows from the inequality and truncation
assumption, so it is included as a conclusion here. This definition captures
the fixed-constant core inequality. The separate bounded-truncation sentence
at line 289 is tracked as a downstream obligation.
-/

set_option autoImplicit false

open MeasureTheory
open scoped Topology

namespace LOOConcentration

/-- The manuscript's log-Sobolev inequality at a fixed positive constant.
Finite energy means square integrability of the local slope; square
integrability of the function is part of the conclusion. -/
def HasLogSobolev {k m : ℕ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (C : ℝ) : Prop :=
  0 < C ∧
  ∀ (u : {g : Observation (k + 1) (m + 1) → ℝ //
    ∀ z, ∃ U ∈ 𝓝 z, ∃ K : ℝ, 0 ≤ K ∧
      ∀ w ∈ U, ∀ v ∈ U,
        |g w - g v| ≤ K * observationNorm (w - v)}),
    Integrable (fun z => observationLocalSlope u z ^ 2) μ →
    Integrable (fun z => u.1 z ^ 2) μ ∧
    Integrable (fun z => u.1 z ^ 2 * Real.log (u.1 z ^ 2)) μ ∧
    (∫ z, u.1 z ^ 2 * Real.log (u.1 z ^ 2) ∂μ) -
      (∫ z, u.1 z ^ 2 ∂μ) * Real.log (∫ z, u.1 z ^ 2 ∂μ) ≤
        2 * C * (∫ z, observationLocalSlope u z ^ 2 ∂μ)

end LOOConcentration
