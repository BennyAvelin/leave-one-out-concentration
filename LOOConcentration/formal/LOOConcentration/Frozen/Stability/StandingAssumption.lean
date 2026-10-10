import LOOConcentration.Frozen.FunctionalInequalities.HasLogSobolev
import LOOConcentration.Frozen.Stability.Stable
import LOOConcentration.Frozen.Probability.MeanFittedLoss
import LOOConcentration.Frozen.Norms.ObservationNormSq
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Standing assumptions for the main concentration theorems

Source: `LOOConcentration/v3/BeLa-LOOConcentration-referee-revision.tex`, lines 241, 273–289,
335–345, and 378–397. Author ruling: the bounded-truncation sentence at
line 289 invokes the fixed inequality after locally Lipschitz finite-energy
class membership is proved for each truncation used in a provider proof.
-/

set_option autoImplicit false

open MeasureTheory Filter
open scoped Topology

namespace LOOConcentration

/-- The standing assumptions at a full sample size `n + 2`. -/
def StandingAssumption {k m n : ℕ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (C : ℝ)
    (T : ∀ r : ℕ, Estimator (k + 1) (m + 1) (r + 1))
    (L : Responses (m + 1) → Responses (m + 1) → ℝ)
    (δ₁ δ₂ : ℕ → Observation (k + 1) (m + 1) → ℝ)
    (δ₃ : ℕ → ℝ)
    (c d : ℝ) : Prop :=
  HasLogSobolev μ C ∧
  Integrable observationNormSq μ ∧
  Stable μ T L δ₁ δ₂ δ₃ ∧
  Integrable (δ₁ (n + 1)) μ ∧ Integrable (δ₂ (n + 1)) μ ∧
  Integrable (δ₁ (n + 2)) μ ∧ Integrable (δ₂ (n + 2)) μ ∧
  Integrable (fun z => fittedLoss (T n) L 0 z) μ ∧
  Integrable (fun z => fittedLoss (T (n + 1)) L 0 z) μ ∧
  0 ≤ c ∧ 0 ≤ d ∧
  ∃ hbar : ∀ z, Integrable
      (fun D : Dataset (Observation (k + 1) (m + 1)) (n + 1) =>
        fittedLoss (T n) L D z)
      (Measure.pi fun _ : Fin (n + 1) => μ),
    ∃ hloc : ∀ z, ∃ U ∈ 𝓝 z, ∃ K : ℝ, 0 ≤ K ∧
      ∀ w ∈ U, ∀ v ∈ U,
        |meanFittedLoss μ (T n) L w (hbar w) -
          meanFittedLoss μ (T n) L v (hbar v)| ≤
          K * observationNorm (w - v),
      ∀ z, observationLocalSlope
        ⟨fun z => meanFittedLoss μ (T n) L z (hbar z), hloc⟩ z ≤
          c + d * observationNorm z

end LOOConcentration
