import LOOConcentration.Frozen.Slopes.DatasetLocalSlope
import LOOConcentration.Frozen.Foundations.FittedLoss
import LOOConcentration.Frozen.Foundations.DeleteAt
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Algorithmic stability

Source: `LOOConcentration/v3/BeLa-LOOConcentration-referee-revision.tex`, lines 335–345.
Author rulings: positive feature and response dimensions; real local slope
on locally Lipschitz functions.
-/

set_option autoImplicit false

open MeasureTheory Filter
open scoped Topology

namespace LOOConcentration

/-- Source definition of stability, with rate indices `r` representing a
training set of size `r + 1`; rate arguments use actual sample sizes. -/
def Stable {k m : ℕ}
    (μ : Measure (Observation (k + 1) (m + 1)))
    [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator (k + 1) (m + 1) (r + 1))
    (L : Responses (m + 1) → Responses (m + 1) → ℝ)
    (δ₁ δ₂ : ℕ → Observation (k + 1) (m + 1) → ℝ)
    (δ₃ : ℕ → ℝ) : Prop :=
  (∀ r, Measurable
    (fun p : Dataset (Observation (k + 1) (m + 1)) (r + 1) ×
      Observation (k + 1) (m + 1) => fittedLoss (T r) L p.1 p.2)) ∧
  (∀ r (π : Equiv.Perm (Fin (r + 1)))
    (D : Dataset (Observation (k + 1) (m + 1)) (r + 1)) z,
    fittedLoss (T r) L (D ∘ π) z = fittedLoss (T r) L D z) ∧
  (∀ r z, 0 ≤ δ₁ (r + 1) z ∧ 0 ≤ δ₂ (r + 1) z) ∧
  (∀ r, Measurable (δ₁ (r + 1)) ∧ Measurable (δ₂ (r + 1))) ∧
  (∀ n, 0 ≤ δ₃ (n + 2)) ∧
  (∀ᵐ z ∂μ, Tendsto (fun r => δ₁ (r + 1) z) atTop (𝓝 0) ∧
    Tendsto (fun r => δ₂ (r + 1) z) atTop (𝓝 0)) ∧
  Tendsto (fun n => δ₃ (n + 2)) atTop (𝓝 0) ∧
  (∀ r, ∀ᵐ z ∂μ,
    ∃ hloc : ∀ D, ∃ U ∈ 𝓝 D, ∃ C : ℝ, 0 ≤ C ∧
      ∀ E ∈ U, ∀ F ∈ U,
        |fittedLoss (T r) L E z - fittedLoss (T r) L F z| ≤ C * datasetNorm (E - F),
      ∀ D, datasetLocalSlope
        ⟨fun E => fittedLoss (T r) L E z, hloc⟩ D ≤
          δ₁ (r + 1) z + δ₂ (r + 1) z * datasetNorm D) ∧
  (∀ n (i : Fin (n + 2)),
    Integrable
      (fun D : Dataset (Observation (k + 1) (m + 1)) (n + 2) =>
        fittedLoss (T n) L (deleteAt D i) (D i))
      (Measure.pi fun _ : Fin (n + 2) => μ) ∧
    Integrable
      (fun p : Dataset (Observation (k + 1) (m + 1)) (n + 2) ×
        Observation (k + 1) (m + 1) =>
        fittedLoss (T (n + 1)) L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ) ∧
    |(∫ D : Dataset (Observation (k + 1) (m + 1)) (n + 2),
      fittedLoss (T n) L (deleteAt D i) (D i)
        ∂Measure.pi fun _ : Fin (n + 2) => μ) -
      (∫ p : Dataset (Observation (k + 1) (m + 1)) (n + 2) ×
        Observation (k + 1) (m + 1),
        fittedLoss (T (n + 1)) L p.1 p.2
          ∂((Measure.pi fun _ : Fin (n + 2) => μ).prod μ))| ≤ δ₃ (n + 2))

end LOOConcentration
