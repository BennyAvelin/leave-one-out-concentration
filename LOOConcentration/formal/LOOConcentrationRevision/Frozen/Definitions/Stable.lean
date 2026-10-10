import LOOConcentration.Geometry.NormTransport
import LOOConcentration.Frozen.Foundations.FittedLoss
import LOOConcentration.Frozen.Foundations.LooEstimate
import LOOConcentration.Probability.ProductConditionalRisk
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Data.EReal.Basic
import LOOConcentrationRevision.Frozen.Definitions.DatasetOfEuclidean
import LOOConcentrationRevision.Frozen.Definitions.ObservationLogSobolevConstant

/-! Exact revision command for pre-approval elaboration; no declaration approval inferred. -/

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory Filter
open scoped Topology ENNReal

structure Stable {k m : ℕ}
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (_hlsi : observationLogSobolevConstant μ < ⊤)
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) : Prop where
  measurable_loss : ∀ r, Measurable
    (fun p : Dataset (Observation k m) (r + 1) × Observation k m =>
      fittedLoss (T r) L p.1 p.2)
  delta₁_nonneg : ∀ r z, 0 ≤ δ₁ (r + 1) z
  delta₂_nonneg : ∀ r z, 0 ≤ δ₂ (r + 1) z
  delta₃_nonneg : ∀ n, 0 ≤ δ₃ (n + 2)
  delta₁_tendsto : ∀ᵐ z ∂μ, Tendsto (fun r => δ₁ (r + 1) z) atTop (𝓝 0)
  delta₂_tendsto : ∀ᵐ z ∂μ, Tendsto (fun r => δ₂ (r + 1) z) atTop (𝓝 0)
  delta₃_tendsto : Tendsto (fun n => δ₃ (n + 2)) atTop (𝓝 0)
  locallyLipschitz_loss : ∀ r, ∀ᵐ z ∂μ, LocallyLipschitz
    (fun x : EuclideanSpace ℝ (DatasetCoordinate k m (r + 1)) =>
      fittedLoss (T r) L (datasetOfEuclidean x) z)
  gradient_loss : ∀ r, ∀ᵐ z ∂μ, ∀ᵐ x ∂(volume :
      Measure (EuclideanSpace ℝ (DatasetCoordinate k m (r + 1)))),
    let f := fun y => fittedLoss (T r) L (datasetOfEuclidean y) z
    DifferentiableAt ℝ f x ∧ ‖gradient f x‖ ≤ δ₁ (r + 1) z + δ₂ (r + 1) z * ‖x‖
  integrable_deleted : ∀ n (i : Fin (n + 2)), Integrable
    (fun D : Dataset (Observation k m) (n + 2) =>
      fittedLoss (T n) L (deleteAt D i) (D i))
    (Measure.pi fun _ : Fin (n + 2) => μ)
  integrable_full : ∀ n, Integrable
    (fun p : Dataset (Observation k m) (n + 2) × Observation k m =>
      fittedLoss (T (n + 1)) L p.1 p.2)
    ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ)
  bias : ∀ n (i : Fin (n + 2)),
    |(∫ D : Dataset (Observation k m) (n + 2),
      fittedLoss (T n) L (deleteAt D i) (D i)
        ∂Measure.pi fun _ : Fin (n + 2) => μ) -
      (∫ p : Dataset (Observation k m) (n + 2) × Observation k m,
        fittedLoss (T (n + 1)) L p.1 p.2
          ∂((Measure.pi fun _ : Fin (n + 2) => μ).prod μ))| ≤ δ₃ (n + 2)

end LOOConcentration.Revision
