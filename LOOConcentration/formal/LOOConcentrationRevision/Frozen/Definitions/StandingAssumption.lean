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
import LOOConcentrationRevision.Frozen.Definitions.ObservationOfEuclidean
import LOOConcentrationRevision.Frozen.Definitions.ObservationLogSobolevConstant
import LOOConcentrationRevision.Frozen.Definitions.MeanFittedLoss
import LOOConcentrationRevision.Frozen.Definitions.Stable

/-! Exact revision command for pre-approval elaboration; no declaration approval inferred. -/

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory Filter
open scoped Topology ENNReal

structure StandingAssumption {k m n : ℕ}
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ)
    (c d : ℝ) : Prop where
  lsi : observationLogSobolevConstant μ < ⊤
  second_moment : Integrable observationNormSq μ
  stable : Stable μ lsi T L δ₁ δ₂ δ₃
  delta₁_deleted_integrable : Integrable (δ₁ (n + 1)) μ
  delta₂_deleted_integrable : Integrable (δ₂ (n + 1)) μ
  delta₁_full_integrable : Integrable (δ₁ (n + 2)) μ
  delta₂_full_integrable : Integrable (δ₂ (n + 2)) μ
  zero_deleted_integrable : Integrable (fun z => fittedLoss (T n) L 0 z) μ
  zero_full_integrable : Integrable (fun z => fittedLoss (T (n + 1)) L 0 z) μ
  c_nonneg : 0 ≤ c
  d_nonneg : 0 ≤ d
  mean_integrable : ∀ z, Integrable
    (fun D : Dataset (Observation k m) (n + 1) => fittedLoss (T n) L D z)
    (Measure.pi fun _ : Fin (n + 1) => μ)
  mean_locallyLipschitz : LocallyLipschitz
    (fun x : EuclideanSpace ℝ (ObservationCoordinate k m) =>
      meanFittedLoss μ (T n) L (observationOfEuclidean x)
        (mean_integrable (observationOfEuclidean x)))
  mean_gradient : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (ObservationCoordinate k m))),
    let f := fun y => meanFittedLoss μ (T n) L (observationOfEuclidean y)
      (mean_integrable (observationOfEuclidean y))
    DifferentiableAt ℝ f x ∧ ‖gradient f x‖ ≤ c + d * ‖x‖

end LOOConcentration.Revision
