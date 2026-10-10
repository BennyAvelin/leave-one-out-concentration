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
import LOOConcentrationRevision.Frozen.Definitions.ObservationLogSobolevConstant
import LOOConcentrationRevision.Frozen.Definitions.LooRiskL1
import LOOConcentrationRevision.Frozen.Definitions.StandingAssumption
import Mathlib.Tactic
import LOOConcentrationRevision.Providers.Results.LooMoments

/-! Exact revision command for pre-approval elaboration; no declaration approval inferred. -/

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory Filter
open scoped Topology ENNReal

theorem looMoments {k m n : ℕ}
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1)) (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (h : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)
    (p : ℝ) (_hp : 2 ≤ p)
    (_hδ₁ : MemLp (δ₁ (n + 1)) (ENNReal.ofReal p) μ)
    (_hδ₂ : MemLp (δ₂ (n + 1)) (ENNReal.ofReal p) μ) :
    let ν := Measure.pi fun _ : Fin (n + 2) => μ
    let C := (observationLogSobolevConstant μ).toReal
    let M₂ := ∫ z, observationNormSq z ∂μ
    let Qdeleted := Real.sqrt ((n + 1 : ℝ) * M₂ + C * (p - 2))
    let Qfull := Real.sqrt ((n + 2 : ℝ) * M₂ + C * (p - 2))
    let B := Real.sqrt (C * (p - 1)) *
      ((eLpNorm (δ₁ (n + 1)) (ENNReal.ofReal p) μ).toReal +
       Qdeleted * (eLpNorm (δ₂ (n + 1)) (ENNReal.ofReal p) μ).toReal +
       c / Real.sqrt (n + 2 : ℝ) + d / (n + 2 : ℝ) * Qfull +
       (∫ z, δ₁ (n + 2) z ∂μ) + (∫ z, δ₂ (n + 2) z ∂μ) * Qfull)
    let H := fun D => (looRiskL1 μ (T (n + 1)) L (h.stable.integrable_full n)) D -
      looEstimate (T n) L D
    eLpNorm (fun D => H D - ∫ E, H E ∂ν) (ENNReal.ofReal p) ν ≤ ENNReal.ofReal B ∧
    eLpNorm H (ENNReal.ofReal p) ν ≤ ENNReal.ofReal (δ₃ (n + 2) + B) ∧
    (p = 2 → (∫ D, (H D - ∫ E, H E ∂ν) ^ 2 ∂ν) ≤ B ^ 2) := by
  exact Providers.looMoments μ T L δ₁ δ₂ δ₃ c d h p _hp _hδ₁ _hδ₂

end LOOConcentration.Revision
