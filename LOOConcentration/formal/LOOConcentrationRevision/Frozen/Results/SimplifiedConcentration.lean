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
import LOOConcentrationRevision.Frozen.Definitions.MeanFittedLoss
import LOOConcentrationRevision.Frozen.Definitions.LooRiskL1
import LOOConcentrationRevision.Frozen.Definitions.StandingAssumption
import Mathlib.Tactic
import LOOConcentrationRevision.Providers.Results.SimplifiedConcentration

/-! Exact revision command for pre-approval elaboration; no declaration approval inferred. -/

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory Filter
open scoped Topology ENNReal

theorem simplifiedConcentration :
    (∀ (k m n : ℕ) (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
      (T : ∀ r : ℕ, Estimator k m (r + 1)) (L : Responses m → Responses m → ℝ)
      (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
      (h : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)
      (hzero : ∀ z, δ₂ (n + 1) z = 0 ∧ δ₂ (n + 2) z = 0)
      (hLip : ∀ z w,
        |meanFittedLoss μ (T n) L z (h.mean_integrable z) -
          meanFittedLoss μ (T n) L w (h.mean_integrable w)| ≤ c * observationNorm (z - w)),
      let C := (observationLogSobolevConstant μ).toReal
      let ν := Measure.pi fun _ : Fin (n + 2) => μ
      let H := fun D => (looRiskL1 μ (T (n + 1)) L (h.stable.integrable_full n)) D -
        looEstimate (T n) L D
      (∀ (ε : ℝ) (_hε : 3 * δ₃ (n + 2) < ε),
        let t := (ε - δ₃ (n + 2)) / 3
        let G := fun s : ℝ => if C * s ^ 2 = 0 then 0 else
          Real.exp (-(t ^ 2 / (2 * C * s ^ 2)))
        let rhs := (n + 2 : ℝ) * (∫ z, G (δ₁ (n + 1) z) ∂μ) +
          G (c / Real.sqrt (n + 2 : ℝ)) + G (∫ z, δ₁ (n + 2) z ∂μ)
        ν.real {D | H D > ε} ≤ rhs) ∧
      (∀ (a : NNReal) (_ha : ∀ᵐ z ∂μ, δ₁ (n + 1) z ≤ (a : ℝ))
        (t : ℝ) (_ht : 0 < t),
        let s := (a : ℝ) + c / Real.sqrt (n + 2 : ℝ) + ∫ z, δ₁ (n + 2) z ∂μ
        let G := if C * s ^ 2 = 0 then 0 else Real.exp (-(t ^ 2 / (2 * C * s ^ 2)))
        ν.real {D | |H D| > δ₃ (n + 2) + t} ≤ 2 * G ∧
        ν.real {D | H D > δ₃ (n + 2) + t} ≤ G ∧
        ν.real {D | -H D > δ₃ (n + 2) + t} ≤ G)) ∧
    (∀ (C A B : NNReal), ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ (k m : ℕ) (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
        (T : ∀ r : ℕ, Estimator k m (r + 1)) (L : Responses m → Responses m → ℝ)
        (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ c d : ℕ → ℝ)
        (_hC : (observationLogSobolevConstant μ).toReal = (C : ℝ))
        (hstanding : ∀ n, StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ (c (n + 1)) (d (n + 1)))
        (_hzero : ∀ n z, δ₂ (n + 1) z = 0 ∧ δ₂ (n + 2) z = 0)
        (_hLip : ∀ n z w,
          |meanFittedLoss μ (T n) L z ((hstanding n).mean_integrable z) -
            meanFittedLoss μ (T n) L w ((hstanding n).mean_integrable w)| ≤
            c (n + 1) * observationNorm (z - w))
        (_hc : ∀ n, c (n + 1) ≤ (B : ℝ))
        (_hδ₁ : ∀ n, ∀ᵐ z ∂μ,
          δ₁ (n + 1) z ≤ (A : ℝ) / Real.sqrt (n + 1 : ℝ) ∧
          δ₁ (n + 2) z ≤ (A : ℝ) / Real.sqrt (n + 2 : ℝ)),
        ∀ (ε : ℝ) (_hε : 0 < ε), ∃ nε : ℕ, ∀ n ≥ nε,
          let ν := Measure.pi fun _ : Fin (n + 2) => μ
          let H := fun D =>
            (looRiskL1 μ (T (n + 1)) L ((hstanding n).stable.integrable_full n)) D -
              looEstimate (T n) L D
          ν.real {D | H D > ε} ≤
            3 * (n + 2 : ℝ) * Real.exp (-(c₀ * ε ^ 2 * (n + 2 : ℝ)))) := by exact LOOConcentration.Revision.Providers.simplifiedConcentration

end LOOConcentration.Revision
