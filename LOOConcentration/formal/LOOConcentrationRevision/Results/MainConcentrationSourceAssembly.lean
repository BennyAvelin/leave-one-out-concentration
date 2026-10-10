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
import LOOConcentrationRevision.Frozen.Definitions.ThetaRate
import Mathlib.Tactic
import LOOConcentrationRevision.Results.StandingLossDecomposition
import LOOConcentrationRevision.Concentration.StandingI1CorollaryRealConsumer
import LOOConcentrationRevision.Concentration.StandingOrderedI2SourceCorollary
import LOOConcentrationRevision.Concentration.StandingRiskThetaAllDimensions
import LOOConcentrationRevision.Concentration.StandingUniformI1WholeTailSource

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Revision
open MeasureTheory Filter
open scoped Topology ENNReal

theorem mainConcentration_source_assembly {k m n : ℕ}
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1)) (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (h : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)
    (ε : ℝ) (hε : 3 * δ₃ (n + 2) < ε) :
    let C := (observationLogSobolevConstant μ).toReal
    let M₂ := ∫ z, observationNormSq z ∂μ
    let H := fun D =>
      (looRiskL1 μ (T (n + 1)) L (h.stable.integrable_full n)) D -
        looEstimate (T n) L D
    let θ₁ := fun z => thetaRate C M₂ ENNReal.toReal_nonneg
      (integral_nonneg observationNormSq_nonneg) (n + 1) (by omega)
      (ε / 3) (by linarith [h.stable.delta₃_nonneg n])
      (δ₁ (n + 1) z) (δ₂ (n + 1) z)
      (h.stable.delta₁_nonneg n z) (h.stable.delta₂_nonneg n z)
    let θ₂ := thetaRate C M₂ ENNReal.toReal_nonneg
      (integral_nonneg observationNormSq_nonneg) (n + 2) (by omega)
      (ε / 3) (by linarith [h.stable.delta₃_nonneg n])
      (c / Real.sqrt (n + 2 : ℝ)) (d / (n + 2 : ℝ))
      (div_nonneg h.c_nonneg (Real.sqrt_nonneg _))
      (div_nonneg h.d_nonneg (by positivity))
    let θ₃ := thetaRate C M₂ ENNReal.toReal_nonneg
      (integral_nonneg observationNormSq_nonneg) (n + 2) (by omega)
      (ε / 3 - δ₃ (n + 2)) (by linarith)
      (∫ z, δ₁ (n + 2) z ∂μ) (∫ z, δ₂ (n + 2) z ∂μ)
      (integral_nonneg (h.stable.delta₁_nonneg (n + 1)))
      (integral_nonneg (h.stable.delta₂_nonneg (n + 1)))
    let Pplus := (Measure.pi fun _ : Fin (n + 2) => μ).real {D | H D > ε}
    let Pminus := (Measure.pi fun _ : Fin (n + 2) => μ).real {D | -H D > ε}
    (Pplus ≤ (n + 2 : ℝ) * (∫ z, θ₁ z ∂μ) + θ₂ + θ₃ ∧
     Pminus ≤ (n + 2 : ℝ) * (∫ z, θ₁ z ∂μ) + θ₂ + θ₃) ∧
    ∀ (a b : NNReal) (_hbound : ∀ᵐ z ∂μ,
      δ₁ (n + 1) z ≤ (a : ℝ) ∧ δ₂ (n + 1) z ≤ (b : ℝ)),
      let θuniform := thetaRate C M₂ ENNReal.toReal_nonneg
        (integral_nonneg observationNormSq_nonneg) (n + 1) (by omega)
        (ε / 3) (by linarith [h.stable.delta₃_nonneg n])
        a b a.property b.property
      Pplus ≤ θuniform + θ₂ + θ₃ ∧ Pminus ≤ θuniform + θ₂ + θ₃ := by
  dsimp only
  have ht1 : 0 < ε / 3 := by
    have hδ := h.stable.delta₃_nonneg n
    linarith
  have ht3 : 0 < ε / 3 - δ₃ (n + 2) := by
    linarith
  have hsplit := standingLoss_main_tail_split μ T L δ₁ δ₂ δ₃ c d h ε
  have hI1 := standing_I1_mixed_growth_mixture_tail_via_source_corollary
    μ T L δ₁ δ₂ δ₃ c d h (ε / 3) ht1
  have hI2 := standing_validation_ordered_I2_tails_via_source_corollary
    μ T L δ₁ δ₂ δ₃ c d h (ε / 3) ht1
  have hI3 := standing_conditional_risk_theta_tails_all_dimensions
    μ T L δ₁ δ₂ δ₃ c d h (ε / 3 - δ₃ (n + 2)) ht3
  dsimp only [standingH, standingRisk, standingI1, standingI2, standingI3,
    standingV, standingER, standingEV] at hsplit hI1 hI2 hI3 ⊢
  constructor
  · constructor
    · exact hsplit.1.trans (add_le_add (add_le_add hI1.1 hI2.1) hI3.1)
    · exact hsplit.2.trans (add_le_add (add_le_add hI1.2 hI2.2) (by simpa only [neg_sub, gt_iff_lt] using hI3.2))
  · intro a b _hbound
    have hI1u := standing_I1_actual_uniform_average_theta_tails
      μ T L δ₁ δ₂ δ₃ c d h (a : ℝ) (b : ℝ) (ε / 3) ht1 _hbound
    dsimp only [standingI1, standingV] at hI1u
    constructor
    · exact hsplit.1.trans (add_le_add (add_le_add hI1u.1 hI2.1) hI3.1)
    · exact hsplit.2.trans (add_le_add (add_le_add hI1u.2 hI2.2) (by simpa only [neg_sub, gt_iff_lt] using hI3.2))

end LOOConcentration.Revision
