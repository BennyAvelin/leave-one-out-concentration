import LOOConcentration.Frozen.Foundations.FittedLoss
import LOOConcentration.Frozen.Foundations.LooEstimate
import LOOConcentration.Geometry.NormTransport
import LOOConcentration.Probability.ProductConditionalRisk
import LOOConcentrationRevision.Frozen.Definitions.LooRiskL1
import LOOConcentrationRevision.Frozen.Definitions.MeanFittedLoss
import LOOConcentrationRevision.Frozen.Definitions.ObservationLogSobolevConstant
import LOOConcentrationRevision.Frozen.Definitions.StandingAssumption
import LOOConcentrationRevision.Frozen.Definitions.ThetaRate
import LOOConcentrationRevision.Providers.Results.DataDependentConcentration
import LOOConcentrationRevision.Providers.Results.LooMoments
import LOOConcentrationRevision.Providers.Results.MainConcentration
import LOOConcentrationRevision.Providers.Results.SimplifiedConcentration
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.EReal.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false
namespace LOOConcentration.Revision.Challenges
open LOOConcentration LOOConcentration.Revision MeasureTheory Filter
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
            3 * (n + 2 : ℝ) * Real.exp (-(c₀ * ε ^ 2 * (n + 2 : ℝ)))) := by
  exact LOOConcentration.Revision.Providers.simplifiedConcentration

theorem mainConcentration {k m n : ℕ}
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
    ∀ (a b : NNReal) (hbound : ∀ᵐ z ∂μ,
      δ₁ (n + 1) z ≤ (a : ℝ) ∧ δ₂ (n + 1) z ≤ (b : ℝ)),
      let θuniform := thetaRate C M₂ ENNReal.toReal_nonneg
        (integral_nonneg observationNormSq_nonneg) (n + 1) (by omega)
        (ε / 3) (by linarith [h.stable.delta₃_nonneg n])
        a b a.property b.property
      Pplus ≤ θuniform + θ₂ + θ₃ ∧ Pminus ≤ θuniform + θ₂ + θ₃ := by
  exact LOOConcentration.Revision.Providers.mainConcentration μ T L δ₁ δ₂ δ₃ c d h ε hε

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

theorem dataDependentConcentration {k m n : ℕ}
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (_hlsi : observationLogSobolevConstant μ < ⊤)
    (_hsecond : Integrable observationNormSq μ)
    (H : Dataset (Observation k m) (n + 2) → ℝ) (_hH : Measurable H)
    (B δ L_K : NNReal)
    (_hL2 : eLpNorm H 2 (Measure.pi fun _ : Fin (n + 2) => μ) ≤ (B : ℝ≥0∞))
    (_hbias : |∫ D, H D ∂Measure.pi fun _ : Fin (n + 2) => μ| ≤ (δ : ℝ))
    (K : Set (Dataset (Observation k m) (n + 2))) (_hK : MeasurableSet K)
    (_hKpos : 0 < (Measure.pi fun _ : Fin (n + 2) => μ) K)
    (_hLip : ∀ D ∈ K, ∀ E ∈ K, |H D - H E| ≤ (L_K : ℝ) * datasetNorm (D - E)) :
    let ν := Measure.pi fun _ : Fin (n + 2) => μ
    let p := ν.real Kᶜ
    let C := (observationLogSobolevConstant μ).toReal
    let cBNT := 3 * (2 : ℝ) ^ 12 * Real.exp 2
    let C_K := cBNT * C * Real.log (Real.exp 1 / (1 - p))
    let η_K := (B : ℝ) * Real.sqrt (p / (1 - p))
    ∀ (ε : ℝ) (_hε : (δ : ℝ) + η_K < ε),
      let G := if C_K * (L_K : ℝ) ^ 2 = 0 then 0 else
        Real.exp (-((ε - (δ : ℝ) - η_K) ^ 2 / (2 * C_K * (L_K : ℝ) ^ 2)))
      ν.real {D | H D > ε} ≤ p + G ∧
      ν.real {D | -H D > ε} ≤ p + G ∧
      ν.real {D | |H D| > ε} ≤ p + 2 * G := by
  exact LOOConcentration.Revision.Providers.dataDependentConcentration μ _hlsi _hsecond H _hH B δ L_K _hL2 _hbias K _hK _hKpos _hLip

end LOOConcentration.Revision.Challenges
