import LOOConcentrationManuscript.Internal.MeanQuadraticObservationIntegrabilityConsumer
import LOOConcentrationRevision.Frozen.Definitions.LooRiskL1
import LOOConcentration.Frozen.Foundations.LooEstimate
import Mathlib.MeasureTheory.Measure.Map

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open MeasureTheory ProbabilityTheory Filter

/-- Both scalar-source tail events are the actual paired-observation tail events,
using the accepted conditional-risk class on its proved integrability domain. -/
theorem empiricalMean_quadratic_scalar_observation_H_tail_transport
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hSecond : Integrable (fun x : ℝ => x ^ 2) μ) (n : ℕ) :
    let φ := fun x : ℝ =>
      (((fun _ : Fin 1 => (0 : ℝ)), (fun _ : Fin 1 => x)) : LOOConcentration.Observation 1 1)
    let ν := μ.map φ
    letI : IsProbabilityMeasure ν := μ.isProbabilityMeasure_map (by fun_prop)
    let T : ∀ r : ℕ, LOOConcentration.Estimator 1 1 (r + 1) := fun r D =>
      ContinuousMap.const (LOOConcentration.Features 1)
        (fun _ : Fin 1 => empiricalMean r (WithLp.toLp 2 (fun i => (D i).2 0)))
    let L := fun y y' : LOOConcentration.Responses 1 => (y 0 - y' 0) ^ 2
    let Pμ := Measure.pi fun _ : Fin (n + 2) => μ
    let Pν := Measure.pi fun _ : Fin (n + 2) => ν
    let Φ := fun D : Fin (n + 2) → ℝ => fun i => φ (D i)
    ∃ hFull : Integrable
      (fun p : (Fin (n + 2) → LOOConcentration.Observation 1 1) × LOOConcentration.Observation 1 1 =>
        LOOConcentration.fittedLoss (T (n + 1)) L p.1 p.2) (Pν.prod ν),
      let Hν := fun D : Fin (n + 2) → LOOConcentration.Observation 1 1 =>
        (LOOConcentration.Revision.looRiskL1 ν (T (n + 1)) L hFull) D -
          LOOConcentration.looEstimate (T n) L D
      let Hμ := fun D : Fin (n + 2) → ℝ =>
        (∫ z : ℝ, (empiricalMean (n + 1) (WithLp.toLp 2 D) - z) ^ 2 ∂μ) -
          (n + 2 : ℝ)⁻¹ * ∑ i : Fin (n + 2),
            (empiricalMean n (WithLp.toLp 2 (fun j => D (i.succAbove j))) - D i) ^ 2
      Pμ.map Φ = Pν ∧
        ∀ ε : ℝ,
          Pν.real {D | Hν D > ε} = Pμ.real {D | Hμ D > ε} ∧
          Pν.real {D | -Hν D > ε} = Pμ.real {D | -Hμ D > ε} := by
  classical
  intro φ ν
  let : IsProbabilityMeasure ν := μ.isProbabilityMeasure_map (by
    exact (show Measurable φ from by
      change Measurable (fun x : ℝ => ((fun _ : Fin 1 => (0 : ℝ)), (fun _ : Fin 1 => x)))
      fun_prop).aemeasurable)
  intro T L Pμ Pν Φ
  have hFull := (empiricalMean_actualObservation_quadratic_integrability_bias μ hSecond).2 n |>.2.1
  refine ⟨hFull, ?_⟩
  intro Hν Hμ
  have hMap : Pμ.map Φ = Pν := (meanQuadratic_observation_product_laws μ hSecond).1 (n + 1)
  have hΦ : Measurable Φ := by change Measurable (fun D : Fin (n + 2) → ℝ => fun i => φ (D i)); fun_prop
  let Hraw := fun D : Fin (n + 2) → LOOConcentration.Observation 1 1 =>
    (∫ z, LOOConcentration.fittedLoss (T (n + 1)) L D z ∂ν) -
      LOOConcentration.looEstimate (T n) L D
  have hJoint : Measurable (fun p : (Fin (n + 2) → LOOConcentration.Observation 1 1) ×
      LOOConcentration.Observation 1 1 => LOOConcentration.fittedLoss (T (n + 1)) L p.1 p.2) := by
    change Measurable (fun p : (Fin (n + 2) → LOOConcentration.Observation 1 1) ×
      LOOConcentration.Observation 1 1 =>
        (empiricalMean (n + 1) (WithLp.toLp 2 (fun i => (p.1 i).2 0)) - p.2.2 0) ^ 2)
    fun_prop [empiricalMean]
  have hLoo : Measurable (fun D : Fin (n + 2) → LOOConcentration.Observation 1 1 =>
      LOOConcentration.looEstimate (T n) L D) := by
    change Measurable (fun D : Fin (n + 2) → LOOConcentration.Observation 1 1 =>
      (∑ i : Fin (n + 2),
        (empiricalMean n (WithLp.toLp 2 (fun j => (D (i.succAbove j)).2 0)) - (D i).2 0) ^ 2) /
          (n + 2 : ℝ))
    fun_prop [empiricalMean]
  have hRawMeas : Measurable Hraw := (hJoint.stronglyMeasurable.integral_prod_right').measurable.sub hLoo
  have hRep : Hν =ᵐ[Pν] Hraw := by
    have hClass := hFull.integral_prod_left.coeFn_toL1
    filter_upwards [hClass] with D hD
    change _ - LOOConcentration.looEstimate (T n) L D = _
    exact congrArg (fun a => a - LOOConcentration.looEstimate (T n) L D) hD
  have hRawPhi : ∀ D : Fin (n + 2) → ℝ, Hraw (Φ D) = Hμ D := by
    intro D
    have hφ : Measurable φ := by
      change Measurable (fun x : ℝ => ((fun _ : Fin 1 => (0 : ℝ)), (fun _ : Fin 1 => x)))
      fun_prop
    have hIntegrand : Measurable (fun z : LOOConcentration.Observation 1 1 =>
        LOOConcentration.fittedLoss (T (n + 1)) L (Φ D) z) := by
      change Measurable (fun z : LOOConcentration.Observation 1 1 =>
        (empiricalMean (n + 1) (WithLp.toLp 2 (fun i => (Φ D i).2 0)) - z.2 0) ^ 2)
      fun_prop
    dsimp [Hraw, Hμ]
    rw [show ν = μ.map φ from rfl, integral_map hφ.aemeasurable hIntegrand.aestronglyMeasurable]
    simp only [LOOConcentration.fittedLoss, LOOConcentration.looEstimate,
      LOOConcentration.deleteAt, T, L, Φ, φ, ContinuousMap.const_apply, div_eq_mul_inv]
    ring
  refine ⟨hMap, ?_⟩
  intro ε
  have hTail (sign : ℝ) :
      Pν.real {D | sign * Hν D > ε} = Pμ.real {D | sign * Hμ D > ε} := by
    have hs : MeasurableSet {D | sign * Hraw D > ε} :=
      measurableSet_lt measurable_const (measurable_const.mul hRawMeas)
    have hEvents : (fun D => sign * Hν D > ε) =ᵐ[Pν] (fun D => sign * Hraw D > ε) := by
      filter_upwards [hRep] with D hD
      rw [hD]
    change (Pν {D | sign * Hν D > ε}).toReal = (Pμ {D | sign * Hμ D > ε}).toReal
    have hMeasure : Pν {D | sign * Hν D > ε} = Pν {D | sign * Hraw D > ε} :=
      measure_congr hEvents
    rw [hMeasure, ← hMap, Measure.map_apply hΦ hs]
    have hPreimage : Φ ⁻¹' {D | sign * Hraw D > ε} = {D | sign * Hμ D > ε} := by
      ext D
      change (sign * Hraw (Φ D) > ε) ↔ (sign * Hμ D > ε)
      rw [hRawPhi D]
    rw [hPreimage]
  constructor
  · simpa only [one_mul] using hTail 1
  · simpa only [neg_one_mul] using hTail (-1)

end LOOConcentration.Manuscript.Internal
