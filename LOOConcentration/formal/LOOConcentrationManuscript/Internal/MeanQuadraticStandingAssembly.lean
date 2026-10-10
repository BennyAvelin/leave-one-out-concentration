import LOOConcentrationManuscript.Internal.MeanQuadraticObservationIntegrabilityConsumer
import LOOConcentrationManuscript.Internal.MeanQuadraticQueryRegularityConsumer
import LOOConcentrationManuscript.Internal.MeanQuadraticStandingIntegrabilityConsumer
import LOOConcentrationManuscript.Internal.MeanQuadraticRateConvergenceConsumer
import LOOConcentrationManuscript.Internal.AmbientMeanLossRegularityConsumer
import LOOConcentrationManuscript.Internal.ScalarObservationMomentLawTransportConsumer
import LOOConcentrationManuscript.Internal.ScalarObservationLSITransportConsumer
import LOOConcentrationRevision.Frozen.Definitions.StandingAssumption

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open MeasureTheory ProbabilityTheory Filter
open scoped ContDiff ENNReal Topology

/-- Every field of the source standing assumption, for the actual response
observation law and the literal empirical-mean quadratic loss. -/
theorem empiricalMean_quadraticStanding_of_scalarLaw
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hSecond : Integrable (fun x : ℝ => x ^ 2) μ)
    (hFinite : let scalar := fun x : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => x)
      letI : IsProbabilityMeasure (μ.map scalar) := μ.isProbabilityMeasure_map (by fun_prop)
      LOOConcentration.Revision.logSobolevConstant (μ.map scalar) < ⊤)
    (n : ℕ) :
    let φ := fun x : ℝ =>
      (((fun _ : Fin 1 => (0 : ℝ)), (fun _ : Fin 1 => x)) : LOOConcentration.Observation 1 1)
    let ν := μ.map φ
    letI : IsProbabilityMeasure ν := μ.isProbabilityMeasure_map (by fun_prop)
    let T : ∀ r : ℕ, LOOConcentration.Estimator 1 1 (r + 1) := fun r D =>
      ContinuousMap.const (LOOConcentration.Features 1)
        (fun _ : Fin 1 => empiricalMean r (WithLp.toLp 2 (fun i => (D i).2 0)))
    let L := fun y y' : LOOConcentration.Responses 1 => (y 0 - y' 0) ^ 2
    let δ₁ := fun N : ℕ => fun z : LOOConcentration.Observation 1 1 =>
      2 * |z.2 0| / Real.sqrt (N : ℝ)
    let δ₂ := fun N : ℕ => fun _z : LOOConcentration.Observation 1 1 => (2 : ℝ) / (N : ℝ)
    let δ₃ := fun N : ℕ => variance (id : ℝ → ℝ) μ / ((N : ℝ) * ((N : ℝ) - 1))
    LOOConcentration.Revision.StandingAssumption (n := n) ν T L δ₁ δ₂ δ₃
      (2 * |∫ x : ℝ, x ∂μ|) 2 := by
  classical
  intro φ ν
  let : IsProbabilityMeasure ν := μ.isProbabilityMeasure_map (by
    exact (show Measurable φ from by
      change Measurable (fun x : ℝ => ((fun _ : Fin 1 => (0 : ℝ)), (fun _ : Fin 1 => x)))
      fun_prop).aemeasurable)
  intro T L δ₁ δ₂ δ₃
  have hLSI : LOOConcentration.Revision.observationLogSobolevConstant ν < ⊤ :=
    lt_of_le_of_lt (scalarResponseObservation_nativeConstant_le μ) hFinite
  have hMoment := scalarObservation_sample_and_fresh_test_transport μ hSecond true 0
  have hActual := empiricalMean_actualObservation_quadratic_integrability_bias μ hSecond
  obtain ⟨h₁, h₁lim, h₂, h₂lim, h₃, h₃lim⟩ :=
    quadraticMean_actual_response_rate_fields μ
  have hRates := scalarResponse_quadraticStanding_integrability_fields μ hSecond n
  have hStable : LOOConcentration.Revision.Stable ν hLSI T L δ₁ δ₂ δ₃ := by
    refine {
      measurable_loss := ?_
      delta₁_nonneg := h₁
      delta₂_nonneg := h₂
      delta₃_nonneg := h₃
      delta₁_tendsto := h₁lim
      delta₂_tendsto := h₂lim
      delta₃_tendsto := h₃lim
      locallyLipschitz_loss := ?_
      gradient_loss := ?_
      integrable_deleted := ?_
      integrable_full := ?_
      bias := ?_ }
    · intro r
      change Measurable (fun p : (Fin (r + 1) → LOOConcentration.Observation 1 1) ×
        LOOConcentration.Observation 1 1 =>
          (empiricalMean r (WithLp.toLp 2 (fun i => (p.1 i).2 0)) - p.2.2 0) ^ 2)
      fun_prop [empiricalMean]
    · intro r
      exact Eventually.of_forall fun z => by
        have hs := (empiricalMean_quadraticLoss_actualDataset_ambient_regular r (z.2 0) 0).1
        exact (hs.of_le (by simp : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))).locallyLipschitz
    · intro r
      exact Eventually.of_forall fun z => Eventually.of_forall fun x => by
        obtain ⟨hs, hg⟩ := empiricalMean_quadraticLoss_actualDataset_ambient_regular r (z.2 0) x
        exact ⟨hs.differentiable (by simp) x, hg⟩
    · intro r i
      exact (hActual.2 r).1 i
    · intro r
      exact (hActual.2 r).2.1
    · intro r i
      have hBias := (hActual.2 r).2.2 i
      change _ ≤ variance (id : ℝ → ℝ) μ /
        (((r + 2 : ℕ) : ℝ) * (((r + 2 : ℕ) : ℝ) - 1))
      have hDen : (((r + 2 : ℕ) : ℝ) - 1) = (r + 1 : ℝ) := by push_cast; ring
      rw [hDen]
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using hBias.le
  have hIntegrable : ∀ z : LOOConcentration.Observation 1 1,
      Integrable (fun D : Fin (n + 1) → LOOConcentration.Observation 1 1 =>
        LOOConcentration.fittedLoss (T n) L D z) (Measure.pi fun _ => ν) :=
    fun z => (hActual.1 n z).1
  have hFormula : (fun x : EuclideanSpace ℝ (LOOConcentration.ObservationCoordinate 1 1) =>
      LOOConcentration.Revision.meanFittedLoss ν (T n) L
        (LOOConcentration.Revision.observationOfEuclidean x)
        (hIntegrable (LOOConcentration.Revision.observationOfEuclidean x))) =
      (fun x : EuclideanSpace ℝ (LOOConcentration.ObservationCoordinate 1 1) =>
        (x (Sum.inr (0 : Fin 1)) - ∫ t : ℝ, t ∂μ) ^ 2 +
          variance (id : ℝ → ℝ) μ / (n + 1 : ℝ)) := by
    funext x
    exact (hActual.1 n (LOOConcentration.Revision.observationOfEuclidean x)).2
  obtain ⟨hsMean, hgMean⟩ := quadraticMean_responseQuery_polynomial_regular
    (∫ t : ℝ, t ∂μ) (variance (id : ℝ → ℝ) μ / (n + 1 : ℝ))
  refine {
    lsi := hLSI
    second_moment := hMoment.2.1
    stable := hStable
    delta₁_deleted_integrable := hRates.1
    delta₂_deleted_integrable := hRates.2.1
    delta₁_full_integrable := hRates.2.2.1
    delta₂_full_integrable := hRates.2.2.2.1
    zero_deleted_integrable := hRates.2.2.2.2.1
    zero_full_integrable := hRates.2.2.2.2.2
    c_nonneg := mul_nonneg (by norm_num) (abs_nonneg _)
    d_nonneg := by norm_num
    mean_integrable := hIntegrable
    mean_locallyLipschitz := ?_
    mean_gradient := ?_ }
  · rw [hFormula]
    exact (hsMean.of_le (by simp : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))).locallyLipschitz
  · exact Eventually.of_forall fun x => by
      simpa only [hFormula] using hgMean x

end LOOConcentration.Manuscript.Internal
