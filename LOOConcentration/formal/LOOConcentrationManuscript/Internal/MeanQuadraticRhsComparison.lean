import LOOConcentrationManuscript.Internal.MeanQuadraticStandingAssembly
import LOOConcentrationManuscript.Internal.ScalarObservationThetaRateConsumer
import LOOConcentration.Results.MainRateIntegrability
import LOOConcentrationRevision.Concentration.Chernoff
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LOOConcentration.Manuscript.Internal

open MeasureTheory ProbabilityTheory
open scoped ENNReal

private theorem integrable_revisionThetaRate_of_integrable_coefficients
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {a b : α → ℝ} (ha : Integrable a μ) (hb : Integrable b μ)
    (C M₂ : ℝ) (hC : 0 ≤ C) (hM₂ : 0 ≤ M₂)
    (r : ℕ) (hr : 1 ≤ r) (t : ℝ) (ht : 0 < t)
    (ha0 : ∀ x, 0 ≤ a x) (hb0 : ∀ x, 0 ≤ b x) :
    Integrable
      (fun x => LOOConcentration.Revision.thetaRate C M₂ hC hM₂ r hr t ht
        (a x) (b x) (ha0 x) (hb0 x)) μ := by
  by_cases hC0 : C = 0
  · have hfun :
        (fun x => LOOConcentration.Revision.thetaRate C M₂ hC hM₂ r hr t ht
          (a x) (b x) (ha0 x) (hb0 x)) = fun _ => (0 : ℝ) := by
      funext x
      simp [LOOConcentration.Revision.thetaRate, hC0]
    rw [hfun]
    exact integrable_const 0
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
    have hold := LOOConcentration.integrable_thetaRate_of_integrable_coefficients
      ha hb C M₂ hCpos hM₂ r hr t ht ha0 hb0
    have hfun :
        (fun x => LOOConcentration.Revision.thetaRate C M₂ hC hM₂ r hr t ht
          (a x) (b x) (ha0 x) (hb0 x)) =
        fun x => LOOConcentration.thetaRate C M₂ hCpos hM₂ r hr t ht
          (a x) (b x) (ha0 x) (hb0 x) := by
      funext x
      exact LOOConcentration.Revision.thetaRate_eq_historical_of_pos
        C M₂ hCpos hM₂ r hr t ht (a x) (b x) (ha0 x) (hb0 x)
    rw [hfun]
    exact hold

private theorem meanQuadratic_epsilon_third_pos
    (μ : Measure ℝ) (n : ℕ) (ε : ℝ)
    (hε : 3 * (variance (id : ℝ → ℝ) μ /
      ((n + 2 : ℝ) * (n + 1 : ℝ))) < ε) :
    0 < ε / 3 := by
  have hv : 0 ≤ variance (id : ℝ → ℝ) μ := variance_nonneg _ _
  have hb : 0 ≤ variance (id : ℝ → ℝ) μ /
      ((n + 2 : ℝ) * (n + 1 : ℝ)) := div_nonneg hv (by positivity)
  linarith

private theorem meanQuadratic_epsilon_final_pos
    (μ : Measure ℝ) (n : ℕ) (ε : ℝ)
    (hε : 3 * (variance (id : ℝ → ℝ) μ /
      ((n + 2 : ℝ) * (n + 1 : ℝ))) < ε) :
    0 < ε / 3 - variance (id : ℝ → ℝ) μ /
      ((n + 2 : ℝ) * (n + 1 : ℝ)) := by
  have hv : 0 ≤ variance (id : ℝ → ℝ) μ := variance_nonneg _ _
  have hd : 0 < (n + 2 : ℝ) * (n + 1 : ℝ) := by positivity
  have hb : 0 ≤ variance (id : ℝ → ℝ) μ /
      ((n + 2 : ℝ) * (n + 1 : ℝ)) := div_nonneg hv hd.le
  linarith

theorem empiricalMean_quadratic_main_rhs_le_scalar_source
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hSecond : Integrable (fun x : ℝ => x ^ 2) μ)
    (hFinite :
      let scalar := fun x : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => x)
      letI : IsProbabilityMeasure (μ.map scalar) := μ.isProbabilityMeasure_map (by fun_prop)
      LOOConcentration.Revision.logSobolevConstant (μ.map scalar) < ⊤)
    (n : ℕ) (ε : ℝ)
    (hε : 3 * (variance (id : ℝ → ℝ) μ /
      ((n + 2 : ℝ) * (n + 1 : ℝ))) < ε) :
    let φ := fun x : ℝ =>
      (((fun _ : Fin 1 => (0 : ℝ)), (fun _ : Fin 1 => x)) : LOOConcentration.Observation 1 1)
    let ν := μ.map φ
    letI : IsProbabilityMeasure ν := μ.isProbabilityMeasure_map (by fun_prop)
    let scalar := fun x : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => x)
    letI : IsProbabilityMeasure (μ.map scalar) := μ.isProbabilityMeasure_map (by fun_prop)
    let N := n + 2
    let Cobs := (LOOConcentration.Revision.observationLogSobolevConstant ν).toReal
    let Mobs := ∫ z : LOOConcentration.Observation 1 1,
      LOOConcentration.observationNormSq z ∂ν
    let Cscalar := (LOOConcentration.Revision.logSobolevConstant (μ.map scalar)).toReal
    let M₂ := ∫ x : ℝ, x ^ 2 ∂μ
    let m := ∫ x : ℝ, x ∂μ
    let bias := variance (id : ℝ → ℝ) μ / ((N : ℝ) * (N - 1 : ℝ))
    let δ₁ := fun (q : ℕ) (z : LOOConcentration.Observation 1 1) =>
      2 * |z.2 0| / Real.sqrt (q : ℝ)
    let δ₂ := fun (q : ℕ) (_z : LOOConcentration.Observation 1 1) =>
      (2 : ℝ) / (q : ℝ)
    (N : ℝ) * (∫ z : LOOConcentration.Observation 1 1,
        LOOConcentration.Revision.thetaRate Cobs Mobs ENNReal.toReal_nonneg
          (integral_nonneg_of_ae (Filter.Eventually.of_forall
            LOOConcentration.observationNormSq_nonneg))
          (n + 1) (by omega) (ε / 3) (meanQuadratic_epsilon_third_pos μ n ε hε)
          (δ₁ (n + 1) z) (δ₂ (n + 1) z)
          (by dsimp [δ₁]; positivity) (by dsimp [δ₂]; positivity) ∂ν) +
      LOOConcentration.Revision.thetaRate Cobs Mobs ENNReal.toReal_nonneg
        (integral_nonneg_of_ae (Filter.Eventually.of_forall
          LOOConcentration.observationNormSq_nonneg))
        N (by omega) (ε / 3) (meanQuadratic_epsilon_third_pos μ n ε hε)
        (2 * |m| / Real.sqrt (N : ℝ)) (2 / (N : ℝ)) (by positivity) (by positivity) +
      LOOConcentration.Revision.thetaRate Cobs Mobs ENNReal.toReal_nonneg
        (integral_nonneg_of_ae (Filter.Eventually.of_forall
          LOOConcentration.observationNormSq_nonneg))
        N (by omega) (ε / 3 - bias) (by
          have hden : bias = variance (id : ℝ → ℝ) μ /
              ((n + 2 : ℝ) * (n + 1 : ℝ)) := by
            dsimp [bias, N]
            push_cast
            congr 1
            ring
          rw [hden]
          exact meanQuadratic_epsilon_final_pos μ n ε hε)
        (∫ z : LOOConcentration.Observation 1 1, δ₁ N z ∂ν)
        (∫ z : LOOConcentration.Observation 1 1, δ₂ N z ∂ν)
        (integral_nonneg fun z => by dsimp [δ₁]; positivity)
        (integral_nonneg fun z => by dsimp [δ₂]; positivity) ≤
    (N : ℝ) * (∫ x : ℝ,
        LOOConcentration.Revision.thetaRate Cscalar M₂ ENNReal.toReal_nonneg
          (integral_nonneg fun x : ℝ => sq_nonneg x)
          (n + 1) (by omega) (ε / 3) (meanQuadratic_epsilon_third_pos μ n ε hε)
          (2 * |x| / Real.sqrt (n + 1 : ℝ)) (2 / (n + 1 : ℝ))
          (by positivity) (by positivity) ∂μ) +
      LOOConcentration.Revision.thetaRate Cscalar M₂ ENNReal.toReal_nonneg
        (integral_nonneg fun x : ℝ => sq_nonneg x)
        N (by omega) (ε / 3) (meanQuadratic_epsilon_third_pos μ n ε hε)
        (2 * |m| / Real.sqrt (N : ℝ)) (2 / (N : ℝ)) (by positivity) (by positivity) +
      LOOConcentration.Revision.thetaRate Cscalar M₂ ENNReal.toReal_nonneg
        (integral_nonneg fun x : ℝ => sq_nonneg x)
        N (by omega) (ε / 3 - bias) (by
          have hden : bias = variance (id : ℝ → ℝ) μ /
              ((n + 2 : ℝ) * (n + 1 : ℝ)) := by
            dsimp [bias, N]
            push_cast
            congr 1
            ring
          rw [hden]
          exact meanQuadratic_epsilon_final_pos μ n ε hε)
        (2 * (∫ x : ℝ, |x| ∂μ) / Real.sqrt (N : ℝ)) (2 / (N : ℝ))
        (by positivity) (by positivity) := by
  classical
  intro φ ν
  let : IsProbabilityMeasure ν := μ.isProbabilityMeasure_map (by fun_prop)
  intro scalar
  let : IsProbabilityMeasure (μ.map scalar) := μ.isProbabilityMeasure_map (by fun_prop)
  intro N Cobs Mobs Cscalar M₂ m bias δ₁ δ₂
  let T : ∀ r : ℕ, LOOConcentration.Estimator 1 1 (r + 1) := fun r D =>
    ContinuousMap.const (LOOConcentration.Features 1)
      (fun _ : Fin 1 => LOOConcentration.Manuscript.empiricalMean r
        (WithLp.toLp 2 (fun i => (D i).2 0)))
  let L := fun y y' : LOOConcentration.Responses 1 => (y 0 - y' 0) ^ 2
  let δ₁' := fun (q : ℕ) (z : LOOConcentration.Observation 1 1) =>
    2 * |z.2 0| / Real.sqrt (q : ℝ)
  let δ₂' := fun (q : ℕ) (_z : LOOConcentration.Observation 1 1) => (2 : ℝ) / (q : ℝ)
  let δ₃ := fun q : ℕ => variance (id : ℝ → ℝ) μ /
    ((q : ℝ) * ((q : ℝ) - 1))
  have hStanding := empiricalMean_quadraticStanding_of_scalarLaw μ hSecond hFinite n
  change LOOConcentration.Revision.StandingAssumption ν T L δ₁' δ₂' δ₃
    (2 * |∫ x : ℝ, x ∂μ|) 2 at hStanding
  have hCobs : LOOConcentration.Revision.observationLogSobolevConstant ν < ⊤ :=
    hStanding.lsi
  have hAbs : Integrable (fun x : ℝ => |x|) μ := by
    have hL2 : MemLp (id : ℝ → ℝ) 2 μ :=
      (memLp_two_iff_integrable_sq (by fun_prop)).2 hSecond
    have hL1 : MemLp (id : ℝ → ℝ) 1 μ := hL2.mono_exponent (by norm_num)
    exact (memLp_one_iff_integrable.mp hL1).abs
  have hBiasNonneg : 0 ≤ bias := by
    dsimp [bias]
    have hNpos : 0 < (N : ℝ) := by dsimp [N]; positivity
    have hNminus : 0 < (N : ℝ) - 1 := by
      dsimp [N]
      push_cast
      linarith
    exact div_nonneg (variance_nonneg _ _) (mul_nonneg hNpos.le hNminus.le)
  have hden : bias = variance (id : ℝ → ℝ) μ /
      ((n + 2 : ℝ) * (n + 1 : ℝ)) := by
    dsimp [bias, N]
    push_cast
    congr 1
    ring
  have hε' : 3 * bias < ε := by rw [hden]; exact hε
  have ht : 0 < ε / 3 := by linarith
  have htBias : 0 < ε / 3 - bias := by linarith
  have hMobs : 0 ≤ Mobs := by
    dsimp [Mobs]
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall
      LOOConcentration.observationNormSq_nonneg)
  have hM₂ : 0 ≤ M₂ := by dsimp [M₂]; exact integral_nonneg fun x : ℝ => sq_nonneg x
  have hIntObsFirst := integrable_revisionThetaRate_of_integrable_coefficients
    hStanding.delta₁_deleted_integrable hStanding.delta₂_deleted_integrable
    Cobs Mobs ENNReal.toReal_nonneg hMobs (n + 1) (by omega) (ε / 3) ht
    (fun z => by dsimp [δ₁']; positivity) (fun z => by dsimp [δ₂']; positivity)
  have hIntScalarFirst := integrable_revisionThetaRate_of_integrable_coefficients
    (hAbs.const_mul (2 / Real.sqrt (n + 1 : ℝ)))
    (integrable_const (2 / (n + 1 : ℝ))) Cscalar M₂ ENNReal.toReal_nonneg hM₂
    (n + 1) (by omega) (ε / 3) ht
    (fun x => by positivity) (fun x => by positivity)
  have hPoint (x : ℝ) :
      LOOConcentration.Revision.thetaRate Cobs Mobs ENNReal.toReal_nonneg hMobs
        (n + 1) (by omega) (ε / 3) ht
        (2 * |x| / Real.sqrt (n + 1 : ℝ)) (2 / (n + 1 : ℝ))
        (by positivity) (by positivity) ≤
      LOOConcentration.Revision.thetaRate Cscalar M₂ ENNReal.toReal_nonneg hM₂
        (n + 1) (by omega) (ε / 3) ht
        (2 * |x| / Real.sqrt (n + 1 : ℝ)) (2 / (n + 1 : ℝ))
        (by positivity) (by positivity) := by
    obtain ⟨_, hcmp⟩ := scalarResponse_thetaRate_le_original_source
      μ hSecond hFinite (n + 1) (by omega) (ε / 3) ht
      (2 * |x| / Real.sqrt (n + 1 : ℝ)) (2 / (n + 1 : ℝ))
      (by positivity) (by positivity)
    simpa [Cobs, Mobs, Cscalar, M₂] using hcmp
  have hMapFirst :
      (∫ z : LOOConcentration.Observation 1 1,
        LOOConcentration.Revision.thetaRate Cobs Mobs ENNReal.toReal_nonneg hMobs
          (n + 1) (by omega) (ε / 3) ht
          (δ₁' (n + 1) z) (δ₂' (n + 1) z)
          (by positivity) (by positivity) ∂ν) =
      ∫ x : ℝ,
        LOOConcentration.Revision.thetaRate Cobs Mobs ENNReal.toReal_nonneg hMobs
          (n + 1) (by omega) (ε / 3) ht
          (δ₁' (n + 1) (φ x)) (δ₂' (n + 1) (φ x))
          (by positivity) (by positivity) ∂μ := by
    exact integral_map (by fun_prop : AEMeasurable φ μ) hIntObsFirst.aestronglyMeasurable
  have hIntegralFirst :
      (∫ z : LOOConcentration.Observation 1 1,
        LOOConcentration.Revision.thetaRate Cobs Mobs ENNReal.toReal_nonneg hMobs
          (n + 1) (by omega) (ε / 3) ht
          (2 * |z.2 0| / Real.sqrt (n + 1 : ℝ)) (2 / (n + 1 : ℝ))
          (by positivity) (by positivity) ∂ν) ≤
      ∫ x : ℝ, LOOConcentration.Revision.thetaRate Cscalar M₂ ENNReal.toReal_nonneg hM₂
          (n + 1) (by omega) (ε / 3) ht
          (2 * |x| / Real.sqrt (n + 1 : ℝ)) (2 / (n + 1 : ℝ))
          (by positivity) (by positivity) ∂μ := by
    have hactual : Integrable (fun x : ℝ =>
        LOOConcentration.Revision.thetaRate Cobs Mobs ENNReal.toReal_nonneg hMobs
          (n + 1) (by omega) (ε / 3) ht
          (2 * |x| / Real.sqrt (n + 1 : ℝ)) (2 / (n + 1 : ℝ))
          (by positivity) (by positivity)) μ := by
      have hcomp := hIntObsFirst.comp_aemeasurable (by fun_prop : AEMeasurable φ μ)
      convert hcomp using 1
      funext x
      simp [δ₁', δ₂', φ]
    have hsource : Integrable (fun x : ℝ =>
        LOOConcentration.Revision.thetaRate Cscalar M₂ ENNReal.toReal_nonneg hM₂
          (n + 1) (by omega) (ε / 3) ht
          (2 * |x| / Real.sqrt (n + 1 : ℝ)) (2 / (n + 1 : ℝ))
          (by positivity) (by positivity)) μ := by
      convert hIntScalarFirst using 1
      funext x
      congr 1
      ring
    calc
      _ = ∫ x : ℝ, LOOConcentration.Revision.thetaRate Cobs Mobs ENNReal.toReal_nonneg hMobs
          (n + 1) (by omega) (ε / 3) ht
          (2 * |x| / Real.sqrt (n + 1 : ℝ)) (2 / (n + 1 : ℝ))
          (by positivity) (by positivity) ∂μ := by
        simpa [δ₁', δ₂', φ] using hMapFirst
      _ ≤ _ := integral_mono hactual hsource (fun x => hPoint x)
  have hThirdCoeff1 :
      (∫ z : LOOConcentration.Observation 1 1, δ₁' N z ∂ν) =
        2 * (∫ x : ℝ, |x| ∂μ) / Real.sqrt (N : ℝ) := by
    rw [integral_map (by fun_prop : AEMeasurable (fun x : ℝ =>
      (((fun _ : Fin 1 => (0 : ℝ)), (fun _ : Fin 1 => x)) : LOOConcentration.Observation 1 1)) μ)
      (by fun_prop : AEStronglyMeasurable (δ₁' N) ν)]
    simp only [δ₁', N]
    rw [show (fun x : ℝ => 2 * |x| / Real.sqrt (↑(n + 2) : ℝ)) =
      fun x => (2 / Real.sqrt (↑(n + 2) : ℝ)) * |x| by funext x; ring,
      integral_const_mul]
    ring
  have hThirdCoeff2 :
      (∫ z : LOOConcentration.Observation 1 1, δ₂' N z ∂ν) = 2 / (N : ℝ) := by
    simp [δ₂', N]
  have hPointMiddle :
      LOOConcentration.Revision.thetaRate Cobs Mobs ENNReal.toReal_nonneg hMobs
        N (by omega) (ε / 3) ht
        (2 * |m| / Real.sqrt (N : ℝ)) (2 / (N : ℝ)) (by positivity) (by positivity) ≤
      LOOConcentration.Revision.thetaRate Cscalar M₂ ENNReal.toReal_nonneg hM₂
        N (by omega) (ε / 3) ht
        (2 * |m| / Real.sqrt (N : ℝ)) (2 / (N : ℝ)) (by positivity) (by positivity) := by
    obtain ⟨_, hcmp⟩ := scalarResponse_thetaRate_le_original_source
      μ hSecond hFinite N (by omega) (ε / 3) ht
      (2 * |m| / Real.sqrt (N : ℝ)) (2 / (N : ℝ)) (by positivity) (by positivity)
    simpa [Cobs, Mobs, Cscalar, M₂, m] using hcmp
  have hPointThird :
      LOOConcentration.Revision.thetaRate Cobs Mobs ENNReal.toReal_nonneg hMobs
        N (by omega) (ε / 3 - bias) htBias
        (∫ z : LOOConcentration.Observation 1 1, δ₁' N z ∂ν)
        (∫ z : LOOConcentration.Observation 1 1, δ₂' N z ∂ν)
        (integral_nonneg fun z => by dsimp [δ₁']; positivity)
        (integral_nonneg fun z => by dsimp [δ₂']; positivity) ≤
      LOOConcentration.Revision.thetaRate Cscalar M₂ ENNReal.toReal_nonneg hM₂
        N (by omega) (ε / 3 - bias) htBias
        (2 * (∫ x : ℝ, |x| ∂μ) / Real.sqrt (N : ℝ)) (2 / (N : ℝ))
        (by positivity) (by positivity) := by
    obtain ⟨_, hcmp⟩ := scalarResponse_thetaRate_le_original_source
      μ hSecond hFinite N (by omega) (ε / 3 - bias) htBias
      (∫ z : LOOConcentration.Observation 1 1, δ₁' N z ∂ν)
      (∫ z : LOOConcentration.Observation 1 1, δ₂' N z ∂ν)
      (integral_nonneg fun z => by dsimp [δ₁']; positivity)
      (integral_nonneg fun z => by dsimp [δ₂']; positivity)
    simpa [Cobs, Mobs, Cscalar, M₂, hThirdCoeff1, hThirdCoeff2] using hcmp
  have hFirstScaled :
      (N : ℝ) * (∫ z : LOOConcentration.Observation 1 1,
        LOOConcentration.Revision.thetaRate Cobs Mobs ENNReal.toReal_nonneg hMobs
          (n + 1) (by omega) (ε / 3) ht
          (2 * |z.2 0| / Real.sqrt (n + 1 : ℝ)) (2 / (n + 1 : ℝ))
          (by positivity) (by positivity) ∂ν) ≤
      (N : ℝ) * (∫ x : ℝ, LOOConcentration.Revision.thetaRate Cscalar M₂
          ENNReal.toReal_nonneg hM₂ (n + 1) (by omega) (ε / 3) ht
          (2 * |x| / Real.sqrt (n + 1 : ℝ)) (2 / (n + 1 : ℝ))
          (by positivity) (by positivity) ∂μ) :=
    mul_le_mul_of_nonneg_left hIntegralFirst (by positivity)
  have hRhs := add_le_add (add_le_add hFirstScaled hPointMiddle) hPointThird
  simpa [N, Cobs, Mobs, Cscalar, M₂, m, bias, δ₁, δ₂, δ₁', δ₂',
    hThirdCoeff1, hThirdCoeff2] using hRhs

end LOOConcentration.Manuscript.Internal
