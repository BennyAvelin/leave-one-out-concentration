import LOOConcentrationManuscript.Internal.MeanAbsoluteStandingAssembly
import LOOConcentrationManuscript.Internal.StandingMeanLossLipschitz
import LOOConcentrationManuscript.Internal.SimplifiedRateExponential
import LOOConcentrationRevision.Frozen.Results.SimplifiedConcentration
import LOOConcentrationRevision.Frozen.Definitions.LooRiskL1_characterization

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal

open MeasureTheory Filter
open scoped Topology ENNReal

/-- The source response-only empirical mean has an eventual exponential tail
for the positive difference between its fresh-query risk and its delete-one
estimate. The rate is uniform in the deviation and sample size. -/
theorem empiricalMean_absolute_actual_source_concentration
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hSecond : Integrable (fun x : ℝ => x ^ 2) μ)
    (hFinite : let scalar := fun x : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => x)
      letI : IsProbabilityMeasure (μ.map scalar) := μ.isProbabilityMeasure_map (by fun_prop)
      LOOConcentration.Revision.logSobolevConstant (μ.map scalar) < ⊤) :
    let φ : ℝ → LOOConcentration.Observation 1 1 :=
      fun x => ((fun _ : Fin 1 => 0), (fun _ : Fin 1 => x))
    let ν := μ.map φ
    letI : IsProbabilityMeasure ν := μ.isProbabilityMeasure_map (by fun_prop)
    let T : ∀ r : ℕ, LOOConcentration.Estimator 1 1 (r + 1) := fun r D =>
      ContinuousMap.const (LOOConcentration.Features 1)
        (fun _ : Fin 1 => empiricalMean r
          (WithLp.toLp 2 (fun i : Fin (r + 1) => (D i).2 0)))
    let L : LOOConcentration.Responses 1 → LOOConcentration.Responses 1 → ℝ :=
      fun y y' => |y 0 - y' 0|
    ∃ c₂ : ℝ, 0 < c₂ ∧
      ∀ ε : ℝ, 0 < ε → ∃ nε : ℕ, ∀ n ≥ nε,
        let P := Measure.pi (fun _ : Fin (n + 2) => ν)
        let H := fun D =>
          (LOOConcentration.Revision.looRiskL1 ν (T (n + 1)) L
            ((empiricalMean_absoluteStanding_of_scalarLaw μ hSecond hFinite n).stable.integrable_full n)) D -
          LOOConcentration.looEstimate (T n) L D
        P.real {D | H D > ε} ≤ Real.exp (-(c₂ * ε ^ 2 * (n + 2 : ℝ))) ∧
        P.real {D | H D > ε} ≤
          3 * (n + 2 : ℝ) * Real.exp (-(c₂ * ε ^ 2 * (n + 2 : ℝ))) := by
  classical
  intro φ ν
  have hνProb : IsProbabilityMeasure ν := μ.isProbabilityMeasure_map (by fun_prop)
  intro T L
  let scalar := fun x : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => x)
  have hScalarProb : IsProbabilityMeasure (μ.map scalar) :=
    μ.isProbabilityMeasure_map (by fun_prop)
  let nativeConstant := @LOOConcentration.Revision.logSobolevConstant (Fin 1)
    inferInstance inferInstance (μ.map scalar) hScalarProb
  have hNativeFinite :
      nativeConstant < ⊤ := by
    simpa only [scalar] using hFinite
  let δ₁ := fun N : ℕ => fun _z : LOOConcentration.Observation 1 1 =>
    (Real.sqrt (N : ℝ))⁻¹
  let δ₂ := fun _N : ℕ => fun _z : LOOConcentration.Observation 1 1 => (0 : ℝ)
  let δ₃ := fun N : ℕ => 2 * (∫ x : ℝ, |x| ∂μ) / ((N : ℝ) - 1)
  let C := (LOOConcentration.Revision.observationLogSobolevConstant ν).toReal
  let σ := nativeConstant.toReal
  let c₂ := 1 / (576 * (σ + 1))
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hCσ : C ≤ σ :=
    ENNReal.toReal_mono (ne_of_lt hNativeFinite)
      (scalarResponseObservation_nativeConstant_le μ)
  have hStandingZero := empiricalMean_absoluteStanding_of_scalarLaw μ hSecond hFinite 0
  have hBiasLimit : Tendsto (fun r : ℕ => δ₃ (r + 2)) atTop (𝓝 0) :=
    hStandingZero.stable.delta₃_tendsto
  refine ⟨c₂, ?_, ?_⟩
  · dsimp [c₂]
    positivity
  · intro ε hε
    have hSmall : ∀ᶠ r : ℕ in atTop, δ₃ (r + 2) < ε / 2 := by
      exact hBiasLimit.eventually (Iio_mem_nhds (by linarith))
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hSmall
    refine ⟨max 2 N, ?_⟩
    intro n hn
    have hnN : N ≤ n := le_trans (Nat.le_max_right 2 N) hn
    have hnδ : δ₃ (n + 2) < ε / 2 := hN n hnN
    have hn2 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    let hStanding := empiricalMean_absoluteStanding_of_scalarLaw μ hSecond hFinite n
    let P := Measure.pi (fun _ : Fin (n + 2) => ν)
    let H := fun D =>
      (LOOConcentration.Revision.looRiskL1 ν (T (n + 1)) L
        (hStanding.stable.integrable_full n)) D - LOOConcentration.looEstimate (T n) L D
    change P.real {D | H D > ε} ≤ _ ∧ P.real {D | H D > ε} ≤ _
    have hLip := standing_zero_d_mean_loss_lipschitz ν T L δ₁ δ₂ δ₃ 1 hStanding
    have hZero : ∀ z, δ₂ (n + 1) z = 0 ∧ δ₂ (n + 2) z = 0 := by
      intro z
      simp only [δ₂]
      exact ⟨trivial, trivial⟩
    have hSimple := (LOOConcentration.Revision.simplifiedConcentration.1
      1 1 n ν T L δ₁ δ₂ δ₃ 1 0 hStanding hZero hLip).2
    let a : NNReal := ⟨1 / Real.sqrt ((n + 1 : ℕ) : ℝ), by positivity⟩
    have ha : (a : ℝ) = 1 / Real.sqrt ((n + 1 : ℕ) : ℝ) := rfl
    have hA : ∀ᵐ z ∂ν, δ₁ (n + 1) z ≤ (a : ℝ) := by
      filter_upwards [] with z
      simp only [δ₁, one_div, ha]
      exact le_rfl
    have hUniform := hSimple a hA (ε / 2) (by linarith)
    let s := (a : ℝ) + 1 / Real.sqrt ((n : ℝ) + 2) +
      ∫ z : LOOConcentration.Observation 1 1, δ₁ (n + 2) z ∂ν
    let G := if C * s ^ 2 = 0 then 0 else
      Real.exp (-((ε / 2) ^ 2 / (2 * C * s ^ 2)))
    have hTail : P.real {D | H D > δ₃ (n + 2) + ε / 2} ≤ G := by
      simpa only [P, H, s, G, C] using hUniform.2.1
    have hIntegral :
        (∫ z : LOOConcentration.Observation 1 1, δ₁ (n + 2) z ∂ν) =
          1 / Real.sqrt ((n : ℝ) + 2) := by
      simp only [δ₁, integral_const, probReal_univ, one_smul]
      rw [one_div]
      rw [Nat.cast_add]
      norm_num
    have hs : s = 1 / Real.sqrt ((n + 1 : ℕ) : ℝ) +
        2 * (1 / Real.sqrt ((n : ℝ) + 2)) := by
      dsimp [s]
      rw [ha, hIntegral]
      ring
    have hRate := (simplifiedRate_bandwidth_exponential_bound C 1 1 (ε / 2)
      hC (by norm_num) (by norm_num) (by linarith)).2
    have hG : G ≤ Real.exp (-(c₂ * ε ^ 2 * (n + 2 : ℝ))) := by
      let q := (ε / 2) ^ 2 / (18 * (C + 1) * (1 + 1) ^ 2)
      have hGnum : G ≤ Real.exp (-(q * (n + 1 : ℝ))) := by
        dsimp only [G]
        rw [hs]
        convert hRate n using 1
        · simp only [Nat.cast_add, Nat.cast_one, one_pow, one_mul]
        · congr 1
          dsimp [q]
          ring
      have hq : 2 * c₂ * ε ^ 2 ≤ q := by
        have hLeft : 2 * c₂ * ε ^ 2 = ε ^ 2 / (288 * (σ + 1)) := by
          dsimp [c₂]
          field_simp
          ring
        have hRight : q = ε ^ 2 / (288 * (C + 1)) := by
          dsimp [q]
          norm_num
          field_simp
          ring
        have hden : 288 * (C + 1) ≤ 288 * (σ + 1) := by nlinarith [hCσ]
        rw [hLeft, hRight]
        exact div_le_div_of_nonneg_left (sq_nonneg ε) (by positivity) hden
      have hIndex : ((n + 2 : ℕ) : ℝ) / 2 ≤ (n + 1 : ℝ) := by
        push_cast
        nlinarith
      have hExponent : c₂ * ε ^ 2 * (n + 2 : ℝ) ≤ q * (n + 1 : ℝ) := by
        calc
          c₂ * ε ^ 2 * (n + 2 : ℝ) = (2 * c₂ * ε ^ 2) * (((n + 2 : ℕ) : ℝ) / 2) := by
            push_cast
            ring
          _ ≤ q * (((n + 2 : ℕ) : ℝ) / 2) := by
            apply mul_le_mul_of_nonneg_right hq
            positivity
          _ ≤ q * (n + 1 : ℝ) := by
            apply mul_le_mul_of_nonneg_left hIndex
            dsimp [q]
            positivity
      exact hGnum.trans (Real.exp_le_exp.mpr (neg_le_neg hExponent))
    have hThreshold : δ₃ (n + 2) + ε / 2 < ε := by linarith
    have hSubset : {D | H D > ε} ⊆ {D | H D > δ₃ (n + 2) + ε / 2} := by
      intro D hD
      exact lt_trans hThreshold hD
    have hStrong : P.real {D | H D > ε} ≤
        Real.exp (-(c₂ * ε ^ 2 * (n + 2 : ℝ))) := by
      calc
        P.real {D | H D > ε} ≤ P.real {D | H D > δ₃ (n + 2) + ε / 2} :=
          measureReal_mono (μ := P) hSubset
        _ ≤ G := hTail
        _ ≤ Real.exp (-(c₂ * ε ^ 2 * (n + 2 : ℝ))) := hG
    refine ⟨hStrong, ?_⟩
    calc
      P.real {D | H D > ε} ≤ Real.exp (-(c₂ * ε ^ 2 * (n + 2 : ℝ))) := hStrong
      _ ≤ 3 * (n + 2 : ℝ) * Real.exp (-(c₂ * ε ^ 2 * (n + 2 : ℝ))) := by
        have hFactor : 1 ≤ 3 * (n + 2 : ℝ) := by
          have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
          nlinarith [hn0]
        calc
          Real.exp (-(c₂ * ε ^ 2 * (n + 2 : ℝ))) =
              1 * Real.exp (-(c₂ * ε ^ 2 * (n + 2 : ℝ))) := by ring
          _ ≤ 3 * (n + 2 : ℝ) * Real.exp (-(c₂ * ε ^ 2 * (n + 2 : ℝ))) :=
            mul_le_mul_of_nonneg_right hFactor (le_of_lt (Real.exp_pos _))

/-- Source-facing raw-risk form of the empirical-mean concentration bound.
The fresh query risk is the literal integral of the source absolute loss. -/
theorem empiricalMean_absolute_actual_raw_query_concentration
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hSecond : Integrable (fun x : ℝ => x ^ 2) μ)
    (hFinite : let scalar := fun x : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => x)
      letI : IsProbabilityMeasure (μ.map scalar) := μ.isProbabilityMeasure_map (by fun_prop)
      LOOConcentration.Revision.logSobolevConstant (μ.map scalar) < ⊤) :
    let φ : ℝ → LOOConcentration.Observation 1 1 :=
      fun x => ((fun _ : Fin 1 => 0), (fun _ : Fin 1 => x))
    let ν := μ.map φ
    letI : IsProbabilityMeasure ν := μ.isProbabilityMeasure_map (by fun_prop)
    let T : ∀ r : ℕ, LOOConcentration.Estimator 1 1 (r + 1) := fun r D =>
      ContinuousMap.const (LOOConcentration.Features 1)
        (fun _ : Fin 1 => empiricalMean r
          (WithLp.toLp 2 (fun i : Fin (r + 1) => (D i).2 0)))
    let L : LOOConcentration.Responses 1 → LOOConcentration.Responses 1 → ℝ :=
      fun y y' => |y 0 - y' 0|
    ∃ c₂ : ℝ, 0 < c₂ ∧
      ∀ ε : ℝ, 0 < ε → ∃ nε : ℕ, ∀ n ≥ nε,
        let P := Measure.pi (fun _ : Fin (n + 2) => ν)
        let H := fun D =>
          (∫ z : LOOConcentration.Observation 1 1,
            LOOConcentration.fittedLoss (T (n + 1)) L D z ∂ν) -
          LOOConcentration.looEstimate (T n) L D
        P.real {D | H D > ε} ≤ Real.exp (-(c₂ * ε ^ 2 * (n + 2 : ℝ))) ∧
        P.real {D | H D > ε} ≤
          3 * (n + 2 : ℝ) * Real.exp (-(c₂ * ε ^ 2 * (n + 2 : ℝ))) := by
  classical
  intro φ ν
  have hνProb : IsProbabilityMeasure ν := μ.isProbabilityMeasure_map (by fun_prop)
  intro T L
  obtain ⟨c₂, hc₂, hAll⟩ :=
    empiricalMean_absolute_actual_source_concentration μ hSecond hFinite
  refine ⟨c₂, hc₂, ?_⟩
  intro ε hε
  obtain ⟨nε, hAllε⟩ := hAll ε hε
  refine ⟨nε, ?_⟩
  intro n hn P H
  let hStanding := empiricalMean_absoluteStanding_of_scalarLaw μ hSecond hFinite n
  let J := fun D =>
    (LOOConcentration.Revision.looRiskL1 ν (T (n + 1)) L
      (hStanding.stable.integrable_full n)) D - LOOConcentration.looEstimate (T n) L D
  have hBase := hAllε n hn
  have hRisk :
      (fun D => (LOOConcentration.Revision.looRiskL1 ν (T (n + 1)) L
        (hStanding.stable.integrable_full n)) D) =ᵐ[P]
        (fun D => ∫ z : LOOConcentration.Observation 1 1,
          LOOConcentration.fittedLoss (T (n + 1)) L D z ∂ν) :=
    (hStanding.stable.integrable_full n).integral_prod_left.coeFn_toL1
  have hHJ : H =ᵐ[P] J := by
    filter_upwards [hRisk] with D hD
    dsimp only [H, J]
    rw [hD]
  have hEvent : P.real {D | H D > ε} = P.real {D | J D > ε} := by
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [hHJ] with D hD
    change (H D > ε) = (J D > ε)
    rw [hD]
  rw [hEvent]
  exact hBase

end LOOConcentration.Manuscript.Internal
