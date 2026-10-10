import LOOConcentrationManuscript.Internal.KernelDensitySimplifiedTails
import LOOConcentrationManuscript.Internal.SimplifiedRateExponential

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open MeasureTheory Filter
open scoped Topology ENNReal

/-- Fixed-bandwidth concentration of the literal density estimate's query risk. -/
theorem kde_actual_fixed_bandwidth_pointwise_risk_exponential_tails
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hSecond : Integrable (fun x : ℝ => x ^ 2) μ)
    (hLSI : let scalar := fun x : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => x)
      letI : IsProbabilityMeasure (μ.map scalar) := μ.isProbabilityMeasure_map (by fun_prop)
      LOOConcentration.Revision.logSobolevConstant (μ.map scalar) < ⊤)
    (K : {K : ℝ → ℝ // ContDiff ℝ 1 K ∧ (∀ x, 0 ≤ K x) ∧
      (∃ B : ℝ, ∀ x, |K x| ≤ B) ∧ (∫ x : ℝ, K x) = 1 ∧
      (∃ B : ℝ, ∀ x, |deriv K x| ≤ B)})
    (h : {t : ℝ // 0 < t}) :
    let φ := fun x : ℝ => ((fun _ : Fin 1 => x), (fun _ : Fin 1 => (0 : ℝ)))
    let ν := μ.map φ
    letI : IsProbabilityMeasure ν := μ.isProbabilityMeasure_map (by fun_prop)
    let T := fun r : ℕ => LOOConcentration.Manuscript.kernelDensityEstimator K h r
    let L := fun a _ : LOOConcentration.Responses 1 => |a 0|
    ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      let H := fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (n + 2) =>
        (∫ z, LOOConcentration.fittedLoss (T (n + 1)) L D z ∂ν) -
          LOOConcentration.looEstimate (T n) L D
      (Measure.pi fun _ : Fin (n + 2) => ν).real {D | |H D| > ε} ≤
        2 * Real.exp (-c * (n : ℝ)) ∧
      (Measure.pi fun _ : Fin (n + 2) => ν).real {D | H D > ε} ≤
        Real.exp (-c * (n : ℝ)) ∧
      (Measure.pi fun _ : Fin (n + 2) => ν).real {D | -H D > ε} ≤
        Real.exp (-c * (n : ℝ)) := by
  intro φ ν T L ε hε
  have : IsProbabilityMeasure ν := μ.isProbabilityMeasure_map (by fun_prop)
  obtain ⟨hM, hAll⟩ := kde_actual_exact_supremum_simplified_tails μ hSecond hLSI K h
  let M := sSup (Set.range (fun t : ℝ => |deriv K.val t|))
  let σ := (LOOConcentration.Revision.observationLogSobolevConstant ν).toReal
  obtain ⟨c, hc, hDecay⟩ := simplifiedRate_two_scaled_exponential_bound σ (M / h.val ^ 2) ε
    ENNReal.toReal_nonneg (by positivity) hε
  refine ⟨c, hc, ?_⟩
  intro n H
  obtain ⟨hStanding, hTails⟩ := hAll n
  have hT := hTails ε hε
  let P := Measure.pi fun _ : Fin (n + 2) => ν
  let hf := hStanding.stable.integrable_full n
  let J := fun D => (LOOConcentration.Revision.looRiskL1 ν (T (n + 1)) L hf) D -
    LOOConcentration.looEstimate (T n) L D
  let s := M / (h.val ^ 2 * Real.sqrt (n + 1 : ℝ)) +
    2 * (M / (h.val ^ 2 * Real.sqrt (n + 2 : ℝ)))
  let G := if σ * s ^ 2 = 0 then 0 else Real.exp (-(ε ^ 2 / (2 * σ * s ^ 2)))
  have hTail : P.real {D | |J D| > ε} ≤ 2 * G ∧
      P.real {D | J D > ε} ≤ G ∧ P.real {D | -J D > ε} ≤ G := hT
  have hs : s = (M / h.val ^ 2) / Real.sqrt (n + 1 : ℝ) +
      2 * ((M / h.val ^ 2) / Real.sqrt (n + 2 : ℝ)) := by dsimp [s]; ring
  have hG : G ≤ Real.exp (-c * (n : ℝ)) := by
    dsimp only [G]
    rw [hs]
    exact hDecay n
  have hRisk : (fun D => (LOOConcentration.Revision.looRiskL1 ν (T (n + 1)) L hf) D) =ᵐ[P]
      (fun D => ∫ z, LOOConcentration.fittedLoss (T (n + 1)) L D z ∂ν) :=
    hf.integral_prod_left.coeFn_toL1
  have hHJ : H =ᵐ[P] J := by
    filter_upwards [hRisk] with D hD
    change (∫ z, LOOConcentration.fittedLoss (T (n + 1)) L D z ∂ν) -
      LOOConcentration.looEstimate (T n) L D =
      (LOOConcentration.Revision.looRiskL1 ν (T (n + 1)) L hf) D -
      LOOConcentration.looEstimate (T n) L D
    rw [hD]
  have hEvent (f : ℝ → ℝ) : P.real {D | f (H D) > ε} = P.real {D | f (J D) > ε} := by
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [hHJ] with D hD
    change (f (H D) > ε) = (f (J D) > ε)
    rw [hD]
  have hAbs : P.real {D | |H D| > ε} = P.real {D | |J D| > ε} := hEvent abs
  have hPos : P.real {D | H D > ε} = P.real {D | J D > ε} := hEvent (fun x => x)
  have hNeg : P.real {D | -H D > ε} = P.real {D | -J D > ε} := hEvent (fun x => -x)
  rw [hAbs, hPos, hNeg]
  exact ⟨hTail.1.trans (mul_le_mul_of_nonneg_left hG (by norm_num)),
    hTail.2.1.trans hG, hTail.2.2.trans hG⟩

/-- Fixed-bandwidth concentration of the literal density estimate's query risk. -/
theorem kde_actual_bandwidth_rate_pointwise_risk_tails
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hSecond : Integrable (fun x : ℝ => x ^ 2) μ)
    (hLSI : let scalar := fun x : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => x)
      letI : IsProbabilityMeasure (μ.map scalar) := μ.isProbabilityMeasure_map (by fun_prop)
      LOOConcentration.Revision.logSobolevConstant (μ.map scalar) < ⊤)
    (K : {K : ℝ → ℝ // ContDiff ℝ 1 K ∧ (∀ x, 0 ≤ K x) ∧
      (∃ B : ℝ, ∀ x, |K x| ≤ B) ∧ (∫ x : ℝ, K x) = 1 ∧
      (∃ B : ℝ, ∀ x, |deriv K x| ≤ B)})
    (h : {t : ℝ // 0 < t}) :
    let φ := fun x : ℝ => ((fun _ : Fin 1 => x), (fun _ : Fin 1 => (0 : ℝ)))
    let ν := μ.map φ
    letI : IsProbabilityMeasure ν := μ.isProbabilityMeasure_map (by fun_prop)
    let T := fun r : ℕ => LOOConcentration.Manuscript.kernelDensityEstimator K h r
    let L := fun a _ : LOOConcentration.Responses 1 => |a 0|
    ∀ ε : ℝ, 0 < ε →
      let M := sSup (Set.range (fun t : ℝ => |deriv K.val t|))
      let c := ε ^ 2 / (18 * ((LOOConcentration.Revision.observationLogSobolevConstant ν).toReal + 1) * (M + 1) ^ 2)
      0 < c ∧ ∀ n : ℕ,
      let H := fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (n + 2) =>
        (∫ z, LOOConcentration.fittedLoss (T (n + 1)) L D z ∂ν) -
          LOOConcentration.looEstimate (T n) L D
      (Measure.pi fun _ : Fin (n + 2) => ν).real {D | |H D| > ε} ≤
        2 * Real.exp (-c * (n + 1 : ℝ) * h.val ^ 4) ∧
      (Measure.pi fun _ : Fin (n + 2) => ν).real {D | H D > ε} ≤
        Real.exp (-c * (n + 1 : ℝ) * h.val ^ 4) ∧
      (Measure.pi fun _ : Fin (n + 2) => ν).real {D | -H D > ε} ≤
        Real.exp (-c * (n + 1 : ℝ) * h.val ^ 4) := by
  intro φ ν T L ε hε M c
  have : IsProbabilityMeasure ν := μ.isProbabilityMeasure_map (by fun_prop)
  obtain ⟨hM, hAll⟩ := kde_actual_exact_supremum_simplified_tails μ hSecond hLSI K h
  let σ := (LOOConcentration.Revision.observationLogSobolevConstant ν).toReal
  have hc : 0 < c := by dsimp [c]; positivity
  have hDecay := (simplifiedRate_bandwidth_exponential_bound σ M h.val ε
    ENNReal.toReal_nonneg hM h.property hε).2
  refine ⟨hc, ?_⟩
  intro n H
  obtain ⟨hStanding, hTails⟩ := hAll n
  have hT := hTails ε hε
  let P := Measure.pi fun _ : Fin (n + 2) => ν
  let hf := hStanding.stable.integrable_full n
  let J := fun D => (LOOConcentration.Revision.looRiskL1 ν (T (n + 1)) L hf) D -
    LOOConcentration.looEstimate (T n) L D
  let s := M / (h.val ^ 2 * Real.sqrt (n + 1 : ℝ)) +
    2 * (M / (h.val ^ 2 * Real.sqrt (n + 2 : ℝ)))
  let G := if σ * s ^ 2 = 0 then 0 else Real.exp (-(ε ^ 2 / (2 * σ * s ^ 2)))
  have hTail : P.real {D | |J D| > ε} ≤ 2 * G ∧
      P.real {D | J D > ε} ≤ G ∧ P.real {D | -J D > ε} ≤ G := hT
  have hG : G ≤ Real.exp (-c * (n + 1 : ℝ) * h.val ^ 4) := by
    dsimp only [G]
    exact hDecay n
  have hRisk : (fun D => (LOOConcentration.Revision.looRiskL1 ν (T (n + 1)) L hf) D) =ᵐ[P]
      (fun D => ∫ z, LOOConcentration.fittedLoss (T (n + 1)) L D z ∂ν) :=
    hf.integral_prod_left.coeFn_toL1
  have hHJ : H =ᵐ[P] J := by
    filter_upwards [hRisk] with D hD
    change (∫ z, LOOConcentration.fittedLoss (T (n + 1)) L D z ∂ν) -
      LOOConcentration.looEstimate (T n) L D =
      (LOOConcentration.Revision.looRiskL1 ν (T (n + 1)) L hf) D -
      LOOConcentration.looEstimate (T n) L D
    rw [hD]
  have hEvent (f : ℝ → ℝ) : P.real {D | f (H D) > ε} = P.real {D | f (J D) > ε} := by
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [hHJ] with D hD
    change (f (H D) > ε) = (f (J D) > ε)
    rw [hD]
  have hAbs : P.real {D | |H D| > ε} = P.real {D | |J D| > ε} := hEvent abs
  have hPos : P.real {D | H D > ε} = P.real {D | J D > ε} := hEvent (fun x => x)
  have hNeg : P.real {D | -H D > ε} = P.real {D | -J D > ε} := hEvent (fun x => -x)
  rw [hAbs, hPos, hNeg]
  exact ⟨hTail.1.trans (mul_le_mul_of_nonneg_left hG (by norm_num)),
    hTail.2.1.trans hG, hTail.2.2.trans hG⟩


end LOOConcentration.Manuscript.Internal
