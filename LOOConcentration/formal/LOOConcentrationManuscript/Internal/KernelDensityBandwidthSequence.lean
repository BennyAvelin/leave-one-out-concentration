import LOOConcentrationManuscript.Internal.KernelDensityExponentialTails

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open MeasureTheory Filter
open scoped Topology ENNReal

/-- The full and deleted fits use the same current bandwidth. -/
theorem kde_actual_bandwidth_sequence_concentration
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hSecond : Integrable (fun x : ℝ => x ^ 2) μ)
    (hLSI : let scalar := fun x : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => x)
      letI : IsProbabilityMeasure (μ.map scalar) := μ.isProbabilityMeasure_map (by fun_prop)
      LOOConcentration.Revision.logSobolevConstant (μ.map scalar) < ⊤)
    (K : {K : ℝ → ℝ // ContDiff ℝ 1 K ∧ (∀ x, 0 ≤ K x) ∧
      (∃ B : ℝ, ∀ x, |K x| ≤ B) ∧ (∫ x : ℝ, K x) = 1 ∧
      (∃ B : ℝ, ∀ x, |deriv K x| ≤ B)})
    (hs : ℕ → {t : ℝ // 0 < t})
    (hGrowth : Tendsto (fun N : ℕ => (N : ℝ) * (hs N).val ^ 4) atTop atTop) :
    let φ := fun x : ℝ => ((fun _ : Fin 1 => x), (fun _ : Fin 1 => (0 : ℝ)))
    let ν := μ.map φ
    let T := fun n r : ℕ => LOOConcentration.Manuscript.kernelDensityEstimator K (hs (n + 2)) r
    let L := fun a _ : LOOConcentration.Responses 1 => |a 0|
    let H := fun n (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (n + 2)) =>
      (∫ z, LOOConcentration.fittedLoss (T n (n + 1)) L D z ∂ν) -
        LOOConcentration.looEstimate (T n n) L D
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => (Measure.pi fun _ : Fin (n + 2) => ν).real {D | |H n D| > ε}) atTop (𝓝 0) ∧
      Tendsto (fun n => (Measure.pi fun _ : Fin (n + 2) => ν).real {D | H n D > ε}) atTop (𝓝 0) ∧
      Tendsto (fun n => (Measure.pi fun _ : Fin (n + 2) => ν).real {D | -H n D > ε}) atTop (𝓝 0) := by
  intro φ ν T L H ε hε
  have : IsProbabilityMeasure ν := μ.isProbabilityMeasure_map (by fun_prop)
  let M := sSup (Set.range (fun t : ℝ => |deriv K.val t|))
  let c := ε ^ 2 / (18 * ((LOOConcentration.Revision.observationLogSobolevConstant ν).toReal + 1) * (M + 1) ^ 2)
  have hBound (n : ℕ) :
      (Measure.pi fun _ : Fin (n + 2) => ν).real {D | |H n D| > ε} ≤
        2 * Real.exp (-c * (n + 1 : ℝ) * (hs (n + 2)).val ^ 4) ∧
      (Measure.pi fun _ : Fin (n + 2) => ν).real {D | H n D > ε} ≤
        Real.exp (-c * (n + 1 : ℝ) * (hs (n + 2)).val ^ 4) ∧
      (Measure.pi fun _ : Fin (n + 2) => ν).real {D | -H n D > ε} ≤
        Real.exp (-c * (n + 1 : ℝ) * (hs (n + 2)).val ^ 4) :=
    (kde_actual_bandwidth_rate_pointwise_risk_tails μ hSecond hLSI K (hs (n + 2)) ε hε).2 n
  have hc : 0 < c :=
    (kde_actual_bandwidth_rate_pointwise_risk_tails μ hSecond hLSI K (hs 2) ε hε).1
  have hShift : Tendsto (fun n : ℕ => n + 2) atTop atTop := tendsto_add_atTop_nat 2
  have hG := hGrowth.comp hShift
  have hHalf : Tendsto (fun n : ℕ => (1 / 2 : ℝ) * ((n + 2 : ℝ) * (hs (n + 2)).val ^ 4)) atTop atTop := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using hG.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2)
  have hSize : Tendsto (fun n : ℕ => (n + 1 : ℝ) * (hs (n + 2)).val ^ 4) atTop atTop := by
    apply tendsto_atTop_mono _ hHalf
    intro n
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    have hPower : 0 ≤ (hs (n + 2)).val ^ 4 := pow_nonneg (hs (n + 2)).property.le _
    nlinarith
  have hExp : Tendsto (fun n : ℕ => Real.exp (-c * (n + 1 : ℝ) * (hs (n + 2)).val ^ 4)) atTop (𝓝 0) := by
    have ht := Real.tendsto_exp_neg_atTop_nhds_zero.comp (hSize.const_mul_atTop hc)
    convert ht using 1
    funext n
    congr 1
    ring
  have hTwo : Tendsto (fun n : ℕ => 2 * Real.exp (-c * (n + 1 : ℝ) * (hs (n + 2)).val ^ 4)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hExp.const_mul 2
  refine ⟨?_, ?_, ?_⟩
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hTwo
    · intro n; exact ENNReal.toReal_nonneg
    · intro n; exact (hBound n).1
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hExp
    · intro n; exact ENNReal.toReal_nonneg
    · intro n; exact (hBound n).2.1
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hExp
    · intro n; exact ENNReal.toReal_nonneg
    · intro n; exact (hBound n).2.2

end LOOConcentration.Manuscript.Internal
