import LOOConcentration.Concentration.NormTruncationSlope
import LOOConcentration.Concentration.NormEntropyODE
import LOOConcentration.Concentration.SmoothTestEnergy
import LOOConcentration.Concentration.EntropyCalculus
import LOOConcentration.Probability.SampleMoments
import LOOConcentration.FunctionalInequalities.ProductLSI
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic

/-!
# Monotone limit for the squared-norm exponential moment

This module passes from the reviewed bounded norm-truncation ODE to the actual
squared dataset norm by monotone convergence. The product-LSI entropy output
remains an explicit predecessor.

Source: [arXiv:2211.02478](https://arxiv.org/abs/2211.02478) (historical audit version),
-/

set_option autoImplicit false

open MeasureTheory
open Filter
open scoped Topology ENNReal

namespace LOOConcentration

noncomputable section

/-- Explicit product-LSI predecessor for the bounded norm exponential tests.
It states the entropy inequality at the actual test and local-slope energy;
it does not assume any norm MGF conclusion. -/
abbrev HasProductNormTruncationEntropy {k m n : ℕ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (C : ℝ) : Prop :=
  ∀ (A : ℝ) (hA : 0 < A) (t : ℝ) (ht : 0 ≤ t),
    Integrable
      (fun D : Dataset (Observation (k + 1) (m + 1)) (n + 1) =>
        datasetLocalSlope
          (normTruncationExpTest (k := k) (m := m) (n := n) hA t ht) D ^ 2)
      (Measure.pi fun _ : Fin (n + 1) => μ) →
    looconcentrationEntropy (Measure.pi fun _ : Fin (n + 1) => μ)
      (fun D => Real.exp (t * normTruncation A hA D)) ≤
      2 * C * ∫ D : Dataset (Observation (k + 1) (m + 1)) (n + 1),
        datasetLocalSlope
          (normTruncationExpTest (k := k) (m := m) (n := n) hA t ht) D ^ 2
          ∂Measure.pi (fun _ : Fin (n + 1) => μ)

private theorem normTruncation_exp_integral_le
    {k m n : ℕ} (μ : Measure (Observation (k + 1) (m + 1)))
    [IsProbabilityMeasure μ] {C s : ℝ}
    (hC : 0 < C) (hs : 0 ≤ s) (hsCut : s < 1 / (2 * C))
    (hM2 : Integrable observationNormSq μ)
    (hEntropy : HasProductNormTruncationEntropy
      (k := k) (m := m) (n := n) μ C)
    (A : ℝ) (hA : 0 < A) :
    Integrable
        (fun D : Dataset (Observation (k + 1) (m + 1)) (n + 1) =>
          Real.exp (s * normTruncation A hA D))
        (Measure.pi fun _ : Fin (n + 1) => μ) ∧
      (∫ D : Dataset (Observation (k + 1) (m + 1)) (n + 1),
        Real.exp (s * normTruncation A hA D)
          ∂Measure.pi (fun _ : Fin (n + 1) => μ)) ≤
        Real.exp
          (s * ((n + 1 : ℝ) * ∫ z, observationNormSq z ∂μ) /
            (1 - 2 * C * s)) := by
  let ν : Measure (Dataset (Observation (k + 1) (m + 1)) (n + 1)) :=
    Measure.pi fun _ : Fin (n + 1) => μ
  let Q : Dataset (Observation (k + 1) (m + 1)) (n + 1) → ℝ :=
    normTruncation A hA
  have hQmeas : Measurable Q :=
    (normTruncation_contDiff (k := k) (m := m) (n := n) A hA).continuous.measurable
  have hQnn : ∀ D, 0 ≤ Q D := fun D => normTruncation_nonneg hA D
  have hQle : ∀ D, Q D ≤ datasetNormSq D :=
    fun D => normTruncation_le_normSq hA D
  have hQbound : ∀ D, |Q D| ≤ A := by
    intro D
    rw [abs_of_nonneg (hQnn D)]
    exact normTruncation_le hA D
  have hQint : Integrable Q ν := by
    apply Integrable.mono' (integrable_const A) hQmeas.aestronglyMeasurable
    filter_upwards with D
    simpa [Real.norm_eq_abs, abs_of_nonneg hA.le] using hQbound D
  have hNormInt := integrable_datasetNormSq (μ := μ) (n := n + 1) hM2
  have hQmean : (∫ D, Q D ∂ν) ≤
      (n + 1 : ℝ) * ∫ z, observationNormSq z ∂μ := by
    calc
      (∫ D, Q D ∂ν) ≤ ∫ D, datasetNormSq D ∂ν :=
        integral_mono hQint hNormInt hQle
      _ = (n + 1 : ℝ) * ∫ z, observationNormSq z ∂μ :=
        by simpa [ν, Nat.cast_add] using
          (integral_datasetNormSq (μ := μ) (n := n + 1) hM2)
  have hSlopeMeas : ∀ t (ht : 0 ≤ t),
      AEStronglyMeasurable
        (fun D : Dataset (Observation (k + 1) (m + 1)) (n + 1) =>
          datasetLocalSlope
            (normTruncationExpTest (k := k) (m := m) (n := n) hA t ht) D ^ 2)
        ν := by
    intro t ht
    exact (integrable_smoothNormTruncationExpTest_slope_sq
      (k := k) (m := m) (n := n) μ hA t ht).aestronglyMeasurable
  have hEntropyA : ∀ t (ht : 0 ≤ t),
      Integrable
        (fun D : Dataset (Observation (k + 1) (m + 1)) (n + 1) =>
          datasetLocalSlope
            (normTruncationExpTest (k := k) (m := m) (n := n) hA t ht) D ^ 2)
        ν →
      looconcentrationEntropy ν (fun D => Real.exp (t * normTruncation A hA D)) ≤
        2 * C * ∫ D : Dataset (Observation (k + 1) (m + 1)) (n + 1),
          datasetLocalSlope
            (normTruncationExpTest (k := k) (m := m) (n := n) hA t ht) D ^ 2
            ∂ν := by
    intro t ht hInt
    exact hEntropy A hA t ht hInt
  have hLog := normTruncation_logPartitionLog_le_of_product_entropy
    (k := k) (m := m) (n := n) μ hA hC hSlopeMeas hEntropyA hs hsCut
  have hDen : 0 < 1 - 2 * C * s := by
    have hmul : s * (2 * C) < 1 :=
      (lt_div_iff₀ (by positivity : 0 < 2 * C)).mp hsCut
    nlinarith [hmul]
  have hScaledMean : s * (∫ D, Q D ∂ν) ≤
      s * ((n + 1 : ℝ) * ∫ z, observationNormSq z ∂μ) :=
    mul_le_mul_of_nonneg_left hQmean hs
  have hQuotient : s * (∫ D, Q D ∂ν) / (1 - 2 * C * s) ≤
      s * ((n + 1 : ℝ) * ∫ z, observationNormSq z ∂μ) /
        (1 - 2 * C * s) :=
    div_le_div_of_nonneg_right hScaledMean hDen.le
  have hZpos : 0 < logPartition ν Q s :=
    logPartition_pos hQmeas (B := A) hQbound
  have hLog' : Real.log (∫ D, Real.exp (s * Q D) ∂ν) ≤
      s * (∫ D, Q D ∂ν) / (1 - 2 * C * s) := by
    simpa [logPartitionLog, logPartition, Q, ν, div_eq_mul_inv,
      mul_assoc, mul_left_comm, mul_comm] using hLog
  have hIntegralBound := (Real.log_le_iff_le_exp hZpos).mp
    (hLog'.trans hQuotient)
  have hExpInt : Integrable (fun D => Real.exp (s * Q D)) ν :=
    logPartition_integrable hQmeas (B := A) hQbound
  exact ⟨hExpInt, hIntegralBound⟩

/-- The exponential of the actual squared dataset norm is integrable, and its
log-MGF obeys the norm bound, conditional only on the explicit product-LSI
entropy output for the bounded smooth norm tests. The cap energy and slope
measurability are discharged by the reviewed smooth-test energy theorem. -/
theorem datasetNormSq_exp_logMGF_le_of_product_entropy
    {k m n : ℕ} (μ : Measure (Observation (k + 1) (m + 1)))
    [IsProbabilityMeasure μ] {C s : ℝ}
    (hC : 0 < C) (hs : 0 ≤ s) (hsCut : s < 1 / (2 * C))
    (hM2 : Integrable observationNormSq μ)
    (hEntropy : HasProductNormTruncationEntropy
      (k := k) (m := m) (n := n) μ C) :
    Integrable
        (fun D : Dataset (Observation (k + 1) (m + 1)) (n + 1) =>
          Real.exp (s * datasetNormSq D))
        (Measure.pi fun _ : Fin (n + 1) => μ) ∧
      Real.log (∫ D : Dataset (Observation (k + 1) (m + 1)) (n + 1),
        Real.exp (s * datasetNormSq D) ∂Measure.pi (fun _ : Fin (n + 1) => μ)) ≤
        s * ((n + 1 : ℝ) * ∫ z, observationNormSq z ∂μ) /
          (1 - 2 * C * s) := by
  let ν : Measure (Dataset (Observation (k + 1) (m + 1)) (n + 1)) :=
    Measure.pi fun _ : Fin (n + 1) => μ
  let Q : Dataset (Observation (k + 1) (m + 1)) (n + 1) → ℝ :=
    datasetNormSq
  let f : ℕ → Dataset (Observation (k + 1) (m + 1)) (n + 1) → ℝ≥0∞ :=
    fun j D => ENNReal.ofReal
      (Real.exp (s * normTruncationSequence D j))
  have hfmeas : ∀ j, Measurable (f j) := by
    intro j
    dsimp [f]
    exact ENNReal.continuous_ofReal.measurable.comp
      (Real.measurable_exp.comp
        (measurable_const.mul
          ((normTruncation_contDiff (k := k) (m := m) (n := n)
            ((j + 1 : ℕ) : ℝ) (by positivity)).continuous.measurable)))
  have hfmono : Monotone f := by
    intro i j hij D
    apply ENNReal.ofReal_le_ofReal
    exact Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (normTruncationSequence_monotone D hij) hs)
  have hpointwise : (fun D => ⨆ j, f j D) =
      (fun D => ENNReal.ofReal (Real.exp (s * Q D))) := by
    funext D
    apply iSup_eq_of_tendsto (fun i j hij => hfmono hij D)
    have hseq := normTruncationSequence_tendsto D
    have hscaled : Tendsto (fun j => s * normTruncationSequence D j)
        atTop (𝓝 (s * datasetNormSq D)) :=
      tendsto_const_nhds.mul hseq
    have hexp : Tendsto (fun j => Real.exp (s * normTruncationSequence D j))
        atTop (𝓝 (Real.exp (s * datasetNormSq D))) :=
      (Real.continuous_exp.tendsto _).comp hscaled
    change Tendsto
      (fun j => ENNReal.ofReal
        (Real.exp (s * normTruncationSequence D j)))
      atTop (𝓝 (ENNReal.ofReal (Real.exp (s * Q D))))
    simpa [Q] using ENNReal.tendsto_ofReal hexp
  have hlintegral : (∫⁻ D, ENNReal.ofReal (Real.exp (s * Q D)) ∂ν) =
      ⨆ j, ∫⁻ D, f j D ∂ν := by
    rw [← hpointwise, lintegral_iSup hfmeas hfmono]
  have hCapMajorant :
      (∫⁻ D, ENNReal.ofReal (Real.exp (s * Q D)) ∂ν) ≤
        ENNReal.ofReal
          (Real.exp
            (s * ((n + 1 : ℝ) * ∫ z, observationNormSq z ∂μ) /
              (1 - 2 * C * s))) := by
    rw [hlintegral]
    apply iSup_le
    intro j
    have hAj : 0 < ((j + 1 : ℕ) : ℝ) := by positivity
    have hCap := normTruncation_exp_integral_le
      (k := k) (m := m) (n := n) μ hC hs hsCut hM2 hEntropy
      ((j + 1 : ℕ) : ℝ) hAj
    have hCapENN := ofReal_integral_eq_lintegral_ofReal
      hCap.1 (ae_of_all _ (fun D => (Real.exp_pos _).le))
    have hCapLe := ENNReal.ofReal_le_ofReal hCap.2
    calc
      (∫⁻ D, f j D ∂ν) =
          ENNReal.ofReal
            (∫ D, Real.exp (s * normTruncationSequence D j) ∂ν) := by
        symm
        simpa [f, normTruncationSequence] using hCapENN
      _ ≤ ENNReal.ofReal
          (Real.exp
            (s * ((n + 1 : ℝ) * ∫ z, observationNormSq z ∂μ) /
              (1 - 2 * C * s))) := hCapLe
  have hFinite :
      (∫⁻ D, ENNReal.ofReal (Real.exp (s * Q D)) ∂ν) ≠ ∞ := by
    exact ne_of_lt (lt_of_le_of_lt hCapMajorant ENNReal.ofReal_lt_top)
  have hExpMeas : Measurable (fun D : Dataset
      (Observation (k + 1) (m + 1)) (n + 1) => Real.exp (s * Q D)) := by
    change Measurable (fun D => Real.exp (s * datasetNormSq D))
    exact Real.measurable_exp.comp
      (measurable_const.mul (continuous_datasetNormSq (k := k + 1)
        (m := m + 1) (n := n + 1)).measurable)
  have hExpInt : Integrable (fun D => Real.exp (s * Q D)) ν :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      hExpMeas.aestronglyMeasurable
      (ae_of_all _ (fun D => (Real.exp_pos _).le))).mp hFinite
  have hRealENN := ofReal_integral_eq_lintegral_ofReal
    hExpInt (ae_of_all _ (fun D => (Real.exp_pos _).le))
  have hRealBound : (∫ D, Real.exp (s * Q D) ∂ν) ≤
      Real.exp
        (s * ((n + 1 : ℝ) * ∫ z, observationNormSq z ∂μ) /
          (1 - 2 * C * s)) := by
    apply (ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le).mp
    rw [hRealENN]
    exact hCapMajorant
  have hIntegralPos : 0 < ∫ D, Real.exp (s * Q D) ∂ν := by
    have hLower := integral_mono (integrable_const (1 : ℝ)) hExpInt
      (fun D => Real.one_le_exp (mul_nonneg hs (datasetNormSq_nonneg D)))
    have hOne : (∫ _D : Dataset (Observation (k + 1) (m + 1)) (n + 1),
        (1 : ℝ) ∂ν) = 1 := by
      simp [ν, probReal_univ]
    rw [hOne] at hLower
    exact lt_of_lt_of_le (by norm_num) hLower
  refine ⟨hExpInt, ?_⟩
  apply (Real.log_le_iff_le_exp hIntegralPos).2
  exact hRealBound

/-- The centered squared-norm log-MGF bound follows by removing the actual
mean `(n+1) * M₂` from the uncentered exponential. This remains conditional
on the explicit product-LSI entropy predecessor above. -/
theorem centered_datasetNormSq_logMGF_le_of_product_entropy
    {k m n : ℕ} (μ : Measure (Observation (k + 1) (m + 1)))
    [IsProbabilityMeasure μ] {C s : ℝ}
    (hC : 0 < C) (hs : 0 ≤ s) (hsCut : s < 1 / (2 * C))
    (hM2 : Integrable observationNormSq μ)
    (hEntropy : HasProductNormTruncationEntropy
      (k := k) (m := m) (n := n) μ C) :
    Integrable
        (fun D : Dataset (Observation (k + 1) (m + 1)) (n + 1) =>
          Real.exp (s * (datasetNormSq D -
            (n + 1 : ℝ) * ∫ z, observationNormSq z ∂μ)))
        (Measure.pi fun _ : Fin (n + 1) => μ) ∧
      Real.log (∫ D : Dataset (Observation (k + 1) (m + 1)) (n + 1),
        Real.exp (s * (datasetNormSq D -
          (n + 1 : ℝ) * ∫ z, observationNormSq z ∂μ))
          ∂Measure.pi (fun _ : Fin (n + 1) => μ)) ≤
        2 * C * s ^ 2 * ((n + 1 : ℝ) * ∫ z, observationNormSq z ∂μ) /
          (1 - 2 * C * s) := by
  let ν : Measure (Dataset (Observation (k + 1) (m + 1)) (n + 1)) :=
    Measure.pi fun _ : Fin (n + 1) => μ
  let M : ℝ := (n + 1 : ℝ) * ∫ z, observationNormSq z ∂μ
  let Q : Dataset (Observation (k + 1) (m + 1)) (n + 1) → ℝ :=
    datasetNormSq
  have hUncentered := datasetNormSq_exp_logMGF_le_of_product_entropy
    (k := k) (m := m) (n := n) μ hC hs hsCut hM2 hEntropy
  have hBaseInt : Integrable (fun D => Real.exp (s * Q D)) ν := by
    simpa [ν, Q] using hUncentered.1
  have hShiftInt : Integrable
      (fun D => Real.exp (-s * M) * Real.exp (s * Q D)) ν :=
    hBaseInt.const_mul (Real.exp (-s * M))
  have hExpShift (D : Dataset (Observation (k + 1) (m + 1)) (n + 1)) :
      Real.exp (s * (Q D - M)) =
        Real.exp (-s * M) * Real.exp (s * Q D) := by
    calc
      Real.exp (s * (Q D - M)) = Real.exp (s * Q D + (-s * M)) := by
        congr 1
        ring
      _ = Real.exp (s * Q D) * Real.exp (-s * M) := Real.exp_add _ _
      _ = Real.exp (-s * M) * Real.exp (s * Q D) := by ring
  have hCenteredInt : Integrable
      (fun D => Real.exp (s * (Q D - M))) ν := by
    refine hShiftInt.congr ?_
    filter_upwards with D
    exact (hExpShift D).symm
  have hIntegralEq :
      (∫ D, Real.exp (s * (Q D - M)) ∂ν) =
        Real.exp (-s * M) * ∫ D, Real.exp (s * Q D) ∂ν := by
    calc
      (∫ D, Real.exp (s * (Q D - M)) ∂ν) =
          ∫ D, Real.exp (-s * M) * Real.exp (s * Q D) ∂ν := by
        apply integral_congr_ae
        filter_upwards with D
        exact hExpShift D
      _ = Real.exp (-s * M) * ∫ D, Real.exp (s * Q D) ∂ν :=
        integral_const_mul _ _
  have hBasePos : 0 < ∫ D, Real.exp (s * Q D) ∂ν := by
    have hLower := integral_mono (integrable_const (1 : ℝ)) hBaseInt
      (fun D => Real.one_le_exp (mul_nonneg hs (datasetNormSq_nonneg D)))
    have hOne : (∫ _D : Dataset (Observation (k + 1) (m + 1)) (n + 1),
        (1 : ℝ) ∂ν) = 1 := by
      simp [ν, probReal_univ]
    rw [hOne] at hLower
    exact lt_of_lt_of_le (by norm_num) hLower
  have hCenteredPos : 0 < ∫ D, Real.exp (s * (Q D - M)) ∂ν := by
    rw [hIntegralEq]
    exact mul_pos (Real.exp_pos _) hBasePos
  have hLogBase := hUncentered.2
  have hLogEq :
      Real.log (∫ D, Real.exp (s * (Q D - M)) ∂ν) =
        -s * M + Real.log (∫ D, Real.exp (s * Q D) ∂ν) := by
    rw [hIntegralEq, Real.log_mul (ne_of_gt (Real.exp_pos _))
      (ne_of_gt hBasePos), Real.log_exp]
  have hDen : 0 < 1 - 2 * C * s := by
    have hmul : s * (2 * C) < 1 :=
      (lt_div_iff₀ (by positivity : 0 < 2 * C)).mp hsCut
    nlinarith [hmul]
  have hAlgebra : -s * M + s * M / (1 - 2 * C * s) =
      2 * C * s ^ 2 * M / (1 - 2 * C * s) := by
    let d : ℝ := 1 - 2 * C * s
    have hdpos : 0 < d := by dsimp [d]; exact hDen
    have hdne : d ≠ 0 := ne_of_gt hdpos
    have hinv : d * d⁻¹ = 1 := mul_inv_cancel₀ hdne
    have hrelation : 1 - d = 2 * C * s := by dsimp [d]; ring
    have hdiff : d⁻¹ - 1 = (2 * C * s) * d⁻¹ := by
      calc
        d⁻¹ - 1 = d⁻¹ - d * d⁻¹ := by rw [hinv]
        _ = (1 - d) * d⁻¹ := by ring
        _ = (2 * C * s) * d⁻¹ := by rw [hrelation]
    change -s * M + s * M / d = 2 * C * s ^ 2 * M / d
    calc
      -s * M + s * M / d = s * M * (d⁻¹ - 1) := by
        rw [div_eq_mul_inv]
        ring
      _ = s * M * ((2 * C * s) * d⁻¹) := by rw [hdiff]
      _ = 2 * C * s ^ 2 * M / d := by
        rw [div_eq_mul_inv]
        ring
  refine ⟨hCenteredInt, ?_⟩
  rw [hLogEq]
  calc
    -s * M + Real.log (∫ D, Real.exp (s * Q D) ∂ν) ≤
        -s * M + s * M / (1 - 2 * C * s) := by linarith [hLogBase]
    _ = 2 * C * s ^ 2 * M / (1 - 2 * C * s) := hAlgebra

end

end LOOConcentration

#print axioms LOOConcentration.datasetNormSq_exp_logMGF_le_of_product_entropy
#print axioms LOOConcentration.centered_datasetNormSq_logMGF_le_of_product_entropy
