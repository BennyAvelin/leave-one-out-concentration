import LOOConcentration.Concentration.NormTruncationTest
import LOOConcentration.Concentration.EntropyCalculus
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-!
# Scalar norm-entropy ODE and the bounded truncation specialization

The scalar estimate uses the differential inequality produced by the norm
entropy calculation. The dataset specialization leaves the product-LSI output
and squared-slope measurability visible as explicit predecessors.

Source: [arXiv:2211.02478](https://arxiv.org/abs/2211.02478) (historical audit version),
-/

set_option autoImplicit false

open Filter MeasureTheory
open scoped Topology

namespace LOOConcentration

noncomputable section

/-- Integrating the norm-entropy differential inequality gives the sharp
positive-parameter log-MGF bound. -/
theorem normEntropyODE_scalar_bound
    {ψ : ℝ → ℝ} {C m t : ℝ}
    (hC : 0 < C)
    (hψ0 : ψ 0 = 0)
    (hderiv0 : HasDerivAt ψ m 0)
    (hDiff : ∀ x, DifferentiableAt ℝ ψ x)
    (hODE : ∀ s, 0 < s → s < 1 / (2 * C) →
      s * deriv ψ s - ψ s ≤ 2 * C * s ^ 2 * deriv ψ s)
    (ht : 0 ≤ t) (htCut : t < 1 / (2 * C)) :
    ψ t ≤ t * m / (1 - 2 * C * t) := by
  by_cases ht0 : t = 0
  · simp [ht0, hψ0]
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  let q : ℝ → ℝ := fun x => ψ x / x - 2 * C * ψ x
  have hqLimit : Tendsto q (𝓝[>] 0) (𝓝 m) := by
    have hslope := hderiv0.tendsto_slope.mono_left (nhdsGT_le_nhdsNE 0)
    have hψtendsto : Tendsto ψ (𝓝 0) (𝓝 0) := by
      simpa [hψ0] using hderiv0.continuousAt.tendsto
    have hψwithin : Tendsto ψ (𝓝[>] 0) (𝓝 0) :=
      hψtendsto.mono_left nhdsWithin_le_nhds
    have hterm : Tendsto (fun x => 2 * C * ψ x) (𝓝[>] 0) (𝓝 0) := by
      simpa using tendsto_const_nhds.mul hψwithin
    have hlimit : Tendsto (fun x => slope ψ 0 x - 2 * C * ψ x)
        (𝓝[>] 0) (𝓝 m) := by
      simpa using hslope.sub hterm
    have hEq : q =ᶠ[𝓝[>] 0] fun x => slope ψ 0 x - 2 * C * ψ x := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      simp [q, slope_def_field, hψ0]
    exact Tendsto.congr' hEq.symm hlimit
  have hqDiff : ∀ x, x ≠ 0 → DifferentiableAt ℝ q x := by
    intro x hx
    dsimp [q]
    exact (DifferentiableAt.div (hDiff x) differentiableAt_id hx).sub
      ((hDiff x).const_mul (2 * C))
  have hqDeriv : ∀ x, x ≠ 0 →
      deriv q x =
        ((x * deriv ψ x - ψ x) - 2 * C * x ^ 2 * deriv ψ x) / x ^ 2 := by
    intro x hx
    have hquotDiff := DifferentiableAt.div (hDiff x) differentiableAt_id hx
    have hmulDiff : DifferentiableAt ℝ (fun y => 2 * C * ψ y) x :=
      (hDiff x).const_mul (2 * C)
    have hdiv : deriv (ψ / id) x =
        (deriv ψ x * x - ψ x) / x ^ 2 := by
      simpa using deriv_div (hDiff x) differentiableAt_id hx
    change deriv ((ψ / id) - fun y => 2 * C * ψ y) x = _
    rw [deriv_sub hquotDiff hmulDiff, deriv_const_mul_field, hdiv]
    field_simp [hx]
  have hqDerivNonpos : ∀ x, 0 < x → x < 1 / (2 * C) → deriv q x ≤ 0 := by
    intro x hx hxCut
    have hODEx := hODE x hx hxCut
    have hx2 : 0 < x ^ 2 := sq_pos_of_pos hx
    have hnum :
        (x * deriv ψ x - ψ x) - 2 * C * x ^ 2 * deriv ψ x ≤ 0 := by
      nlinarith [hODEx]
    rw [hqDeriv x (ne_of_gt hx)]
    exact div_nonpos_of_nonpos_of_nonneg hnum hx2.le
  have hqFinal : q t ≤ m := by
    have hEventually : ∀ᶠ e in 𝓝[>] 0, e < t := by
      filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (Iio_mem_nhds htpos)] with e he
      exact he
    have hsecant : ∀ᶠ e in 𝓝[>] 0, q t ≤ q e := by
      filter_upwards [self_mem_nhdsWithin, hEventually] with e he0 het
      have hmvt := exists_deriv_eq_slope q het
        (fun x hx => (hqDiff x (ne_of_gt (lt_of_lt_of_le he0 hx.1))).continuousAt.continuousWithinAt)
        (fun x hx => (hqDiff x (ne_of_gt (lt_trans he0 hx.1))).differentiableWithinAt)
      obtain ⟨c, hc, hderiv⟩ := hmvt
      have hcpos : 0 < c := lt_trans he0 hc.1
      have hcCut : c < 1 / (2 * C) := lt_trans hc.2 htCut
      have hderiv_nonpos : deriv q c ≤ 0 := hqDerivNonpos c hcpos hcCut
      have hquotient : (q t - q e) / (t - e) ≤ 0 := by
        rw [← hderiv]
        exact hderiv_nonpos
      have hcross := (div_le_iff₀ (sub_pos.mpr het)).mp hquotient
      linarith
    exact ge_of_tendsto hqLimit hsecant
  have hden : 0 < 1 - 2 * C * t := by
    have hmul : t * (2 * C) < 1 :=
      (lt_div_iff₀ (by positivity : 0 < 2 * C)).mp htCut
    nlinarith [hmul]
  have hqRewrite : q t * t = ψ t * (1 - 2 * C * t) := by
    dsimp [q]
    field_simp [ne_of_gt htpos]
  have hcross : ψ t * (1 - 2 * C * t) ≤ t * m := by
    have hmul := mul_le_mul_of_nonneg_right hqFinal ht
    rw [hqRewrite] at hmul
    simpa [mul_comm] using hmul
  exact (le_div_iff₀ hden).2 (by simpa [mul_comm] using hcross)

/-- The truncated squared-norm log-MGF bound, conditional on the actual
product-LSI entropy output and on measurability of the limsup-defined squared
local slope. The latter is used only to obtain finite slope energy from the
reviewed pointwise majorant. -/
theorem normTruncation_logPartitionLog_le_of_product_entropy
    {k m n : ℕ} (μ : Measure (Observation (k + 1) (m + 1)))
    [IsProbabilityMeasure μ] {A C : ℝ} (hA : 0 < A) (hC : 0 < C)
    (hSlopeMeas : ∀ s (hs : 0 ≤ s),
      AEStronglyMeasurable
        (fun D : Dataset (Observation (k + 1) (m + 1)) (n + 1) =>
          datasetLocalSlope (normTruncationExpTest
            (k := k) (m := m) (n := n) hA s hs) D ^ 2)
        (Measure.pi fun _ : Fin (n + 1) => μ))
    (hProductEntropy : ∀ s (hs : 0 ≤ s),
      Integrable
        (fun D : Dataset (Observation (k + 1) (m + 1)) (n + 1) =>
          datasetLocalSlope (normTruncationExpTest
            (k := k) (m := m) (n := n) hA s hs) D ^ 2)
        (Measure.pi fun _ : Fin (n + 1) => μ) →
      looconcentrationEntropy (Measure.pi fun _ : Fin (n + 1) => μ)
        (fun D => Real.exp (s * normTruncation A hA D)) ≤
        2 * C * ∫ D : Dataset (Observation (k + 1) (m + 1)) (n + 1),
          datasetLocalSlope (normTruncationExpTest
            (k := k) (m := m) (n := n) hA s hs) D ^ 2
            ∂Measure.pi (fun _ : Fin (n + 1) => μ))
    {t : ℝ} (ht : 0 ≤ t) (htCut : t < 1 / (2 * C)) :
    logPartitionLog (Measure.pi fun _ : Fin (n + 1) => μ)
        (normTruncation A hA) t ≤
      t * (∫ D : Dataset (Observation (k + 1) (m + 1)) (n + 1),
        normTruncation A hA D ∂Measure.pi (fun _ : Fin (n + 1) => μ)) /
        (1 - 2 * C * t) := by
  let ν : Measure (Dataset (Observation (k + 1) (m + 1)) (n + 1)) :=
    Measure.pi fun _ : Fin (n + 1) => μ
  let Q : Dataset (Observation (k + 1) (m + 1)) (n + 1) → ℝ := normTruncation A hA
  let ψ : ℝ → ℝ := logPartitionLog ν Q
  have hQmeas : Measurable Q := by
    exact (normTruncation_contDiff A hA).continuous.measurable
  have hQbound : ∀ D, |Q D| ≤ A := by
    intro D
    rw [abs_of_nonneg (normTruncation_nonneg hA D)]
    exact normTruncation_le hA D
  have hZ0 : logPartition ν Q 0 = 1 := by
    simp [logPartition]
  have hψ0 : ψ 0 = 0 := by
    simp [ψ, logPartitionLog, hZ0]
  have hderiv0 : HasDerivAt ψ (∫ D, Q D ∂ν) 0 := by
    have h := logPartitionLog_hasDerivAt (μ := ν) (F := Q)
      hQmeas (B := A) (t := 0) hA.le hQbound
    simpa [ψ, hZ0, logPartition] using h
  have hDiff : ∀ s, DifferentiableAt ℝ ψ s := by
    intro s
    exact (logPartitionLog_hasDerivAt (μ := ν) (F := Q)
      hQmeas (B := A) (t := s) hA.le hQbound).differentiableAt
  have hODE : ∀ s, 0 < s → s < 1 / (2 * C) →
      s * deriv ψ s - ψ s ≤ 2 * C * s ^ 2 * deriv ψ s := by
    intro s hs hsCut
    let U := normTruncationExpTest (k := k) (m := m) (n := n) hA s hs.le
    have hSlopeInt : Integrable
        (fun D : Dataset (Observation (k + 1) (m + 1)) (n + 1) =>
          datasetLocalSlope U D ^ 2) ν := by
      exact integrable_normTruncationExpTest_slope_sq_of_aestronglyMeasurable
        μ hA s hs.le (hSlopeMeas s hs.le)
    have hSlopePoint : ∀ D : Dataset (Observation (k + 1) (m + 1)) (n + 1),
        datasetLocalSlope U D ^ 2 ≤
          s ^ 2 * Real.exp (s * Q D) * Q D := by
      intro D
      simpa [U, Q] using normTruncationExpTest_slope_sq_le hA s hs.le D
    have hMajorInt : Integrable
        (fun D : Dataset (Observation (k + 1) (m + 1)) (n + 1) =>
          s ^ 2 * Real.exp (s * Q D) * Q D) ν := by
      have hBase := logPartition_derivative_integrable (μ := ν) (F := Q)
        hQmeas (B := A) (t := s) hA.le hQbound
      have hscaled := hBase.const_mul (s ^ 2)
      refine hscaled.congr ?_
      filter_upwards with D
      ring
    have hEnergy := integral_mono hSlopeInt hMajorInt hSlopePoint
    have hEnergyEq :
        (∫ D : Dataset (Observation (k + 1) (m + 1)) (n + 1),
          s ^ 2 * Real.exp (s * Q D) * Q D ∂ν) =
          s ^ 2 * ∫ D, Q D * Real.exp (s * Q D) ∂ν := by
      calc
        _ = ∫ D, s ^ 2 * (Q D * Real.exp (s * Q D)) ∂ν := by
          apply integral_congr_ae
          filter_upwards with D
          ring
        _ = s ^ 2 * ∫ D, Q D * Real.exp (s * Q D) ∂ν := integral_const_mul _ _
    have hEntropy : looconcentrationEntropy ν (fun D => Real.exp (s * Q D)) ≤
        2 * C * (s ^ 2 * ∫ D, Q D * Real.exp (s * Q D) ∂ν) := by
      calc
        _ ≤ 2 * C * ∫ D, datasetLocalSlope U D ^ 2 ∂ν := by
          exact hProductEntropy s hs.le hSlopeInt
        _ ≤ 2 * C * (s ^ 2 * ∫ D, Q D * Real.exp (s * Q D) ∂ν) := by
          rw [← hEnergyEq]
          exact mul_le_mul_of_nonneg_left hEnergy (by positivity)
    have hderiv : deriv ψ s =
        (∫ D, Q D * Real.exp (s * Q D) ∂ν) / logPartition ν Q s := by
      simpa [ψ] using logPartitionLog_deriv (μ := ν) (F := Q)
        hQmeas (B := A) (t := s) hA.le hQbound
    have hZpos : 0 < logPartition ν Q s :=
      logPartition_pos (μ := ν) (F := Q) hQmeas (B := A) (t := s) hQbound
    have hEntropyRatio :
        looconcentrationEntropy ν (fun D => Real.exp (s * Q D)) /
            logPartition ν Q s ≤ 2 * C * s ^ 2 * deriv ψ s := by
      calc
        _ ≤ (2 * C * (s ^ 2 * ∫ D, Q D * Real.exp (s * Q D) ∂ν)) /
            logPartition ν Q s :=
              div_le_div_of_nonneg_right hEntropy hZpos.le
        _ = 2 * C * s ^ 2 * deriv ψ s := by
          rw [hderiv]
          field_simp [ne_of_gt hZpos]
    have hEntropyId := looconcentrationEntropy_exp_eq_logPartition_deriv
      (μ := ν) (F := Q) hQmeas (B := A) (t := s) hA.le hQbound
    rw [← hEntropyId]
    exact hEntropyRatio
  exact normEntropyODE_scalar_bound hC hψ0 hderiv0 hDiff hODE ht htCut

/-- If the truncated norm has zero mean, its nonnegative log-MGF is zero on
the same parameter interval. This records the zero-mean branch of the source
argument explicitly. -/
theorem normTruncation_logPartitionLog_eq_zero_of_mean_eq_zero
    {k m n : ℕ} (μ : Measure (Observation (k + 1) (m + 1)))
    [IsProbabilityMeasure μ] {A C : ℝ} (hA : 0 < A) (hC : 0 < C)
    (hSlopeMeas : ∀ s (hs : 0 ≤ s),
      AEStronglyMeasurable
        (fun D : Dataset (Observation (k + 1) (m + 1)) (n + 1) =>
          datasetLocalSlope (normTruncationExpTest
            (k := k) (m := m) (n := n) hA s hs) D ^ 2)
        (Measure.pi fun _ : Fin (n + 1) => μ))
    (hProductEntropy : ∀ s (hs : 0 ≤ s),
      Integrable
        (fun D : Dataset (Observation (k + 1) (m + 1)) (n + 1) =>
          datasetLocalSlope (normTruncationExpTest
            (k := k) (m := m) (n := n) hA s hs) D ^ 2)
        (Measure.pi fun _ : Fin (n + 1) => μ) →
      looconcentrationEntropy (Measure.pi fun _ : Fin (n + 1) => μ)
        (fun D => Real.exp (s * normTruncation A hA D)) ≤
        2 * C * ∫ D : Dataset (Observation (k + 1) (m + 1)) (n + 1),
          datasetLocalSlope (normTruncationExpTest
            (k := k) (m := m) (n := n) hA s hs) D ^ 2
            ∂Measure.pi (fun _ : Fin (n + 1) => μ))
    {t : ℝ} (ht : 0 ≤ t) (htCut : t < 1 / (2 * C))
    (hMeanZero : (∫ D : Dataset (Observation (k + 1) (m + 1)) (n + 1),
      normTruncation A hA D ∂Measure.pi (fun _ : Fin (n + 1) => μ)) = 0) :
    logPartitionLog (Measure.pi fun _ : Fin (n + 1) => μ)
      (normTruncation A hA) t = 0 := by
  let ν : Measure (Dataset (Observation (k + 1) (m + 1)) (n + 1)) :=
    Measure.pi fun _ : Fin (n + 1) => μ
  let Q : Dataset (Observation (k + 1) (m + 1)) (n + 1) → ℝ := normTruncation A hA
  have hUpper := normTruncation_logPartitionLog_le_of_product_entropy
    μ hA hC hSlopeMeas hProductEntropy ht htCut
  have hUpperZero : logPartitionLog ν Q t ≤ 0 := by
    simpa [ν, Q, hMeanZero] using hUpper
  have hQmeas : Measurable Q := (normTruncation_contDiff A hA).continuous.measurable
  have hQbound : ∀ D, |Q D| ≤ A := by
    intro D
    rw [abs_of_nonneg (normTruncation_nonneg hA D)]
    exact normTruncation_le hA D
  have hZint : Integrable (fun D => Real.exp (t * Q D)) ν :=
    logPartition_integrable (μ := ν) (F := Q) hQmeas (B := A) (t := t) hQbound
  have hLower : 1 ≤ logPartition ν Q t := by
    have hIntegral := integral_mono (integrable_const (1 : ℝ)) hZint (fun D => by
      have hQ := normTruncation_nonneg hA D
      have hexp := Real.add_one_le_exp (t * Q D)
      have hprod : 0 ≤ t * Q D := mul_nonneg ht hQ
      nlinarith)
    simpa [logPartition, integral_const, probReal_univ] using hIntegral
  have hLogLower : 0 ≤ logPartitionLog ν Q t := by
    change 0 ≤ Real.log (logPartition ν Q t)
    have h := Real.log_le_log zero_lt_one hLower
    simpa using h
  have hEq : logPartitionLog ν Q t = 0 := le_antisymm hUpperZero hLogLower
  simpa [ν, Q] using hEq

end

end LOOConcentration
