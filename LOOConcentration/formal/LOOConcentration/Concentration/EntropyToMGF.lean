import LOOConcentration.Concentration.EntropyAbsorption
import LOOConcentration.Concentration.EntropyCalculus
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-!
# From tilted entropy to a centered log-partition bound

The real-variable argument integrates the derivative of the quotient
`(ψ t) / t`. Dataset corollaries keep the entropy, moment, and log-Sobolev
inputs explicit while using the bounded-observable derivative formulas.
-/

set_option autoImplicit false

open MeasureTheory
open Filter
open scoped Topology

namespace LOOConcentration

noncomputable section

/-- A one-sided entropy differential bound controls the centered function. -/
theorem centered_log_mgf_le_of_entropy_bound
    {ψ : ℝ → ℝ} {m V Λ t : ℝ}
    (hψ0 : ψ 0 = 0)
    (hderiv0 : HasDerivAt ψ m 0)
    (hDiff : ∀ x, DifferentiableAt ℝ ψ x)
    (hEntropy : ∀ x, 0 < x → x ≤ Λ →
      x * deriv ψ x - ψ x ≤ V * x ^ 2)
    (ht : 0 ≤ t) (htΛ : t ≤ Λ) :
    ψ t - t * m ≤ V * t ^ 2 := by
  by_cases ht0 : t = 0
  · simp [ht0, hψ0]
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  let q : ℝ → ℝ := (ψ / id) - fun _ => m
  have hqLimit : Tendsto q (𝓝[>] 0) (𝓝 0) := by
    have hslope := hderiv0.tendsto_slope.mono_left (nhdsGT_le_nhdsNE 0)
    have hslope' := hslope.sub_const m
    have hEq : q =ᶠ[𝓝[>] 0] fun x => slope ψ 0 x - m := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hxne : x ≠ 0 := ne_of_gt hx
      simp [q, slope_def_field, hψ0]
    have hlimit : Tendsto (fun x => slope ψ 0 x - m) (𝓝[>] 0) (𝓝 0) := by
      simpa using hslope'
    exact Tendsto.congr' hEq.symm hlimit
  have hqDiff : ∀ x, x ≠ 0 → DifferentiableAt ℝ q x := by
    intro x hx
    dsimp [q]
    exact DifferentiableAt.sub_const
      (DifferentiableAt.div (hDiff x) differentiableAt_id hx) m
  have hqDeriv : ∀ x, x ≠ 0 →
      deriv q x = (x * deriv ψ x - ψ x) / x ^ 2 := by
    intro x hx
    have hdiv := deriv_div (hDiff x) differentiableAt_id hx
    have hquotDiff := DifferentiableAt.div (hDiff x) differentiableAt_id hx
    have hdiv' : deriv (ψ / id) x =
        (deriv ψ x * x - ψ x) / x ^ 2 := by
      simpa using hdiv
    change deriv ((ψ / id) - fun _ => m) x = _
    rw [deriv_sub hquotDiff (differentiableAt_const m), deriv_const, sub_zero, hdiv']
    ring
  have hqDerivBound : ∀ x, 0 < x → x < t → deriv q x ≤ V := by
    intro x hx hxt
    have hxΛ : x ≤ Λ := (le_of_lt hxt).trans htΛ
    have hx2 : 0 < x ^ 2 := sq_pos_of_pos hx
    rw [hqDeriv x (ne_of_gt hx)]
    exact (div_le_iff₀ hx2).2 (hEntropy x hx hxΛ)
  have hqFinal : q t ≤ V * t := by
    have hEventually : ∀ᶠ e in 𝓝[>] 0, e < t := by
      filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (Iio_mem_nhds htpos)] with e het
      exact het
    have hsecant : ∀ᶠ e in 𝓝[>] 0,
        q t ≤ q e + V * (t - e) := by
      filter_upwards [self_mem_nhdsWithin, hEventually] with e he0 het
      have hmvt := exists_deriv_eq_slope q het
        (fun x hx => (hqDiff x (ne_of_gt (lt_of_lt_of_le he0 hx.1))).continuousAt.continuousWithinAt)
        (fun x hx => (hqDiff x (ne_of_gt (lt_trans he0 hx.1))).differentiableWithinAt)
      obtain ⟨c, hc, hderiv⟩ := hmvt
      have hcpos : 0 < c := lt_trans he0 hc.1
      have hderiv_le : deriv q c ≤ V := hqDerivBound c hcpos hc.2
      have hquotient : (q t - q e) / (t - e) ≤ V := by
        rw [← hderiv]
        exact hderiv_le
      have hcross := (div_le_iff₀ (sub_pos.mpr het)).mp hquotient
      linarith
    have hid : Tendsto (fun e : ℝ => e) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hlinear : Tendsto (fun e : ℝ => V * (t - e))
        (𝓝[>] 0) (𝓝 (V * t)) := by
      simpa using (tendsto_const_nhds.sub hid).const_mul V
    have hsum : Tendsto (fun e : ℝ => q e + V * (t - e))
        (𝓝[>] 0) (𝓝 (V * t)) := by
      simpa only [zero_add] using hqLimit.add hlinear
    exact ge_of_tendsto hsum hsecant
  have hqRewrite : q t = (ψ t - t * m) / t := by
    dsimp [q]
    field_simp [ne_of_gt htpos]
  rw [hqRewrite] at hqFinal
  have hmul := (div_le_iff₀ htpos).mp hqFinal
  nlinarith

/-- The same estimate on both sides of zero, using `ψ (-t)` on the negative side. -/
theorem centered_log_mgf_le_of_abs_entropy_bound
    {ψ : ℝ → ℝ} {m V Λ t : ℝ}
    (hψ0 : ψ 0 = 0)
    (hderiv0 : HasDerivAt ψ m 0)
    (hDiff : ∀ x, DifferentiableAt ℝ ψ x)
    (hEntropy : ∀ x, 0 < |x| → |x| ≤ Λ →
      x * deriv ψ x - ψ x ≤ V * x ^ 2)
    (ht : |t| ≤ Λ) :
    ψ t - t * m ≤ V * t ^ 2 := by
  by_cases htnonneg : 0 ≤ t
  · exact centered_log_mgf_le_of_entropy_bound hψ0 hderiv0 hDiff
      (fun x hx hxΛ => hEntropy x (abs_pos.mpr (ne_of_gt hx))
        (by simpa [abs_of_pos hx] using hxΛ))
      htnonneg (by simpa [abs_of_nonneg htnonneg] using ht)
  have htneg : t < 0 := lt_of_not_ge htnonneg
  let ψneg : ℝ → ℝ := fun x => ψ (-x)
  have hψneg0 : ψneg 0 = 0 := by simp [ψneg, hψ0]
  have hderivneg : HasDerivAt ψneg (-m) 0 := by
    have hOuter : HasDerivAt ψ m (Neg.neg (0 : ℝ)) := by simpa using hderiv0
    have hcomp := hOuter.comp 0 (hasDerivAt_neg 0)
    simpa [ψneg, Function.comp_def] using hcomp
  have hDiffNeg : ∀ x, DifferentiableAt ℝ ψneg x := by
    intro x
    exact (hDiff (-x)).comp x (hasDerivAt_neg x).differentiableAt
  have hEntropyNeg : ∀ x, 0 < x → x ≤ Λ →
      x * deriv ψneg x - ψneg x ≤ V * x ^ 2 := by
    intro x hx hxΛ
    have hnegAbs : |(-x : ℝ)| = x := by simp [abs_of_pos hx]
    have hSource := hEntropy (-x) (by rw [hnegAbs]; exact hx)
      (by rw [hnegAbs]; exact hxΛ)
    have hcomp := (hDiff (-x)).hasDerivAt.comp x (hasDerivAt_neg x)
    have hderivEq : deriv ψneg x = -deriv ψ (-x) := by
      simpa [ψneg, Function.comp_def] using hcomp.deriv
    calc
      x * deriv ψneg x - ψneg x =
          (-x) * deriv ψ (-x) - ψ (-x) := by
            rw [hderivEq]
            simp only [ψneg]
            ring
      _ ≤ V * (-x) ^ 2 := hSource
      _ = V * x ^ 2 := by ring
  have hnegBound := centered_log_mgf_le_of_entropy_bound
    (ψ := ψneg) (m := -m) (V := V) (Λ := Λ) (t := -t)
    hψneg0 hderivneg hDiffNeg hEntropyNeg (le_of_lt (neg_pos.mpr htneg))
    (by simpa [abs_of_neg htneg] using ht)
  simpa [ψneg] using hnegBound

private theorem tiltEntropy_eq_logPartitionLog_deriv
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F : Ω → ℝ} (hFmeas : Measurable F) {B t : ℝ}
    (hB : 0 ≤ B) (hF : ∀ ω, |F ω| ≤ B) :
    tiltEntropy μ F t =
      t * deriv (logPartitionLog μ F) t - logPartitionLog μ F t := by
  have hMean :
      (∫ ω, tiltDensity μ F t ω * F ω ∂μ) =
        (∫ ω, F ω * Real.exp (t * F ω) ∂μ) /
          logPartition μ F t := by
    calc
      (∫ ω, tiltDensity μ F t ω * F ω ∂μ) =
          ∫ ω, (F ω * Real.exp (t * F ω)) *
            (logPartition μ F t)⁻¹ ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with ω
        simp [tiltDensity, tiltPartition, logPartition, div_eq_mul_inv]
        ring
      _ = (∫ ω, F ω * Real.exp (t * F ω) ∂μ) *
            (logPartition μ F t)⁻¹ := integral_mul_const _ _
      _ = _ := by rw [div_eq_mul_inv]
  rw [tiltEntropy_eq_tiltMean_sub_logPartition hFmeas hB hF, hMean,
    logPartitionLog_deriv hFmeas hB hF]
  rfl

/-- A bounded observable inherits a centered log-partition bound from its
tilted-entropy bound. The entropy hypothesis is an explicit predecessor. -/
theorem boundedObservable_logPartitionLog_centered_of_entropy_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F : Ω → ℝ} (hFmeas : Measurable F) {B V Λ t : ℝ}
    (hB : 0 ≤ B) (hF : ∀ ω, |F ω| ≤ B)
    (hEntropy : ∀ u, 0 < |u| → |u| ≤ Λ →
      tiltEntropy μ F u ≤ V * u ^ 2)
    (ht : |t| ≤ Λ) :
    logPartitionLog μ F t - t * (∫ ω, F ω ∂μ) ≤ V * t ^ 2 := by
  let ψ : ℝ → ℝ := logPartitionLog μ F
  have hZ0 : logPartition μ F 0 = 1 := by
    simp [logPartition]
  have hψ0 : ψ 0 = 0 := by simp [ψ, logPartitionLog, hZ0]
  have hderiv0 : HasDerivAt ψ (∫ ω, F ω ∂μ) 0 := by
    have h := logPartitionLog_hasDerivAt (μ := μ) (F := F)
      hFmeas (B := B) (t := 0) hB hF
    simpa [ψ, hZ0] using h
  have hDiff : ∀ x, DifferentiableAt ℝ ψ x := by
    intro x
    exact (logPartitionLog_hasDerivAt (μ := μ) (F := F)
      hFmeas (B := B) (t := x) hB hF).differentiableAt
  have hDifferential : ∀ u, 0 < |u| → |u| ≤ Λ →
      u * deriv ψ u - ψ u ≤ V * u ^ 2 := by
    intro u hu huΛ
    have hEq := tiltEntropy_eq_logPartitionLog_deriv
      (μ := μ) (F := F) hFmeas hB hF (t := u)
    have h := hEntropy u hu huΛ
    rw [← hEq]
    exact h
  exact centered_log_mgf_le_of_abs_entropy_bound hψ0 hderiv0 hDiff
    hDifferential ht

/-- Positive-gradient dataset specialization. Its four universal families of
inputs are the finite norm moment, finite tilted norm moment, product-LSI
entropy estimate, and norm log-MGF estimate needed by wave 3. -/
theorem datasetNormSq_logPartitionLog_centered_positive_b
    {k m n : ℕ} {μ : Measure (Dataset (Observation k m) n)}
    [IsProbabilityMeasure μ] (F : Dataset (Observation k m) n → ℝ)
    (hFmeas : Measurable F) {B C b a M2 : ℝ} (r : ℕ)
    (hB : 0 ≤ B) (hF : ∀ D, |F D| ≤ B)
    (hC : 0 < C) (hb : 0 < b) (ha : 0 ≤ a) (hM2 : 0 ≤ M2)
    (hNormExp : ∀ u, 0 < |u| → |u| ≤ 1 / (4 * C * b) → Integrable
      (fun D => Real.exp ((2 * C * u ^ 2 * b ^ 2) * datasetNormSq D)) μ)
    (hTiltMoment : ∀ u, 0 < |u| → |u| ≤ 1 / (4 * C * b) → Integrable
      (fun D => tiltDensity μ F u D * datasetNormSq D) μ)
    (hProductLSI : ∀ u, 0 < |u| → |u| ≤ 1 / (4 * C * b) →
      tiltEntropy μ F u ≤ C * u ^ 2 *
        (a ^ 2 + b ^ 2 *
          (∫ D, tiltDensity μ F u D * datasetNormSq D ∂μ)))
    (hNormMGF : ∀ u, 0 < |u| → |u| ≤ 1 / (4 * C * b) →
      Real.log
        (∫ D, Real.exp ((2 * C * u ^ 2 * b ^ 2) * datasetNormSq D) ∂μ) ≤
          ((2 * C * u ^ 2 * b ^ 2) * (r : ℝ) * M2) /
            (1 - 2 * C * (2 * C * u ^ 2 * b ^ 2)))
    {t : ℝ} (ht : |t| ≤ 1 / (4 * C * b)) :
    logPartitionLog μ F t - t * (∫ D, F D ∂μ) ≤
      2 * C * (a ^ 2 + 2 * b ^ 2 * (r : ℝ) * M2) * t ^ 2 := by
  have hEntropy : ∀ u, 0 < |u| → |u| ≤ 1 / (4 * C * b) →
      tiltEntropy μ F u ≤
        (2 * C * (a ^ 2 + 2 * b ^ 2 * (r : ℝ) * M2)) * u ^ 2 := by
    intro u hu huCut
    have hAbsorption := datasetNormSq_entropy_absorption
      (μ := μ) (F := F) hFmeas (B := B) (C := C) (b := b) (a := a)
      (M2 := M2) (lam := u) (s := 2 * C * u ^ 2 * b ^ 2) r
      hB hF hC hb ha hM2 hu huCut rfl
      (hNormExp u hu huCut) (hTiltMoment u hu huCut) (hProductLSI u hu huCut)
      (hNormMGF u hu huCut)
    calc
      tiltEntropy μ F u ≤
          2 * C * u ^ 2 * (a ^ 2 + 2 * b ^ 2 * (r : ℝ) * M2) := hAbsorption
      _ = (2 * C * (a ^ 2 + 2 * b ^ 2 * (r : ℝ) * M2)) * u ^ 2 := by ring
  exact boundedObservable_logPartitionLog_centered_of_entropy_bound
    hFmeas (B := B) (V := 2 * C * (a ^ 2 + 2 * b ^ 2 * (r : ℝ) * M2))
    (Λ := 1 / (4 * C * b)) (t := t) hB hF hEntropy ht

/-- Bounded-gradient dataset specialization. The product-LSI entropy estimate
is explicit and applies for every nonzero parameter, so the symmetric
calculus theorem gives the result for every real parameter. -/
theorem datasetNormSq_logPartitionLog_centered_bounded_gradient
    {k m n : ℕ} {μ : Measure (Dataset (Observation k m) n)}
    [IsProbabilityMeasure μ] (F : Dataset (Observation k m) n → ℝ)
    (hFmeas : Measurable F) {B C a : ℝ}
    (hB : 0 ≤ B) (hF : ∀ D, |F D| ≤ B)
    (hProductLSI : ∀ u, 0 < |u| →
      tiltEntropy μ F u ≤ (C * a ^ 2 / 2) * u ^ 2)
    (t : ℝ) :
    logPartitionLog μ F t - t * (∫ D, F D ∂μ) ≤
      (C * a ^ 2 / 2) * t ^ 2 := by
  have htBound : |t| ≤ |t| + 1 := by linarith
  have h := boundedObservable_logPartitionLog_centered_of_entropy_bound
    hFmeas (B := B) (V := C * a ^ 2 / 2) (Λ := |t| + 1) (t := t)
    hB hF (fun u hu _ => hProductLSI u hu) htBound
  exact h

end
end LOOConcentration
