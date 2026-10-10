import LOOConcentration.Concentration.EntropyCalculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Bounded MGF calculus

This module exports the whole bounded-observable calculus from the existing
`LOOConcentration.Concentration.EntropyCalculus` implementation and adds the
initial-slope limit needed by the revised norm-MGF argument.  Its final
consumer is the source truncation `Q_N(x) = N (1 - exp(-‖x‖²/N))` on a finite
dimensional Euclidean space.
-/

set_option autoImplicit false

open MeasureTheory Filter
open scoped Topology

namespace LOOConcentration.Revision

noncomputable section

/-- A bounded measurable observable has an integrable exponential tilt at
every real parameter. -/
theorem bounded_mgf_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (hYmeas : Measurable Y) {B s : ℝ}
    (hYbound : ∀ x, |Y x| ≤ B) :
    Integrable (fun x => Real.exp (s * Y x)) μ := by
  exact LOOConcentration.logPartition_integrable (μ := μ) (F := Y)
    hYmeas (B := B) (t := s) hYbound

/-- The bounded-observable derivative integrand is integrable at every real
parameter. -/
theorem bounded_mgf_derivative_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (hYmeas : Measurable Y) {B s : ℝ} (hB : 0 ≤ B)
    (hYbound : ∀ x, |Y x| ≤ B) :
    Integrable (fun x => Y x * Real.exp (s * Y x)) μ := by
  exact LOOConcentration.logPartition_derivative_integrable (μ := μ) (F := Y)
    hYmeas (B := B) (t := s) hB hYbound

/-- The exponential partition function of a bounded observable is positive. -/
theorem bounded_mgf_partition_pos {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (hYmeas : Measurable Y) {B s : ℝ}
    (hYbound : ∀ x, |Y x| ≤ B) :
    0 < LOOConcentration.logPartition μ Y s :=
  LOOConcentration.logPartition_pos (μ := μ) (F := Y)
    hYmeas (B := B) (t := s) hYbound

/-- The actual exponential partition function has derivative given by its
bounded-observable moment integral. -/
theorem bounded_mgf_partition_hasDerivAt {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (hYmeas : Measurable Y) {B s : ℝ} (hB : 0 ≤ B)
    (hYbound : ∀ x, |Y x| ≤ B) :
    HasDerivAt (LOOConcentration.logPartition μ Y)
      (∫ x, Y x * Real.exp (s * Y x) ∂μ) s := by
  exact LOOConcentration.logPartition_hasDerivAt (μ := μ) (F := Y)
    hYmeas (B := B) (t := s) hB hYbound

/-- The actual log-partition function has derivative equal to the tilted mean. -/
theorem bounded_mgf_log_hasDerivAt {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (hYmeas : Measurable Y) {B s : ℝ} (hB : 0 ≤ B)
    (hYbound : ∀ x, |Y x| ≤ B) :
    HasDerivAt (LOOConcentration.logPartitionLog μ Y)
      ((∫ x, Y x * Real.exp (s * Y x) ∂μ) /
        LOOConcentration.logPartition μ Y s) s :=
  LOOConcentration.logPartitionLog_hasDerivAt (μ := μ) (F := Y)
    hYmeas (B := B) (t := s) hB hYbound

/-- The log-partition function is zero at the origin for a probability law. -/
theorem bounded_mgf_log_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (Y : Ω → ℝ) :
    LOOConcentration.logPartitionLog μ Y 0 = 0 := by
  have hZ : LOOConcentration.logPartition μ Y 0 = 1 := by
    simp [LOOConcentration.logPartition]
  simp [LOOConcentration.logPartitionLog, hZ]

/-- The punctured-neighborhood initial slope of the actual log-partition
function is the mean of the observable. -/
theorem bounded_mgf_log_initialSlope_ne {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (hYmeas : Measurable Y) {B : ℝ} (hB : 0 ≤ B)
    (hYbound : ∀ x, |Y x| ≤ B) :
    Tendsto
      (fun s : ℝ => LOOConcentration.logPartitionLog μ Y s / s)
      (𝓝[≠] (0 : ℝ)) (𝓝 (∫ x, Y x ∂μ)) := by
  have hZ : LOOConcentration.logPartition μ Y 0 = 1 := by
    simp [LOOConcentration.logPartition]
  have hψ0 : LOOConcentration.logPartitionLog μ Y 0 = 0 := by
    simp [LOOConcentration.logPartitionLog, hZ]
  have hderiv : HasDerivAt (LOOConcentration.logPartitionLog μ Y)
      (∫ x, Y x ∂μ) 0 := by
    have h := LOOConcentration.logPartitionLog_hasDerivAt
      (μ := μ) (F := Y) hYmeas (B := B) (t := 0) hB hYbound
    simpa [hZ] using h
  have hslope := hderiv.tendsto_slope_zero
  simpa [hψ0, smul_eq_mul, div_eq_mul_inv, mul_comm] using hslope

/-- The right-hand initial slope of the actual log-partition function is the
mean of the observable. -/
theorem bounded_mgf_log_initialSlope {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (hYmeas : Measurable Y) {B : ℝ} (hB : 0 ≤ B)
    (hYbound : ∀ x, |Y x| ≤ B) :
    Tendsto
      (fun s : ℝ => LOOConcentration.logPartitionLog μ Y s / s)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x, Y x ∂μ)) :=
  (bounded_mgf_log_initialSlope_ne (μ := μ) Y hYmeas hB hYbound).mono_left
    (nhdsGT_le_nhdsNE 0)

/-- The normalized entropy of a bounded exponential tilt is the exact
log-partition derivative expression. -/
theorem bounded_mgf_entropy_identity {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (hYmeas : Measurable Y) {B s : ℝ} (hB : 0 ≤ B)
    (hYbound : ∀ x, |Y x| ≤ B) :
    LOOConcentration.looconcentrationEntropy μ
        (fun x => Real.exp (s * Y x)) /
      LOOConcentration.logPartition μ Y s =
        s * deriv (LOOConcentration.logPartitionLog μ Y) s -
          LOOConcentration.logPartitionLog μ Y s :=
  LOOConcentration.looconcentrationEntropy_exp_eq_logPartition_deriv
    (μ := μ) (F := Y) hYmeas (B := B) (t := s) hB hYbound

private theorem qNormCap_nonneg {r N : ℕ} (hN : 0 < N)
    (x : EuclideanSpace ℝ (Fin r)) :
    0 ≤ (N : ℝ) * (1 - Real.exp (-(‖x‖ ^ 2) / (N : ℝ))) := by
  have hNreal : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have harg : -(‖x‖ ^ 2) / (N : ℝ) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (sq_nonneg ‖x‖)) hNreal.le
  have hexp : Real.exp (-(‖x‖ ^ 2) / (N : ℝ)) ≤ 1 := by
    calc
      Real.exp (-(‖x‖ ^ 2) / (N : ℝ)) ≤ Real.exp 0 :=
        Real.exp_le_exp.mpr harg
      _ = 1 := Real.exp_zero
  exact mul_nonneg hNreal.le (sub_nonneg.mpr hexp)

private theorem qNormCap_le {r N : ℕ} (hN : 0 < N)
    (x : EuclideanSpace ℝ (Fin r)) :
    (N : ℝ) * (1 - Real.exp (-(‖x‖ ^ 2) / (N : ℝ)) ) ≤ (N : ℝ) := by
  have hNreal : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hfactor : 1 - Real.exp (-(‖x‖ ^ 2) / (N : ℝ)) ≤ 1 :=
    sub_le_self 1 (Real.exp_nonneg _)
  calc
    (N : ℝ) * (1 - Real.exp (-(‖x‖ ^ 2) / (N : ℝ))) ≤ (N : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hfactor hNreal.le
    _ = (N : ℝ) := by ring

private theorem qNormCap_measurable {r N : ℕ} :
    Measurable (fun x : EuclideanSpace ℝ (Fin r) =>
      (N : ℝ) * (1 - Real.exp (-(‖x‖ ^ 2) / (N : ℝ)))) := by
  have hNorm : Continuous (fun x : EuclideanSpace ℝ (Fin r) => ‖x‖) :=
    continuous_norm
  have hNormSq : Continuous (fun x : EuclideanSpace ℝ (Fin r) => ‖x‖ ^ 2) :=
    hNorm.pow 2
  have hArg : Continuous (fun x : EuclideanSpace ℝ (Fin r) =>
      -(‖x‖ ^ 2) / (N : ℝ)) :=
    (continuous_neg.comp hNormSq).div_const (N : ℝ)
  exact (continuous_const.mul
    (continuous_const.sub (Real.continuous_exp.comp hArg))).measurable

/-- The actual source truncation `Q_N` has the bounded-MGF partition
derivative, with its measurability and cap proved on the concrete Euclidean
carrier. -/
theorem bounded_Q_norm_cap_partition_hasDerivAt {r N : ℕ}
    {μ : Measure (EuclideanSpace ℝ (Fin r))} [IsProbabilityMeasure μ]
    (hN : 0 < N) (s : ℝ) :
    HasDerivAt
      (LOOConcentration.logPartition μ
        (fun x : EuclideanSpace ℝ (Fin r) =>
          (N : ℝ) * (1 - Real.exp (-(‖x‖ ^ 2) / (N : ℝ)))))
      (∫ x,
        ((N : ℝ) * (1 - Real.exp (-(‖x‖ ^ 2) / (N : ℝ)))) *
          Real.exp
            (s * ((N : ℝ) * (1 - Real.exp (-(‖x‖ ^ 2) / (N : ℝ)))) ) ∂μ) s := by
  have hmeas := qNormCap_measurable (r := r) (N := N)
  have hbound : ∀ x : EuclideanSpace ℝ (Fin r),
      |(N : ℝ) * (1 - Real.exp (-(‖x‖ ^ 2) / (N : ℝ)))| ≤ (N : ℝ) := by
    intro x
    rw [abs_of_nonneg (qNormCap_nonneg hN x)]
    exact qNormCap_le hN x
  have hB : 0 ≤ (N : ℝ) := (Nat.cast_pos.mpr hN).le
  exact bounded_mgf_partition_hasDerivAt
    (μ := μ)
    (Y := fun x : EuclideanSpace ℝ (Fin r) =>
      (N : ℝ) * (1 - Real.exp (-(‖x‖ ^ 2) / (N : ℝ))))
    hmeas (B := (N : ℝ)) (s := s) hB hbound

/-- The actual source truncation `Q_N` has initial logarithmic-MGF slope equal
to its own expectation, with all bounded-observable premises discharged on
the finite-dimensional Euclidean carrier. -/
theorem bounded_Q_norm_cap_calculus {r N : ℕ}
    {μ : Measure (EuclideanSpace ℝ (Fin r))} [IsProbabilityMeasure μ]
    (hN : 0 < N) :
    Tendsto
      (fun s : ℝ => LOOConcentration.logPartitionLog μ
        (fun x : EuclideanSpace ℝ (Fin r) =>
          (N : ℝ) * (1 - Real.exp (-(‖x‖ ^ 2) / (N : ℝ)))) s / s)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ x,
        (N : ℝ) * (1 - Real.exp (-(‖x‖ ^ 2) / (N : ℝ))) ∂μ)) := by
  have hmeas := qNormCap_measurable (r := r) (N := N)
  have hbound : ∀ x : EuclideanSpace ℝ (Fin r),
      |(N : ℝ) * (1 - Real.exp (-(‖x‖ ^ 2) / (N : ℝ)))| ≤ (N : ℝ) := by
    intro x
    rw [abs_of_nonneg (qNormCap_nonneg hN x)]
    exact qNormCap_le hN x
  have hB : 0 ≤ (N : ℝ) := (Nat.cast_pos.mpr hN).le
  exact bounded_mgf_log_initialSlope
    (μ := μ)
    (Y := fun x : EuclideanSpace ℝ (Fin r) =>
      (N : ℝ) * (1 - Real.exp (-(‖x‖ ^ 2) / (N : ℝ))))
    hmeas (B := (N : ℝ)) hB hbound

end

end LOOConcentration.Revision
