import LOOConcentration.Concentration.NormEntropyODE
import LOOConcentration.Concentration.EntropyToMGF

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory

/-- Conditional scalar calculus for the actual norm-cap log-MGF. The entropy
inequality is an internal input supplied by the completed-pair LSI consumer. -/
theorem norm_entropy_differential_bound
    {ψ : ℝ → ℝ} {C m t : ℝ} (hC : 0 ≤ C)
    (hψ0 : ψ 0 = 0) (hderiv0 : HasDerivAt ψ m 0)
    (hDiff : ∀ x, DifferentiableAt ℝ ψ x)
    (hODE : ∀ s, 0 < s → 2 * C * s < 1 →
      s * deriv ψ s - ψ s ≤ 2 * C * s ^ 2 * deriv ψ s)
    (ht : 0 ≤ t) (htCut : 2 * C * t < 1) :
    ψ t ≤ t * m / (1 - 2 * C * t) := by
  by_cases hzero : C = 0
  · have hEntropy : ∀ x, 0 < x → x ≤ t →
        x * deriv ψ x - ψ x ≤ (0 : ℝ) * x ^ 2 := by
      intro x hx _
      simpa only [hzero, mul_zero, zero_mul] using hODE x hx (by simp [hzero])
    have h := LOOConcentration.centered_log_mgf_le_of_entropy_bound
      hψ0 hderiv0 hDiff hEntropy ht le_rfl
    simp only [hzero, mul_zero, zero_mul, sub_zero, div_one] at h ⊢
    linarith
  have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hzero)
  have htCut' : t < 1 / (2 * C) :=
    (lt_div_iff₀ (by positivity : 0 < 2 * C)).2 (by simpa only [mul_comm] using htCut)
  apply LOOConcentration.normEntropyODE_scalar_bound hCpos hψ0 hderiv0 hDiff ?_ ht htCut'
  intro s hs hsCut
  apply hODE s hs
  have h := (lt_div_iff₀ (by positivity : 0 < 2 * C)).mp hsCut
  simpa only [mul_comm] using h

/-- Actual bounded-observable consumer. Differentiation, integrability and the
initial mean are internally produced; only the norm-cap entropy output remains
conditional until its same-constant completed LSI producer is applied. -/
theorem bounded_log_mgf_le_of_norm_entropy_bound
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (Y : α → ℝ) (hY : Measurable Y) (B : ℝ) (hB : 0 ≤ B)
    (hBound : ∀ x, |Y x| ≤ B) (C : ℝ) (hC : 0 ≤ C)
    (hEntropy : ∀ s, 0 < s → 2 * C * s < 1 →
      LOOConcentration.looconcentrationEntropy μ (fun x => Real.exp (s * Y x)) ≤
        2 * C * s ^ 2 * ∫ x, Y x * Real.exp (s * Y x) ∂μ)
    (t : ℝ) (ht : 0 ≤ t) (htCut : 2 * C * t < 1) :
    Integrable (fun x => Real.exp (t * Y x)) μ ∧
      Real.log (∫ x, Real.exp (t * Y x) ∂μ) ≤
        t * (∫ x, Y x ∂μ) / (1 - 2 * C * t) := by
  let ψ := LOOConcentration.logPartitionLog μ Y
  have hM0 : LOOConcentration.logPartition μ Y 0 = 1 := by
    simp only [LOOConcentration.logPartition, zero_mul, Real.exp_zero, integral_const,
      probReal_univ, one_smul]
  have hψ0 : ψ 0 = 0 := by
    simp only [ψ, LOOConcentration.logPartitionLog, Function.comp_apply, hM0, Real.log_one]
  have hderiv0 : HasDerivAt ψ (∫ x, Y x ∂μ) 0 := by
    have h := LOOConcentration.logPartitionLog_hasDerivAt (μ := μ) (F := Y)
      (t := 0) hY hB hBound
    simpa only [ψ, hM0, zero_mul, Real.exp_zero, mul_one, div_one] using h
  have hDiff : ∀ s, DifferentiableAt ℝ ψ s := fun s =>
    (LOOConcentration.logPartitionLog_hasDerivAt (μ := μ) (F := Y)
      (t := s) hY hB hBound).differentiableAt
  have hODE : ∀ s, 0 < s → 2 * C * s < 1 →
      s * deriv ψ s - ψ s ≤ 2 * C * s ^ 2 * deriv ψ s := by
    intro s hs hsCut
    have hMpos := LOOConcentration.logPartition_pos (μ := μ) (F := Y) (t := s) hY hBound
    have hE := LOOConcentration.looconcentrationEntropy_exp_eq_logPartition_deriv
      (μ := μ) (F := Y) (t := s) hY hB hBound
    change _ = s * deriv ψ s - ψ s at hE
    rw [← hE]
    have hD := LOOConcentration.logPartitionLog_deriv (μ := μ) (F := Y) (t := s) hY hB hBound
    change deriv ψ s = _ at hD
    rw [hD]
    calc
      _ ≤ (2 * C * s ^ 2 * ∫ x, Y x * Real.exp (s * Y x) ∂μ) /
          LOOConcentration.logPartition μ Y s :=
        div_le_div_of_nonneg_right (hEntropy s hs hsCut) hMpos.le
      _ = _ := by ring
  exact ⟨LOOConcentration.logPartition_integrable hY hBound,
    norm_entropy_differential_bound hC hψ0 hderiv0 hDiff hODE ht htCut⟩

end LOOConcentration.Revision
