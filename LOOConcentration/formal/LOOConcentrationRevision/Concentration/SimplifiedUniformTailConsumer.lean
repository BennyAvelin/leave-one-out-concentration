import LOOConcentrationRevision.Concentration.SimplifiedCombinedMGFAndTail
import LOOConcentrationRevision.Results.StandingLossDecomposition
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

open MeasureTheory Filter
open scoped Topology ENNReal

namespace LOOConcentration.Revision

noncomputable section

private theorem measureReal_mono_ae
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {s t : Set α} (hst : ∀ᵐ x ∂μ, x ∈ s → x ∈ t) :
    μ.real s ≤ μ.real t := by
  rw [Measure.real, Measure.real]
  exact ENNReal.toReal_mono (by finiteness) (measure_mono_ae hst)

private theorem strict_tail_of_hasSubgaussianMGF
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    {X : Ω → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hX : ProbabilityTheory.HasSubgaussianMGF X (NNReal.mk K hK) ν)
    {t : ℝ} (ht : 0 < t) :
    ν.real {x | X x > t} ≤
      (if K = 0 then 0 else Real.exp (-(t ^ 2 / (2 * K)))) := by
  by_cases hK0 : K = 0
  · have hzero : ProbabilityTheory.HasSubgaussianMGF X 0 ν := by
      simpa [hK0] using hX
    have hae : X =ᵐ[ν] 0 :=
      hzero.ae_eq_zero_of_hasSubgaussianMGF_zero
    have hsub : ∀ᵐ x ∂ν, x ∈ {x | X x > t} → x ∈ (∅ : Set Ω) := by
      filter_upwards [hae] with x hx hxt
      rw [hx] at hxt
      exact (not_lt_of_ge ht.le hxt).elim
    have hmeasure := measureReal_mono_ae hsub
    simpa [hK0] using hmeasure
  · have htail := hX.measure_ge_le (show 0 ≤ t by linarith)
    have hstrict : {x | X x > t} ⊆ {x | t ≤ X x} := by
      intro x hx
      change t < X x at hx
      exact le_of_lt hx
    have hreal : (NNReal.mk K hK : ℝ) = K := rfl
    have hexp :
        Real.exp (-t ^ 2 / (2 * (NNReal.mk K hK : ℝ))) =
          Real.exp (-(t ^ 2 / (2 * K))) := by
      congr 1
      rw [hreal]
      ring
    calc
      ν.real {x | X x > t} ≤ ν.real {x | t ≤ X x} :=
        measureReal_mono hstrict
      _ ≤ Real.exp (-t ^ 2 / (2 * (NNReal.mk K hK : ℝ))) := htail
      _ = Real.exp (-(t ^ 2 / (2 * K))) := hexp
      _ = if K = 0 then 0 else Real.exp (-(t ^ 2 / (2 * K))) := by
        rw [if_neg hK0]

/-- The source-scale combined MGF gives the exact uniform, two-sided deviation
bound for the L1 risk error after removing and restoring the deterministic
standing bias. Both one-sided bounds are included for the frozen second clause. -/
theorem simplified_uniform_tail
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (h : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)
    (hzero : ∀ z, δ₂ (n + 1) z = 0 ∧ δ₂ (n + 2) z = 0)
    (hLip : ∀ z w,
      |meanFittedLoss μ (T n) L z (h.mean_integrable z) -
        meanFittedLoss μ (T n) L w (h.mean_integrable w)| ≤
          c * observationNorm (z - w))
    (a : NNReal) (ha : ∀ᵐ z ∂μ, δ₁ (n + 1) z ≤ (a : ℝ))
    (t : ℝ) (ht : 0 < t) :
    let ν := Measure.pi fun _ : Fin (n + 2) => μ
    let H := fun D =>
      (looRiskL1 μ (T (n + 1)) L (h.stable.integrable_full n)) D -
        looEstimate (T n) L D
    let s := (a : ℝ) + c / Real.sqrt (n + 2 : ℝ) +
      ∫ z, δ₁ (n + 2) z ∂μ
    let C := (observationLogSobolevConstant μ).toReal
    let G := if C * s ^ 2 = 0 then 0 else
      Real.exp (-(t ^ 2 / (2 * C * s ^ 2)))
    ν.real {D | |H D| > δ₃ (n + 2) + t} ≤ 2 * G ∧
    ν.real {D | H D > δ₃ (n + 2) + t} ≤ G ∧
    ν.real {D | -H D > δ₃ (n + 2) + t} ≤ G := by
  let ν : Measure (Dataset (Observation k m) (n + 2)) :=
    Measure.pi fun _ : Fin (n + 2) => μ
  let H : Dataset (Observation k m) (n + 2) → ℝ := fun D =>
    (looRiskL1 μ (T (n + 1)) L (h.stable.integrable_full n)) D -
      looEstimate (T n) L D
  let B := standingB μ T L δ₁ δ₂ δ₃ c d h
  let C : ℝ := (observationLogSobolevConstant μ).toReal
  let s : ℝ := (a : ℝ) + c / Real.sqrt (n + 2 : ℝ) +
    ∫ z, δ₁ (n + 2) z ∂μ
  let K : ℝ := C * s ^ 2
  have hK : 0 ≤ K := mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
  have hGaussian :
      (if K = 0 then 0 else Real.exp (-(t ^ 2 / (2 * K)))) =
        (if C * s ^ 2 = 0 then 0 else Real.exp (-(t ^ 2 / (2 * C * s ^ 2)))) := by
    by_cases hz : C * s ^ 2 = 0
    · simp [K, hz]
    · have hden : 2 * C * s ^ 2 = 2 * (C * s ^ 2) := by ring
      rw [show K = C * s ^ 2 by rfl]
      simp only [if_neg hz]
      congr 1
      rw [hden]
  have hMgf := simplified_combined_mgf μ T L δ₁ δ₂ δ₃ c d h hzero hLip a ha
  have hTail (X : Dataset (Observation k m) (n + 2) → ℝ)
      (hX : ProbabilityTheory.HasSubgaussianMGF X (NNReal.mk K hK) ν) :
      ν.real {D | X D > t} ≤
        (if K = 0 then 0 else Real.exp (-(t ^ 2 / (2 * K)))) :=
    strict_tail_of_hasSubgaussianMGF hK hX ht
  have hBbound : |B| ≤ δ₃ (n + 2) := by
    dsimp [B]
    exact standingB_abs_le μ T L δ₁ δ₂ δ₃ c d h
  have hSbound : ProbabilityTheory.HasSubgaussianMGF
      (fun D => H D - B) (NNReal.mk K hK) ν := by
    simpa [H, B, K, s, C, ν] using hMgf
  have hUpperSub : {D | H D > δ₃ (n + 2) + t} ⊆
      {D | H D - B > t} := by
    intro D hD
    have hBupper : B ≤ δ₃ (n + 2) := (le_abs_self _).trans hBbound
    change δ₃ (n + 2) + t < H D at hD
    change t < H D - B
    linarith
  have hLowerSub : {D | -H D > δ₃ (n + 2) + t} ⊆
      {D | -(H D - B) > t} := by
    intro D hD
    have hBlower : -B ≤ δ₃ (n + 2) := (neg_le_abs _).trans hBbound
    change δ₃ (n + 2) + t < -H D at hD
    change t < -(H D - B)
    linarith
  have hUpper : ν.real {D | H D > δ₃ (n + 2) + t} ≤
      (if K = 0 then 0 else Real.exp (-(t ^ 2 / (2 * K)))) := by
    calc
      _ ≤ ν.real {D | H D - B > t} := measureReal_mono hUpperSub
      _ ≤ _ := hTail _ hSbound
  have hLower : ν.real {D | -H D > δ₃ (n + 2) + t} ≤
      (if K = 0 then 0 else Real.exp (-(t ^ 2 / (2 * K)))) := by
    calc
      _ ≤ ν.real {D | -(H D - B) > t} := measureReal_mono hLowerSub
      _ ≤ _ := hTail _ hSbound.neg
  have hAbsSub : {D | |H D| > δ₃ (n + 2) + t} ⊆
      {D | H D > δ₃ (n + 2) + t} ∪ {D | -H D > δ₃ (n + 2) + t} := by
    intro D hD
    change δ₃ (n + 2) + t < |H D| at hD
    by_cases hnonneg : 0 ≤ H D
    · left
      simpa [abs_of_nonneg hnonneg] using hD
    · right
      have hneg : H D < 0 := lt_of_not_ge hnonneg
      simpa [abs_of_neg hneg] using hD
  have hAbs : ν.real {D | |H D| > δ₃ (n + 2) + t} ≤
      2 * (if K = 0 then 0 else Real.exp (-(t ^ 2 / (2 * K)))) := by
    calc
      _ ≤ ν.real ({D | H D > δ₃ (n + 2) + t} ∪
          {D | -H D > δ₃ (n + 2) + t}) := measureReal_mono hAbsSub
      _ ≤ _ := by
        calc
          _ ≤ ν.real {D | H D > δ₃ (n + 2) + t} +
              ν.real {D | -H D > δ₃ (n + 2) + t} := measureReal_union_le _ _
          _ ≤ 2 * (if K = 0 then 0 else Real.exp (-(t ^ 2 / (2 * K)))) := by
            calc
              _ ≤ (if K = 0 then 0 else Real.exp (-(t ^ 2 / (2 * K)))) +
                  (if K = 0 then 0 else Real.exp (-(t ^ 2 / (2 * K)))) :=
                    add_le_add hUpper hLower
              _ = 2 * (if K = 0 then 0 else Real.exp (-(t ^ 2 / (2 * K)))) := by ring
  rw [hGaussian] at hAbs hUpper hLower
  simpa only [ν, H, C, s] using And.intro hAbs (And.intro hUpper hLower)

end
end LOOConcentration.Revision
