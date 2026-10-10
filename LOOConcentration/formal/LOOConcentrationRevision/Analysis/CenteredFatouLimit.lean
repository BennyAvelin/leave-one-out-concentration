import LOOConcentration.Analysis.ClipLimit
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology

namespace LOOConcentration.Revision

private theorem integral_means_tendsto_of_L1
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ} {F : α → ℝ}
    (hf : ∀ j, Integrable (f j) μ) (hF : Integrable F μ)
    (hL1 : Tendsto (fun j => ∫ x, |f j x - F x| ∂μ) atTop (𝓝 0)) :
    LOOConcentration.IntegralMeansConverge μ f F := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine squeeze_zero (fun j => norm_nonneg _) ?_ hL1
  intro j
  rw [← integral_sub (hf j) hF]
  simpa only [Real.norm_eq_abs] using
    (norm_integral_le_integral_norm (fun x => f j x - F x) (μ := μ))

private theorem exists_subsequence_of_L1
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ} {F : α → ℝ}
    (hf : ∀ j, Integrable (f j) μ) (hF : Integrable F μ)
    (hL1 : Tendsto (fun j => ∫ x, |f j x - F x| ∂μ) atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂μ, Tendsto (fun j => f (ns j) x) atTop (𝓝 (F x)) := by
  have hLp : Tendsto (fun j => eLpNorm (f j - F) 1 μ) atTop (𝓝 0) := by
    have heq (j : ℕ) : eLpNorm (f j - F) 1 μ =
        ENNReal.ofReal (∫ x, |f j x - F x| ∂μ) := by
      rw [eLpNorm_one_eq_lintegral_enorm]
      have h := ofReal_integral_eq_lintegral_ofReal
        ((hf j).sub hF).norm (Filter.Eventually.of_forall fun x => norm_nonneg (f j x - F x))
      simpa only [← ofReal_norm, Real.norm_eq_abs, Pi.sub_apply] using h.symm
    simp_rw [heq]
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hL1
  exact (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (1 : ENNReal) ≠ 0)
    (fun j => (hf j).aestronglyMeasurable) hF.aestronglyMeasurable hLp).exists_seq_tendsto_ae

/-- L1 convergence produces the centers and a common almost everywhere
subsequence before Fatou passes the uniform centered exponential bound. -/
theorem centeredExp_le_of_L1_tendsto
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ} {F : α → ℝ}
    (hf : ∀ j, Integrable (f j) μ) (hF : Integrable F μ)
    (hL1 : Tendsto (fun j => ∫ x, |f j x - F x| ∂μ) atTop (𝓝 0))
    (lam : ℝ) (B : ENNReal)
    (hbound : ∀ j, ∫⁻ x, ENNReal.ofReal
      (Real.exp (lam * (f j x - ∫ y, f j y ∂μ))) ∂μ ≤ B) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (lam * (F x - ∫ y, F y ∂μ))) ∂μ ≤ B := by
  obtain ⟨ns, hns, hpoint⟩ := exists_subsequence_of_L1 hf hF hL1
  have hmeans := integral_means_tendsto_of_L1 hf hF hL1
  have hsubmeans : LOOConcentration.IntegralMeansConverge μ (fun j => f (ns j)) F :=
    hmeans.comp hns.tendsto_atTop
  exact LOOConcentration.centeredExp_fatou (fun j => hf (ns j)) hF
    hpoint hsubmeans lam B (fun j => hbound (ns j))

/-- The same actual L1 passage preserves centered real-power bounds. -/
theorem centeredPow_le_of_L1_tendsto
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ} {F : α → ℝ}
    (hf : ∀ j, Integrable (f j) μ) (hF : Integrable F μ)
    (hL1 : Tendsto (fun j => ∫ x, |f j x - F x| ∂μ) atTop (𝓝 0))
    {p : ℝ} (hp : 2 ≤ p) (B : ENNReal)
    (hbound : ∀ j, ∫⁻ x, ENNReal.ofReal
      (|f j x - ∫ y, f j y ∂μ| ^ p) ∂μ ≤ B) :
    ∫⁻ x, ENNReal.ofReal (|F x - ∫ y, F y ∂μ| ^ p) ∂μ ≤ B := by
  obtain ⟨ns, hns, hpoint⟩ := exists_subsequence_of_L1 hf hF hL1
  have hmeans := integral_means_tendsto_of_L1 hf hF hL1
  have hsubmeans : LOOConcentration.IntegralMeansConverge μ (fun j => f (ns j)) F :=
    hmeans.comp hns.tendsto_atTop
  exact LOOConcentration.centeredPow_fatou (fun j => hf (ns j)) hF
    hpoint hsubmeans hp B (fun j => hbound (ns j))

#print axioms centeredExp_le_of_L1_tendsto
#print axioms centeredPow_le_of_L1_tendsto

end LOOConcentration.Revision
