import Mathlib.Probability.Moments.SubGaussian

/-!
Three-term Hölder combination for centered sub-Gaussian observables under a
single probability measure. The proof delegates the measure-level Hölder
estimate, including zero-parameter branches, to Mathlib's
`HasSubgaussianMGF.add` theorem.
-/

open MeasureTheory

namespace LOOConcentration.Concentration

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The proxy corresponding to the real coefficient `C * s ^ 2`. -/
noncomputable def subGaussianProxy (C s : NNReal) : NNReal := (C.sqrt * s) ^ 2

@[simp]
theorem coe_subGaussianProxy (C s : NNReal) :
    (subGaussianProxy C s : ℝ) = (C : ℝ) * (s : ℝ) ^ 2 := by
  simp [subGaussianProxy, mul_pow]

/-- A centered observable together with its all-real, integrable sub-Gaussian
MGF bound. Its proxy has real value `C * s ^ 2`. -/
structure CenteredSubGaussianMGF (μ : Measure Ω) (C s : NNReal)
    (I : Ω → ℝ) : Prop where
  integrable : Integrable I μ
  mean_zero : ∫ x, I x ∂μ = 0
  mgf : ProbabilityTheory.HasSubgaussianMGF I (subGaussianProxy C s) μ

/-- A zero proxy forces the observable to vanish almost everywhere. Mathlib's
zero-proxy theorem proves this from the two-sided all-real MGF bound. -/
theorem ae_eq_zero_of_scale_eq_zero {μ : Measure Ω} {C s : NNReal}
    {I : Ω → ℝ} (hI : CenteredSubGaussianMGF μ C s I) (hs : s = 0) :
    I =ᵐ[μ] 0 := by
  have hzero : ProbabilityTheory.HasSubgaussianMGF I 0 μ := by
    simpa [subGaussianProxy, hs] using hI.mgf
  exact hzero.ae_eq_zero_of_hasSubgaussianMGF_zero

/-- Combine three centered observables by Hölder under one probability law.
There is no independence premise. The scales are nonnegative by their `ℝ≥0`
carrier, and Mathlib's addition theorem omits zero-scale terms internally. -/
theorem centeredSubGaussianMGF_three_add {μ : Measure Ω} [IsProbabilityMeasure μ]
    {C s₁ s₂ s₃ : NNReal} {I₁ I₂ I₃ : Ω → ℝ}
    (h₁ : CenteredSubGaussianMGF μ C s₁ I₁)
    (h₂ : CenteredSubGaussianMGF μ C s₂ I₂)
    (h₃ : CenteredSubGaussianMGF μ C s₃ I₃) :
    CenteredSubGaussianMGF μ C (s₁ + s₂ + s₃)
      (fun x => (I₁ x + I₂ x) + I₃ x) := by
  let h₁₂ := h₁.mgf.add h₂.mgf
  let h₁₂₃ := h₁₂.add h₃.mgf
  have hproxy :
      ((((subGaussianProxy C s₁).sqrt + (subGaussianProxy C s₂).sqrt) ^ 2).sqrt +
        (subGaussianProxy C s₃).sqrt) ^ 2 =
      subGaussianProxy C (s₁ + s₂ + s₃) := by
    simp [subGaussianProxy, mul_add]
  have h₁₂int : Integrable (fun x => I₁ x + I₂ x) μ := h₁.integrable.add h₂.integrable
  refine ⟨h₁₂int.add h₃.integrable, ?_, ?_⟩
  · calc
      ∫ x, (I₁ x + I₂ x) + I₃ x ∂μ
          = (∫ x, I₁ x + I₂ x ∂μ) + ∫ x, I₃ x ∂μ :=
              integral_add h₁₂int h₃.integrable
      _ = ((∫ x, I₁ x ∂μ) + ∫ x, I₂ x ∂μ) + ∫ x, I₃ x ∂μ := by
              rw [integral_add h₁.integrable h₂.integrable]
      _ = 0 := by rw [h₁.mean_zero, h₂.mean_zero, h₃.mean_zero]; ring
  · simpa only [hproxy] using h₁₂₃

/-- If all three scales vanish, then their centered sum vanishes almost
everywhere. This is the all-zero branch of the source argument. -/
theorem three_sum_ae_eq_zero_of_scales_eq_zero {μ : Measure Ω} {C s₁ s₂ s₃ : NNReal}
    {I₁ I₂ I₃ : Ω → ℝ}
    (h₁ : CenteredSubGaussianMGF μ C s₁ I₁)
    (h₂ : CenteredSubGaussianMGF μ C s₂ I₂)
    (h₃ : CenteredSubGaussianMGF μ C s₃ I₃)
    (hs₁ : s₁ = 0) (hs₂ : s₂ = 0) (hs₃ : s₃ = 0) :
    (fun x => (I₁ x + I₂ x) + I₃ x) =ᵐ[μ] 0 := by
  filter_upwards [ae_eq_zero_of_scale_eq_zero h₁ hs₁,
    ae_eq_zero_of_scale_eq_zero h₂ hs₂,
    ae_eq_zero_of_scale_eq_zero h₃ hs₃] with x hx₁ hx₂ hx₃
  simp [hx₁, hx₂, hx₃]

end LOOConcentration.Concentration
