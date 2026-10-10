import LOOConcentration.Frozen.Probability.LooRiskL1Unique
import LOOConcentration.Frozen.Foundations.LooEstimate
import LOOConcentration.Frozen.FunctionalInequalities.HasLogSobolev
import LOOConcentration.Frozen.Norms.DatasetNorm
import LOOConcentration.Frozen.Norms.ObservationNormSq
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import LOOConcentration.Results.Providers.DataDependentConcentration

set_option autoImplicit false
namespace LOOConcentration
open MeasureTheory

theorem dataDependentConcentration {k m n : ℕ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (C : ℝ) (hLSI : HasLogSobolev μ C)
    (hM₂ : Integrable observationNormSq μ)
    (T : ∀ r : ℕ, Estimator (k + 1) (m + 1) (r + 1))
    (L : Responses (m + 1) → Responses (m + 1) → ℝ)
    (hf : Integrable
      (fun p : Dataset (Observation (k + 1) (m + 1)) (n + 2) ×
        Observation (k + 1) (m + 1) => fittedLoss (T (n + 1)) L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ))
    (H : Dataset (Observation (k + 1) (m + 1)) (n + 2) → ℝ)
    (hH : H =ᵐ[Measure.pi fun _ : Fin (n + 2) => μ]
      fun D => (looRiskL1 μ (T (n + 1)) L hf) D - looEstimate (T n) L D)
    (B δ₃ LK : ℝ) (hB : 0 ≤ B) (hδ₃ : 0 ≤ δ₃) (hLK : 0 ≤ LK)
    (K : Set (Dataset (Observation (k + 1) (m + 1)) (n + 2)))
    (hK : MeasurableSet K) (hKne : K.Nonempty)
    (D₀ : Dataset (Observation (k + 1) (m + 1)) (n + 2)) (hD₀ : D₀ ∈ K) :
    let ν := Measure.pi fun _ : Fin (n + 2) => μ
    Measurable H →
    eLpNorm H 2 ν ≤ ENNReal.ofReal B →
    |∫ D, H D ∂ν| ≤ δ₃ →
    (∀ D ∈ K, ∀ E ∈ K, |H D - H E| ≤ LK * datasetNorm (D - E)) →
    let M₂ := ∫ z, observationNormSq z ∂μ
    let p := ν.real Kᶜ
    let η := Real.sqrt p *
      (B + |H D₀| + LK * (Real.sqrt ((n + 2 : ℝ) * M₂) + datasetNorm D₀))
    ∀ (t : ℝ) (ht : 0 < t),
      let tail := if LK = 0 then 0 else Real.exp (-(t ^ 2 / (2 * C * LK ^ 2)))
      (ν.real {D | |H D| > δ₃ + η + t} ≤ p + 2 * tail) ∧
      (ν.real {D | H D > δ₃ + η + t} ≤ p + tail) ∧
      (ν.real {D | -H D > δ₃ + η + t} ≤ p + tail) := by
  exact LOOConcentration.Providers.dataDependentConcentration
    μ C hLSI hM₂ T L hf H hH B δ₃ LK hB hδ₃ hLK K hK hKne D₀ hD₀

end LOOConcentration
