import LOOConcentration.Frozen.Probability.LooRiskL1Unique
import LOOConcentration.Frozen.Foundations.LooEstimate
import LOOConcentration.Frozen.FunctionalInequalities.HasLogSobolev
import LOOConcentration.Frozen.Norms.DatasetNorm
import LOOConcentration.Frozen.Norms.ObservationNormSq
import LOOConcentration.Concentration.GeneralQuadraticMGF
import LOOConcentration.Results.GoodSetExtensionMGF
import LOOConcentration.Results.GoodSetTailTransfer
import LOOConcentration.Concentration.SubGaussianSum
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic

set_option autoImplicit false

open MeasureTheory

namespace LOOConcentration.Providers

noncomputable section

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
  intro ν hHmeas hHnorm hHmean hLip
  let E := goodSetLipschitzExtension_localFunction D₀ hD₀ hLK hLip
  have hC : 0 < C := hLSI.1
  let Cnn : NNReal := ⟨C, hC.le⟩
  let LKnn : NNReal := ⟨LK, hLK⟩
  have hCnnVal : (Cnn : ℝ) = C := rfl
  have hLKnnVal : (LKnn : ℝ) = LK := rfl
  have hEslope : ∀ D : DataCarrier k m (n + 1), datasetLocalSlope E D ≤ LK :=
    goodSetLipschitzExtension_localSlope_le D₀ hD₀ hLK hLip
  have hMGF : ProbabilityTheory.HasSubgaussianMGF
      (fun D : DataCarrier k m (n + 1) => E.1 D -
        ∫ E' : DataCarrier k m (n + 1), E.1 E' ∂ν)
      (LOOConcentration.Concentration.subGaussianProxy Cnn LKnn) ν := by
    have hQuadratic (t : ℝ) :=
      generalQuadratic_centeredExp_integral_log_bounded_gradient
        (k := k) (m := m) (n := n + 1) μ hM₂ E hLK hLSI hEslope t
    constructor
    · intro t
      simpa [E, ν, datasetProductLaw, goodSetLipschitzExtension_localFunction] using
        (hQuadratic t).1
    · intro t
      have hIntegralBound :
          (∫ D : DataCarrier k m (n + 1),
            Real.exp (t * (E.1 D - ∫ E' : DataCarrier k m (n + 1), E.1 E' ∂ν)) ∂ν) ≤
            Real.exp (C * LK ^ 2 / 2 * t ^ 2) := by
        simpa [E, ν, datasetProductLaw, goodSetLipschitzExtension_localFunction] using
          (hQuadratic t).2.1
      have hProxyCoeff :
          (LOOConcentration.Concentration.subGaussianProxy Cnn LKnn : ℝ) = C * LK ^ 2 := by
        calc
          _ = (Cnn : ℝ) * (LKnn : ℝ) ^ 2 :=
            LOOConcentration.Concentration.coe_subGaussianProxy Cnn LKnn
          _ = C * LK ^ 2 := by rw [hCnnVal, hLKnnVal]
      change
        (∫ D : DataCarrier k m (n + 1),
          Real.exp (t * (E.1 D - ∫ E' : DataCarrier k m (n + 1), E.1 E' ∂ν)) ∂ν) ≤
          Real.exp ((LOOConcentration.Concentration.subGaussianProxy Cnn LKnn : ℝ) * t ^ 2 / 2)
      calc
        _ ≤ Real.exp (C * LK ^ 2 / 2 * t ^ 2) := hIntegralBound
        _ = Real.exp ((LOOConcentration.Concentration.subGaussianProxy
            Cnn LKnn : ℝ) * t ^ 2 / 2) := by
          congr 1
          rw [hProxyCoeff]
          ring
  have hTransferred := goodSetLipschitzExtension_tail_bounds
    μ C hLSI.1 hM₂ hK hHmeas B δ₃ LK hB hδ₃ hLK D₀ hD₀ hLip
    hHnorm hHmean
  intro M₂ p η t ht tail
  simpa [ν, M₂, p, η, tail, E, datasetProductLaw,
    goodSetLipschitzExtension_localFunction] using
    (hTransferred t ht hMGF).2

end

end LOOConcentration.Providers

#print axioms LOOConcentration.Providers.dataDependentConcentration
