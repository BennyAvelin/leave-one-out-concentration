import LOOConcentrationRevision.Concentration.DataDependentClassAssembly

set_option autoImplicit false
namespace LOOConcentration.Revision.Providers
open MeasureTheory Filter
open scoped Topology ENNReal

theorem dataDependentConcentration {k m n : ℕ}
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (_hlsi : observationLogSobolevConstant μ < ⊤)
    (_hsecond : Integrable observationNormSq μ)
    (H : Dataset (Observation k m) (n + 2) → ℝ) (_hH : Measurable H)
    (B δ L_K : NNReal)
    (_hL2 : eLpNorm H 2 (Measure.pi fun _ : Fin (n + 2) => μ) ≤ (B : ℝ≥0∞))
    (_hbias : |∫ D, H D ∂Measure.pi fun _ : Fin (n + 2) => μ| ≤ (δ : ℝ))
    (K : Set (Dataset (Observation k m) (n + 2))) (_hK : MeasurableSet K)
    (_hKpos : 0 < (Measure.pi fun _ : Fin (n + 2) => μ) K)
    (_hLip : ∀ D ∈ K, ∀ E ∈ K, |H D - H E| ≤ (L_K : ℝ) * datasetNorm (D - E)) :
    let ν := Measure.pi fun _ : Fin (n + 2) => μ
    let p := ν.real Kᶜ
    let C := (observationLogSobolevConstant μ).toReal
    let cBNT := 3 * (2 : ℝ) ^ 12 * Real.exp 2
    let C_K := cBNT * C * Real.log (Real.exp 1 / (1 - p))
    let η_K := (B : ℝ) * Real.sqrt (p / (1 - p))
    ∀ (ε : ℝ) (_hε : (δ : ℝ) + η_K < ε),
      let G := if C_K * (L_K : ℝ) ^ 2 = 0 then 0 else
        Real.exp (-((ε - (δ : ℝ) - η_K) ^ 2 / (2 * C_K * (L_K : ℝ) ^ 2)))
      ν.real {D | H D > ε} ≤ p + G ∧
      ν.real {D | -H D > ε} ≤ p + G ∧
      ν.real {D | |H D| > ε} ≤ p + 2 * G := by
  exact LOOConcentration.Revision.dataDependentConcentration_class_assembly μ _hlsi _hsecond H _hH B δ L_K _hL2 _hbias K _hK _hKpos _hLip

end LOOConcentration.Revision.Providers
