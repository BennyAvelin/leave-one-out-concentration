import LOOConcentration.Frozen.Probability.LooRiskL1Unique
import LOOConcentration.Probability.ProductConditionalRisk
import LOOConcentration.Stability.Basic

/-!
# Pointwise representative of the conditional risk

For a fitted estimator, integrate its loss against the independent test law.
The resulting function is a pointwise representative of the conditional-risk
class; identification with the frozen L1 risk is only almost everywhere.
-/

set_option autoImplicit false

namespace LOOConcentration

open MeasureTheory
open scoped MeasureTheory

/-- The integral over a fresh test observation for a fixed full fit. -/
noncomputable def looRiskIntegralRepresentative {k m n : ℕ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (T : Estimator (k + 1) (m + 1) (n + 2))
    (L : Responses (m + 1) → Responses (m + 1) → ℝ) :
    Dataset (Observation (k + 1) (m + 1)) (n + 2) → ℝ :=
  fun D => ∫ z, fittedLoss T L D z ∂μ

theorem looRiskIntegralRepresentative_measurable {k m n : ℕ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (T : Estimator (k + 1) (m + 1) (n + 2))
    (L : Responses (m + 1) → Responses (m + 1) → ℝ)
    (hfm : Measurable
      (fun p : Dataset (Observation (k + 1) (m + 1)) (n + 2) ×
        Observation (k + 1) (m + 1) => fittedLoss T L p.1 p.2)) :
    Measurable (looRiskIntegralRepresentative μ T L) := by
  change Measurable (fun D : Dataset (Observation (k + 1) (m + 1)) (n + 2) =>
    ∫ z, fittedLoss T L D z ∂μ)
  exact hfm.stronglyMeasurable.integral_prod_right'.measurable

theorem looRiskIntegralRepresentative_integrable {k m n : ℕ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (T : Estimator (k + 1) (m + 1) (n + 2))
    (L : Responses (m + 1) → Responses (m + 1) → ℝ)
    (hf : Integrable
      (fun p : Dataset (Observation (k + 1) (m + 1)) (n + 2) ×
        Observation (k + 1) (m + 1) => fittedLoss T L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ)) :
    Integrable (looRiskIntegralRepresentative μ T L)
      (Measure.pi fun _ : Fin (n + 2) => μ) := by
  change Integrable
    (fun D : Dataset (Observation (k + 1) (m + 1)) (n + 2) =>
      ∫ z, fittedLoss T L D z ∂μ)
    (Measure.pi fun _ : Fin (n + 2) => μ)
  exact hf.integral_prod_left

theorem looRiskIntegralRepresentative_condExp {k m n : ℕ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (T : Estimator (k + 1) (m + 1) (n + 2))
    (L : Responses (m + 1) → Responses (m + 1) → ℝ)
    (hf : Integrable
      (fun p : Dataset (Observation (k + 1) (m + 1)) (n + 2) ×
        Observation (k + 1) (m + 1) => fittedLoss T L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ)) :
    ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ)[
      (fun p : Dataset (Observation (k + 1) (m + 1)) (n + 2) ×
        Observation (k + 1) (m + 1) => fittedLoss T L p.1 p.2) |
        MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[
          ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ)]
      fun p => looRiskIntegralRepresentative μ T L p.1 := by
  have hchar := looRiskL1_characterization μ T L hf
  have hclass :
      (fun D => (looRiskL1 μ T L hf) D) =ᵐ[
        Measure.pi fun _ : Fin (n + 2) => μ]
        (looRiskIntegralRepresentative μ T L) := by
    exact (hf.integral_prod_left).coeFn_toL1
  have hprod := (Measure.quasiMeasurePreserving_fst
    (μ := Measure.pi fun _ : Fin (n + 2) => μ) (ν := μ)).ae_eq_comp hclass
  exact hchar.trans (by simpa only [Function.comp_def] using hprod)

/-- The L1 class constructed from the pointwise integral representative. -/
noncomputable def looRiskIntegralRepresentativeL1 {k m n : ℕ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (T : Estimator (k + 1) (m + 1) (n + 2))
    (L : Responses (m + 1) → Responses (m + 1) → ℝ)
    (hf : Integrable
      (fun p : Dataset (Observation (k + 1) (m + 1)) (n + 2) ×
        Observation (k + 1) (m + 1) => fittedLoss T L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ)) :
    Dataset (Observation (k + 1) (m + 1)) (n + 2) →₁[
      Measure.pi fun _ : Fin (n + 2) => μ] ℝ :=
  (hf.integral_prod_left).toL1 (looRiskIntegralRepresentative μ T L)

theorem looRiskIntegralRepresentative_ae_eq_looRiskL1 {k m n : ℕ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (T : Estimator (k + 1) (m + 1) (n + 2))
    (L : Responses (m + 1) → Responses (m + 1) → ℝ)
    (hf : Integrable
      (fun p : Dataset (Observation (k + 1) (m + 1)) (n + 2) ×
        Observation (k + 1) (m + 1) => fittedLoss T L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ)) :
    (looRiskIntegralRepresentative μ T L) =ᵐ[
      Measure.pi fun _ : Fin (n + 2) => μ]
      (fun D => (looRiskL1 μ T L hf) D) := by
  let R₀L1 := looRiskIntegralRepresentativeL1 μ T L hf
  have hR₀class :
      (fun D => R₀L1 D) =ᵐ[Measure.pi fun _ : Fin (n + 2) => μ]
        looRiskIntegralRepresentative μ T L := by
    dsimp [R₀L1, looRiskIntegralRepresentativeL1]
    exact (hf.integral_prod_left).coeFn_toL1
  have hR₀prod :
      (fun p : Dataset (Observation (k + 1) (m + 1)) (n + 2) ×
        Observation (k + 1) (m + 1) => R₀L1 p.1) =ᵐ[
          ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ)]
        (fun p => looRiskIntegralRepresentative μ T L p.1) := by
    have h := (Measure.quasiMeasurePreserving_fst
      (μ := Measure.pi fun _ : Fin (n + 2) => μ) (ν := μ)).ae_eq_comp hR₀class
    simpa only [Function.comp_def] using h
  have hR :
      ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ)[
        (fun p : Dataset (Observation (k + 1) (m + 1)) (n + 2) ×
          Observation (k + 1) (m + 1) => fittedLoss T L p.1 p.2) |
          MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[
            ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ)]
        (fun p => R₀L1 p.1) := by
    exact (looRiskIntegralRepresentative_condExp μ T L hf).trans hR₀prod.symm
  have hunique := looRiskL1_unique μ T L hf R₀L1 hR
  have hclass :
      (fun D => R₀L1 D) =ᵐ[Measure.pi fun _ : Fin (n + 2) => μ]
        (fun D => (looRiskL1 μ T L hf) D) := Lp.ext_iff.mp hunique
  filter_upwards [hR₀class, hclass] with D hD₀ hD
  exact hD₀.symm.trans hD

theorem stable_fullFitRiskRepresentative_measurable {k m n : ℕ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator (k + 1) (m + 1) (r + 1))
    (L : Responses (m + 1) → Responses (m + 1) → ℝ)
    (δ₁ δ₂ : ℕ → Observation (k + 1) (m + 1) → ℝ)
    (δ₃ : ℕ → ℝ) (h : Stable μ T L δ₁ δ₂ δ₃) :
    Measurable (looRiskIntegralRepresentative μ (T (n + 1)) L) := by
  exact looRiskIntegralRepresentative_measurable μ (T (n + 1)) L
    (stable_measurable_fittedLoss h (n + 1))

theorem stable_fullFitRiskRepresentative_integrable {k m n : ℕ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator (k + 1) (m + 1) (r + 1))
    (L : Responses (m + 1) → Responses (m + 1) → ℝ)
    (δ₁ δ₂ : ℕ → Observation (k + 1) (m + 1) → ℝ)
    (δ₃ : ℕ → ℝ) (h : Stable μ T L δ₁ δ₂ δ₃) :
    Integrable (looRiskIntegralRepresentative μ (T (n + 1)) L)
      (Measure.pi fun _ : Fin (n + 2) => μ) := by
  exact looRiskIntegralRepresentative_integrable μ (T (n + 1)) L
    (stable_integrable_fittedLoss h n)

theorem stable_fullFitRiskRepresentative_ae_eq_looRiskL1 {k m n : ℕ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator (k + 1) (m + 1) (r + 1))
    (L : Responses (m + 1) → Responses (m + 1) → ℝ)
    (δ₁ δ₂ : ℕ → Observation (k + 1) (m + 1) → ℝ)
    (δ₃ : ℕ → ℝ) (h : Stable μ T L δ₁ δ₂ δ₃) :
    (looRiskIntegralRepresentative μ (T (n + 1)) L) =ᵐ[
      Measure.pi fun _ : Fin (n + 2) => μ]
      (fun D => (looRiskL1 μ (T (n + 1)) L
        (stable_integrable_fittedLoss h n)) D) := by
  exact looRiskIntegralRepresentative_ae_eq_looRiskL1 μ (T (n + 1)) L
    (stable_integrable_fittedLoss h n)

end LOOConcentration
