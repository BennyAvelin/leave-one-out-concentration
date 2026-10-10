import LOOConcentration.Results.StandingFacts
import LOOConcentration.Stability.Basic
import LOOConcentration.Probability.SampleTestLaw
import LOOConcentration.Probability.LooIntegrability
import LOOConcentration.Frozen.Probability.MeanFittedLoss
import LOOConcentration.Frozen.Probability.LooRiskL1Characterization
import LOOConcentration.Frozen.Foundations.LooEstimate
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Pointwise decomposition of the leave-one-out error

For a full sample of size `N = n + 2`, the fit in each deleted term is `T n`
(trained on `N - 1 = n + 1` observations), while the full-sample risk uses
`T (n + 1)` (trained on `N` observations).  The risk below is the ordinary
integral representative of the frozen `L¹` conditional risk.
-/

set_option autoImplicit false

namespace LOOConcentration

open MeasureTheory
open scoped MeasureTheory

/-- Integral representative of the conditional risk for the full sample. -/
noncomputable def looR0 {k m n : ℕ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator (k + 1) (m + 1) (r + 1))
    (L : Responses (m + 1) → Responses (m + 1) → ℝ)
    (D : Dataset (Observation (k + 1) (m + 1)) (n + 2)) : ℝ :=
  ∫ z, fittedLoss (T (n + 1)) L D z ∂μ

/-- Empirical leave-one-out validation average. -/
noncomputable def looV {k m n : ℕ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator (k + 1) (m + 1) (r + 1))
    (L : Responses (m + 1) → Responses (m + 1) → ℝ)
    (D : Dataset (Observation (k + 1) (m + 1)) (n + 2)) : ℝ :=
  looEstimate (T n) L D

/-- Validation-sample average of the deleted-fit expected loss. -/
noncomputable def looJ {k m n : ℕ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator (k + 1) (m + 1) (r + 1))
    (L : Responses (m + 1) → Responses (m + 1) → ℝ)
    (hbar : ∀ z, Integrable
      (fun D : Dataset (Observation (k + 1) (m + 1)) (n + 1) =>
        fittedLoss (T n) L D z)
      (Measure.pi fun _ : Fin (n + 1) => μ))
    (D : Dataset (Observation (k + 1) (m + 1)) (n + 2)) : ℝ :=
  (∑ i : Fin (n + 2),
    meanFittedLoss μ (T n) L (D i) (hbar (D i))) / (n + 2 : ℝ)

/-- Average deleted-fit fluctuation around its training-sample mean. -/
noncomputable def looI1 {k m n : ℕ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator (k + 1) (m + 1) (r + 1))
    (L : Responses (m + 1) → Responses (m + 1) → ℝ)
    (hbar : ∀ z, Integrable
      (fun D : Dataset (Observation (k + 1) (m + 1)) (n + 1) =>
        fittedLoss (T n) L D z)
      (Measure.pi fun _ : Fin (n + 1) => μ))
    (D : Dataset (Observation (k + 1) (m + 1)) (n + 2)) : ℝ :=
  (∑ i : Fin (n + 2),
    (meanFittedLoss μ (T n) L (D i) (hbar (D i)) -
      fittedLoss (T n) L (deleteAt D i) (D i))) / (n + 2 : ℝ)

/-- Centered validation-sample fluctuation of the expected fitted loss. -/
noncomputable def looI2 {k m n : ℕ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator (k + 1) (m + 1) (r + 1))
    (L : Responses (m + 1) → Responses (m + 1) → ℝ)
    (hbar : ∀ z, Integrable
      (fun D : Dataset (Observation (k + 1) (m + 1)) (n + 1) =>
        fittedLoss (T n) L D z)
      (Measure.pi fun _ : Fin (n + 1) => μ))
    (D : Dataset (Observation (k + 1) (m + 1)) (n + 2)) : ℝ :=
  (∫ z, meanFittedLoss μ (T n) L z (hbar z) ∂μ) - looJ μ T L hbar D

/-- Centered fluctuation of the full-sample conditional risk. -/
noncomputable def looI3 {k m n : ℕ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator (k + 1) (m + 1) (r + 1))
    (L : Responses (m + 1) → Responses (m + 1) → ℝ)
    (D : Dataset (Observation (k + 1) (m + 1)) (n + 2)) : ℝ :=
  looR0 μ T L D -
    ∫ E : Dataset (Observation (k + 1) (m + 1)) (n + 2),
      looR0 μ T L E ∂Measure.pi fun _ : Fin (n + 2) => μ

/-- Deterministic difference between the full risk mean and deleted-fit mean. -/
noncomputable def looBN {k m n : ℕ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator (k + 1) (m + 1) (r + 1))
    (L : Responses (m + 1) → Responses (m + 1) → ℝ)
    (hbar : ∀ z, Integrable
      (fun D : Dataset (Observation (k + 1) (m + 1)) (n + 1) =>
        fittedLoss (T n) L D z)
      (Measure.pi fun _ : Fin (n + 1) => μ)) : ℝ :=
  (∫ D : Dataset (Observation (k + 1) (m + 1)) (n + 2),
    looR0 μ T L D ∂Measure.pi fun _ : Fin (n + 2) => μ) -
    ∫ z, meanFittedLoss μ (T n) L z (hbar z) ∂μ

private theorem deletedFitTestIntegrable {k m n : ℕ}
    {C : ℝ} {δ₁ δ₂ : ℕ → Observation (k + 1) (m + 1) → ℝ}
    {δ₃ : ℕ → ℝ} {c d : ℝ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator (k + 1) (m + 1) (r + 1))
    (L : Responses (m + 1) → Responses (m + 1) → ℝ)
    (h : StandingAssumption (n := n) μ C T L δ₁ δ₂ δ₃ c d) :
    Integrable
      (fun p : Dataset (Observation (k + 1) (m + 1)) (n + 1) ×
        Observation (k + 1) (m + 1) => fittedLoss (T n) L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 1) => μ).prod μ) := by
  rcases h.2.2.1 with ⟨hmeas, _, _, _, _, _, _, _, hheld⟩
  let i : Fin (n + 2) := ⟨0, by omega⟩
  let φ : Dataset (Observation (k + 1) (m + 1)) (n + 2) →
      Dataset (Observation (k + 1) (m + 1)) (n + 1) ×
        Observation (k + 1) (m + 1) := fun D => (deleteAt D i, D i)
  let g : Dataset (Observation (k + 1) (m + 1)) (n + 1) ×
      Observation (k + 1) (m + 1) → ℝ := fun p => fittedLoss (T n) L p.1 p.2
  have hmap := deleted_sample_and_heldout_measurePreserving μ i
  have hg : AEStronglyMeasurable g
      (Measure.map φ (Measure.pi fun _ : Fin (n + 2) => μ)) := by
    rw [hmap.map_eq]
    exact (hmeas n).aestronglyMeasurable
  have hcomp : Integrable (g ∘ φ) (Measure.pi fun _ : Fin (n + 2) => μ) := by
    change Integrable (fun D => g (φ D)) _
    change Integrable
      (fun D : Dataset (Observation (k + 1) (m + 1)) (n + 2) =>
        fittedLoss (T n) L (deleteAt D i) (D i)) _
    exact (hheld n i).1
  have hmapint : Integrable g (Measure.map φ
      (Measure.pi fun _ : Fin (n + 2) => μ)) :=
    (integrable_map_measure hg hmap.measurable.aemeasurable).2 hcomp
  rw [hmap.map_eq] at hmapint
  exact hmapint

private theorem looMeanFitIntegrable {k m n : ℕ}
    {C : ℝ} {δ₁ δ₂ : ℕ → Observation (k + 1) (m + 1) → ℝ}
    {δ₃ : ℕ → ℝ} {c d : ℝ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator (k + 1) (m + 1) (r + 1))
    (L : Responses (m + 1) → Responses (m + 1) → ℝ)
    (h : StandingAssumption (n := n) μ C T L δ₁ δ₂ δ₃ c d) :
    Integrable
      (fun z => meanFittedLoss μ (T n) L z (standing_mean_integrable h z)) μ := by
  have hprod := deletedFitTestIntegrable μ T L h
  simpa only [meanFittedLoss] using hprod.integral_prod_right

private theorem looR0Integrable {k m n : ℕ}
    {C : ℝ} {δ₁ δ₂ : ℕ → Observation (k + 1) (m + 1) → ℝ}
    {δ₃ : ℕ → ℝ} {c d : ℝ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator (k + 1) (m + 1) (r + 1))
    (L : Responses (m + 1) → Responses (m + 1) → ℝ)
    (h : StandingAssumption (n := n) μ C T L δ₁ δ₂ δ₃ c d) :
    Integrable (looR0 μ T L)
      (Measure.pi fun _ : Fin (n + 2) => μ) := by
  change Integrable
    (fun D : Dataset (Observation (k + 1) (m + 1)) (n + 2) =>
      ∫ z, fittedLoss (T (n + 1)) L D z ∂μ)
    (Measure.pi fun _ : Fin (n + 2) => μ)
  exact (standing_integrable_full_fittedLoss h).integral_prod_left

private theorem looJIntegrable {k m n : ℕ}
    {C : ℝ} {δ₁ δ₂ : ℕ → Observation (k + 1) (m + 1) → ℝ}
    {δ₃ : ℕ → ℝ} {c d : ℝ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator (k + 1) (m + 1) (r + 1))
    (L : Responses (m + 1) → Responses (m + 1) → ℝ)
    (h : StandingAssumption (n := n) μ C T L δ₁ δ₂ δ₃ c d) :
    Integrable (looJ μ T L (standing_mean_integrable h))
      (Measure.pi fun _ : Fin (n + 2) => μ) := by
  let f : Observation (k + 1) (m + 1) → ℝ := fun z =>
    meanFittedLoss μ (T n) L z (standing_mean_integrable h z)
  have hf : Integrable f μ := by
    simpa only [f] using looMeanFitIntegrable μ T L h
  have hcoord : ∀ i : Fin (n + 2),
      Integrable (fun D : Dataset (Observation (k + 1) (m + 1)) (n + 2) => f (D i))
        (Measure.pi fun _ : Fin (n + 2) => μ) := by
    intro i
    exact (sample_coordinate_measurePreserving μ i).integrable_comp_of_integrable hf
  have hsum : Integrable
      (fun D : Dataset (Observation (k + 1) (m + 1)) (n + 2) =>
        ∑ i : Fin (n + 2), f (D i))
      (Measure.pi fun _ : Fin (n + 2) => μ) :=
    integrable_finsetSum Finset.univ (fun i _ => hcoord i)
  change Integrable
    (fun D : Dataset (Observation (k + 1) (m + 1)) (n + 2) =>
      (∑ i : Fin (n + 2), f (D i)) / (n + 2 : ℝ))
    (Measure.pi fun _ : Fin (n + 2) => μ)
  exact hsum.div_const (n + 2 : ℝ)

private theorem looMeanFitIntegral_eq_joint {k m n : ℕ}
    {C : ℝ} {δ₁ δ₂ : ℕ → Observation (k + 1) (m + 1) → ℝ}
    {δ₃ : ℕ → ℝ} {c d : ℝ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator (k + 1) (m + 1) (r + 1))
    (L : Responses (m + 1) → Responses (m + 1) → ℝ)
    (h : StandingAssumption (n := n) μ C T L δ₁ δ₂ δ₃ c d) :
    (∫ z, meanFittedLoss μ (T n) L z (standing_mean_integrable h z) ∂μ) =
      ∫ p : Dataset (Observation (k + 1) (m + 1)) (n + 1) ×
        Observation (k + 1) (m + 1),
        fittedLoss (T n) L p.1 p.2
          ∂((Measure.pi fun _ : Fin (n + 1) => μ).prod μ) := by
  have hprod := deletedFitTestIntegrable μ T L h
  simpa only [meanFittedLoss] using
    (integral_prod_symm
      (fun p : Dataset (Observation (k + 1) (m + 1)) (n + 1) ×
        Observation (k + 1) (m + 1) => fittedLoss (T n) L p.1 p.2)
      hprod).symm

private theorem looVIntegral_eq_meanFit {k m n : ℕ}
    {C : ℝ} {δ₁ δ₂ : ℕ → Observation (k + 1) (m + 1) → ℝ}
    {δ₃ : ℕ → ℝ} {c d : ℝ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator (k + 1) (m + 1) (r + 1))
    (L : Responses (m + 1) → Responses (m + 1) → ℝ)
    (h : StandingAssumption (n := n) μ C T L δ₁ δ₂ δ₃ c d) :
    (∫ D : Dataset (Observation (k + 1) (m + 1)) (n + 2),
      looV μ T L D ∂Measure.pi fun _ : Fin (n + 2) => μ) =
      ∫ z, meanFittedLoss μ (T n) L z (standing_mean_integrable h z) ∂μ := by
  have hloo := integral_looEstimate_eq_independent_test μ (T n) L
    (deletedFitTestIntegrable μ T L h)
  calc
    (∫ D : Dataset (Observation (k + 1) (m + 1)) (n + 2),
      looV μ T L D ∂Measure.pi fun _ : Fin (n + 2) => μ) =
        ∫ p : Dataset (Observation (k + 1) (m + 1)) (n + 1) ×
          Observation (k + 1) (m + 1),
          fittedLoss (T n) L p.1 p.2
            ∂((Measure.pi fun _ : Fin (n + 1) => μ).prod μ) := by
      simpa only [looV] using hloo
    _ = ∫ z, meanFittedLoss μ (T n) L z (standing_mean_integrable h z) ∂μ :=
      (looMeanFitIntegral_eq_joint μ T L h).symm

private theorem looJIntegral_eq_meanFit {k m n : ℕ}
    {C : ℝ} {δ₁ δ₂ : ℕ → Observation (k + 1) (m + 1) → ℝ}
    {δ₃ : ℕ → ℝ} {c d : ℝ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator (k + 1) (m + 1) (r + 1))
    (L : Responses (m + 1) → Responses (m + 1) → ℝ)
    (h : StandingAssumption (n := n) μ C T L δ₁ δ₂ δ₃ c d) :
    (∫ D : Dataset (Observation (k + 1) (m + 1)) (n + 2),
      looJ μ T L (standing_mean_integrable h) D
        ∂Measure.pi fun _ : Fin (n + 2) => μ) =
      ∫ z, meanFittedLoss μ (T n) L z (standing_mean_integrable h z) ∂μ := by
  let f : Observation (k + 1) (m + 1) → ℝ := fun z =>
    meanFittedLoss μ (T n) L z (standing_mean_integrable h z)
  have hf : Integrable f μ := by
    simpa only [f] using looMeanFitIntegrable μ T L h
  have hcoord : ∀ i : Fin (n + 2),
      Integrable (fun D : Dataset (Observation (k + 1) (m + 1)) (n + 2) => f (D i))
        (Measure.pi fun _ : Fin (n + 2) => μ) := by
    intro i
    exact (sample_coordinate_measurePreserving μ i).integrable_comp_of_integrable hf
  have hcoordInt : ∀ i : Fin (n + 2),
      (∫ D : Dataset (Observation (k + 1) (m + 1)) (n + 2),
        f (D i) ∂Measure.pi fun _ : Fin (n + 2) => μ) = ∫ z, f z ∂μ := by
    intro i
    calc
      (∫ D : Dataset (Observation (k + 1) (m + 1)) (n + 2),
        f (D i) ∂Measure.pi fun _ : Fin (n + 2) => μ) =
          ∫ z, f z ∂(Measure.map (fun D : Dataset (Observation (k + 1) (m + 1))
            (n + 2) => D i) (Measure.pi fun _ : Fin (n + 2) => μ)) := by
          symm
          have hmap := sample_coordinate_law μ i
          have hfmap : AEStronglyMeasurable f
              (Measure.map (fun D : Dataset (Observation (k + 1) (m + 1))
                (n + 2) => D i) (Measure.pi fun _ : Fin (n + 2) => μ)) := by
            rw [hmap]
            exact hf.aestronglyMeasurable
          exact integral_map (measurable_pi_apply i).aemeasurable hfmap
      _ = ∫ z, f z ∂μ := by rw [sample_coordinate_law μ i]
  have hsum : Integrable
      (fun D : Dataset (Observation (k + 1) (m + 1)) (n + 2) =>
        ∑ i : Fin (n + 2), f (D i))
      (Measure.pi fun _ : Fin (n + 2) => μ) :=
    integrable_finsetSum Finset.univ (fun i _ => hcoord i)
  have hN : (n + 2 : ℝ) ≠ 0 := by positivity
  change (∫ D : Dataset (Observation (k + 1) (m + 1)) (n + 2),
    (∑ i : Fin (n + 2), f (D i)) / (n + 2 : ℝ)
      ∂Measure.pi fun _ : Fin (n + 2) => μ) = ∫ z, f z ∂μ
  rw [integral_div]
  rw [integral_finsetSum Finset.univ (fun i _ => hcoord i)]
  simp_rw [hcoordInt]
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hN]


/-- The source's four-term identity for the ordinary integral representative.
The deleted estimator has `n + 1 = N - 1` training observations, and the full
estimator has `n + 2 = N`. -/
theorem loo_decomposition_pointwise {k m n : ℕ}
    {C : ℝ} {δ₁ δ₂ : ℕ → Observation (k + 1) (m + 1) → ℝ}
    {δ₃ : ℕ → ℝ} {c d : ℝ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator (k + 1) (m + 1) (r + 1))
    (L : Responses (m + 1) → Responses (m + 1) → ℝ)
    (h : StandingAssumption (n := n) μ C T L δ₁ δ₂ δ₃ c d)
    (D : Dataset (Observation (k + 1) (m + 1)) (n + 2)) :
    looR0 μ T L D - looV μ T L D =
      looI1 μ T L (standing_mean_integrable h) D +
      looI2 μ T L (standing_mean_integrable h) D +
      looI3 μ T L D + looBN μ T L (standing_mean_integrable h) := by
  simp only [looR0, looV, looI1, looI2, looJ, looI3, looBN, looEstimate,
    fittedLoss, Finset.sum_sub_distrib]
  ring_nf

/-- Integrability, centering, and the stability bias bound for the four terms. -/
theorem loo_decomposition_expectations {k m n : ℕ}
    {C : ℝ} {δ₁ δ₂ : ℕ → Observation (k + 1) (m + 1) → ℝ}
    {δ₃ : ℕ → ℝ} {c d : ℝ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator (k + 1) (m + 1) (r + 1))
    (L : Responses (m + 1) → Responses (m + 1) → ℝ)
    (h : StandingAssumption (n := n) μ C T L δ₁ δ₂ δ₃ c d) :
    Integrable (looR0 μ T L) (Measure.pi fun _ : Fin (n + 2) => μ) ∧
    Integrable (looV μ T L) (Measure.pi fun _ : Fin (n + 2) => μ) ∧
    Integrable (looJ μ T L (standing_mean_integrable h))
      (Measure.pi fun _ : Fin (n + 2) => μ) ∧
    Integrable (looI1 μ T L (standing_mean_integrable h))
      (Measure.pi fun _ : Fin (n + 2) => μ) ∧
    Integrable (looI2 μ T L (standing_mean_integrable h))
      (Measure.pi fun _ : Fin (n + 2) => μ) ∧
    Integrable (looI3 μ T L) (Measure.pi fun _ : Fin (n + 2) => μ) ∧
    (∫ D, looI1 μ T L (standing_mean_integrable h) D
      ∂Measure.pi fun _ : Fin (n + 2) => μ) = 0 ∧
    (∫ D, looI2 μ T L (standing_mean_integrable h) D
      ∂Measure.pi fun _ : Fin (n + 2) => μ) = 0 ∧
    (∫ D, looI3 μ T L D ∂Measure.pi fun _ : Fin (n + 2) => μ) = 0 ∧
    |looBN μ T L (standing_mean_integrable h)| ≤ δ₃ (n + 2) := by
  let ν := Measure.pi fun _ : Fin (n + 2) => μ
  let hbar := standing_mean_integrable h
  let f : Observation (k + 1) (m + 1) → ℝ := fun z =>
    meanFittedLoss μ (T n) L z (hbar z)
  let fmean : ℝ := ∫ z, f z ∂μ
  let rmean : ℝ := ∫ D : Dataset (Observation (k + 1) (m + 1)) (n + 2),
    looR0 μ T L D ∂ν
  have hR0 : Integrable (looR0 μ T L) ν := by
    simpa only [ν] using looR0Integrable μ T L h
  have hV : Integrable (looV μ T L) ν := by
    change Integrable (looEstimate (T n) L)
      (Measure.pi fun _ : Fin (n + 2) => μ)
    exact stable_integrable_looEstimate h.2.2.1 n
  have hJ : Integrable (looJ μ T L hbar) ν := by
    simpa only [hbar, ν] using looJIntegrable μ T L h
  have hf : Integrable f μ := by
    simpa only [f, hbar] using looMeanFitIntegrable μ T L h
  have hJmean : (∫ D, looJ μ T L hbar D ∂ν) = fmean := by
    simpa only [hbar, ν, f, fmean] using
      looJIntegral_eq_meanFit (n := n) (C := C) (δ₁ := δ₁) (δ₂ := δ₂)
        (δ₃ := δ₃) (c := c) (d := d) μ T L h
  have hVmean : (∫ D, looV μ T L D ∂ν) = fmean := by
    simpa only [ν, f, fmean, hbar] using looVIntegral_eq_meanFit μ T L h
  have hRmean : rmean =
      ∫ p : Dataset (Observation (k + 1) (m + 1)) (n + 2) ×
        Observation (k + 1) (m + 1),
        fittedLoss (T (n + 1)) L p.1 p.2
          ∂((Measure.pi fun _ : Fin (n + 2) => μ).prod μ) := by
    have hfull := standing_integrable_full_fittedLoss h
    dsimp [rmean, ν]
    simpa only [looR0] using
      (integral_prod
        (fun p : Dataset (Observation (k + 1) (m + 1)) (n + 2) ×
          Observation (k + 1) (m + 1) => fittedLoss (T (n + 1)) L p.1 p.2)
        hfull).symm
  have hI1eq : ∀ D, looI1 μ T L hbar D = looJ μ T L hbar D - looV μ T L D := by
    intro D
    simp only [looI1, looJ, looV, looEstimate, fittedLoss, Finset.sum_sub_distrib]
    ring_nf
  have hI1 : Integrable (looI1 μ T L hbar) ν := by
    have hsub : Integrable (fun D => looJ μ T L hbar D - looV μ T L D) ν :=
      hJ.sub hV
    apply hsub.congr
    filter_upwards with D
    exact (hI1eq D).symm
  have hI2 : Integrable (looI2 μ T L hbar) ν := by
    change Integrable (fun D => fmean - looJ μ T L hbar D) ν
    exact (integrable_const fmean).sub hJ
  have hI3 : Integrable (looI3 μ T L) ν := by
    change Integrable (fun D => looR0 μ T L D - rmean) ν
    exact hR0.sub (integrable_const rmean)
  have hI1mean : (∫ D, looI1 μ T L hbar D ∂ν) = 0 := by
    calc
      (∫ D, looI1 μ T L hbar D ∂ν) =
          ∫ D, looJ μ T L hbar D - looV μ T L D ∂ν :=
        integral_congr_ae (Filter.Eventually.of_forall hI1eq)
      _ = (∫ D, looJ μ T L hbar D ∂ν) -
          ∫ D, looV μ T L D ∂ν := integral_sub hJ hV
      _ = 0 := by rw [hJmean, hVmean]; ring
  have hI2mean : (∫ D, looI2 μ T L hbar D ∂ν) = 0 := by
    calc
      (∫ D, looI2 μ T L hbar D ∂ν) =
          ∫ D, fmean - looJ μ T L hbar D ∂ν := by rfl
      _ = (∫ _D : Dataset (Observation (k + 1) (m + 1)) (n + 2), fmean ∂ν) -
          ∫ D, looJ μ T L hbar D ∂ν := integral_sub (integrable_const fmean) hJ
      _ = 0 := by simp [hJmean, fmean]
  have hI3mean : (∫ D, looI3 μ T L D ∂ν) = 0 := by
    calc
      (∫ D, looI3 μ T L D ∂ν) = ∫ D, looR0 μ T L D - rmean ∂ν := by rfl
      _ = (∫ D, looR0 μ T L D ∂ν) -
          ∫ _D : Dataset (Observation (k + 1) (m + 1)) (n + 2), rmean ∂ν :=
        integral_sub hR0 (integrable_const rmean)
      _ = 0 := by simp [rmean]
  have hbias : |looBN μ T L hbar| ≤ δ₃ (n + 2) := by
    have hstable := stable_expected_loo_bias μ T L δ₁ δ₂ δ₃ h.2.2.1 n
    have hstable' :
        |(∫ D, looV μ T L D ∂ν) -
          (∫ p : Dataset (Observation (k + 1) (m + 1)) (n + 2) ×
            Observation (k + 1) (m + 1),
            fittedLoss (T (n + 1)) L p.1 p.2
              ∂((Measure.pi fun _ : Fin (n + 2) => μ).prod μ))| ≤ δ₃ (n + 2) := by
      simpa only [looV, ν] using hstable
    have hswap : |rmean - fmean| =
        |(∫ D, looV μ T L D ∂ν) - rmean| := by
      rw [hVmean]
      exact abs_sub_comm _ _
    change |rmean - fmean| ≤ δ₃ (n + 2)
    calc
      |rmean - fmean| = |(∫ D, looV μ T L D ∂ν) - rmean| := hswap
      _ ≤ δ₃ (n + 2) := by rw [hRmean]; exact hstable'
  exact ⟨hR0, hV, hJ, hI1, hI2, hI3,
    hI1mean, hI2mean, hI3mean, hbias⟩

/-- The integral representative and the frozen `L¹` risk agree almost
everywhere, so the pointwise algebra transfers to the frozen risk class. This
identity does not supply any of the separate tail estimates. -/
theorem loo_decomposition_ae {k m n : ℕ}
    {C : ℝ} {δ₁ δ₂ : ℕ → Observation (k + 1) (m + 1) → ℝ}
    {δ₃ : ℕ → ℝ} {c d : ℝ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator (k + 1) (m + 1) (r + 1))
    (L : Responses (m + 1) → Responses (m + 1) → ℝ)
    (h : StandingAssumption (n := n) μ C T L δ₁ δ₂ δ₃ c d) :
    ∀ᵐ D ∂(Measure.pi fun _ : Fin (n + 2) => μ),
      (looRiskL1 μ (T (n + 1)) L (standing_integrable_full_fittedLoss h)) D -
        looV μ T L D = looI1 μ T L (standing_mean_integrable h) D +
        looI2 μ T L (standing_mean_integrable h) D +
        looI3 μ T L D + looBN μ T L (standing_mean_integrable h) := by
  let ν := Measure.pi fun _ : Fin (n + 2) => μ
  have hfull := standing_integrable_full_fittedLoss h
  have hchar := looRiskL1_characterization μ (T (n + 1)) L hfull
  have hcond := stable_condExp_fittedLoss_eq_integral_test μ T L δ₁ δ₂ δ₃
    h.2.2.1 n
  have hpair :
      (fun p : Dataset (Observation (k + 1) (m + 1)) (n + 2) ×
        Observation (k + 1) (m + 1) =>
        (looRiskL1 μ (T (n + 1)) L hfull) p.1) =ᵐ[ν.prod μ]
      (fun p => ∫ z, fittedLoss (T (n + 1)) L p.1 z ∂μ) :=
    hchar.symm.trans hcond
  have hsections := Measure.ae_ae_of_ae_prod hpair
  have hclass : ∀ᵐ D ∂ν,
      (looRiskL1 μ (T (n + 1)) L hfull) D = looR0 μ T L D := by
    filter_upwards [hsections] with D hD
    obtain ⟨z, hz⟩ := hD.exists
    exact hz
  filter_upwards [hclass] with D hD
  rw [hD]
  exact loo_decomposition_pointwise μ T L h D

end LOOConcentration
