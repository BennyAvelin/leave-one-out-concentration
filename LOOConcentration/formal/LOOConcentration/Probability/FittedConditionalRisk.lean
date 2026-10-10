import LOOConcentration.Probability.ProductConditionalRisk
import LOOConcentration.Probability.SampleTestLaw
import LOOConcentration.Frozen.Foundations.FittedLoss
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Conditional fitted risk for the LOOConcentration model

The first coordinate is an ordered independent sample and the second coordinate
is a fresh observation with the same law. Integrability and measurability are
explicit here; later source-facing assumptions must prove them.
-/

set_option autoImplicit false

namespace LOOConcentration

open MeasureTheory
open scoped MeasureTheory

theorem condExp_fittedLoss_eq_integral_test
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : Estimator k m (n + 2))
    (L : Responses m → Responses m → ℝ)
    (hf : Integrable
      (fun p : Dataset (Observation k m) (n + 2) × Observation k m =>
        fittedLoss T L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ))
    (hfm : Measurable
      (fun p : Dataset (Observation k m) (n + 2) × Observation k m =>
        fittedLoss T L p.1 p.2)) :
    ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ)[
      (fun p : Dataset (Observation k m) (n + 2) × Observation k m =>
        fittedLoss T L p.1 p.2) |
        MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[((Measure.pi fun _ : Fin (n + 2) => μ).prod μ)]
      fun p => ∫ z, fittedLoss T L p.1 z ∂μ := by
  exact condExp_fst_prod_eq_integral_test
    (Measure.pi fun _ : Fin (n + 2) => μ) μ _ hf hfm.stronglyMeasurable

theorem integrable_heldout_fittedLoss
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : Estimator k m (n + 1))
    (L : Responses m → Responses m → ℝ)
    (i : Fin (n + 2))
    (hf : Integrable
      (fun p : Dataset (Observation k m) (n + 1) × Observation k m =>
        fittedLoss T L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 1) => μ).prod μ)) :
    Integrable
      (fun D : Dataset (Observation k m) (n + 2) =>
        fittedLoss T L (deleteAt D i) (D i))
      (Measure.pi fun _ : Fin (n + 2) => μ) := by
  exact (deleted_sample_and_heldout_measurePreserving μ i).integrable_comp_of_integrable hf

theorem integral_heldout_fittedLoss
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : Estimator k m (n + 1))
    (L : Responses m → Responses m → ℝ)
    (i : Fin (n + 2))
    (hf : Integrable
      (fun p : Dataset (Observation k m) (n + 1) × Observation k m =>
        fittedLoss T L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 1) => μ).prod μ)) :
    (∫ D : Dataset (Observation k m) (n + 2),
      fittedLoss T L (deleteAt D i) (D i) ∂Measure.pi fun _ : Fin (n + 2) => μ) =
    ∫ p : Dataset (Observation k m) (n + 1) × Observation k m,
      fittedLoss T L p.1 p.2 ∂((Measure.pi fun _ : Fin (n + 1) => μ).prod μ) := by
  let φ : Dataset (Observation k m) (n + 2) →
      Dataset (Observation k m) (n + 1) × Observation k m :=
    fun D => (deleteAt D i, D i)
  have hmp := deleted_sample_and_heldout_measurePreserving μ i
  have hfm : AEStronglyMeasurable
      (fun p : Dataset (Observation k m) (n + 1) × Observation k m =>
        fittedLoss T L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 2) => μ).map φ) := by
    rw [hmp.map_eq]
    exact hf.aestronglyMeasurable
  simpa only [φ, hmp.map_eq, Function.comp_def] using
    (integral_map hmp.measurable.aemeasurable hfm).symm

end LOOConcentration
