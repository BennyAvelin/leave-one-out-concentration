import LOOConcentration.Probability.SampleTestLaw
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Transport through delete-one sample coordinates

These lemmas expose the integral, event, and nonnegative-integrand transports
for the map sending a full sample to its deleted sample and held-out point.
-/

set_option autoImplicit false

namespace LOOConcentration

open MeasureTheory
open scoped MeasureTheory ENNReal

/-- The pushforward of the full sample law is the deleted-sample law times the
held-out observation law. At full sample size `n + 2`, the deleted sample has
size `n + 1 = (n + 2) - 1`.
-/
theorem deleted_sample_and_heldout_map_eq
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (i : Fin (n + 2)) :
    (Measure.pi fun _ : Fin (n + 2) => μ).map
      (fun D : Dataset (Observation k m) (n + 2) => (deleteAt D i, D i)) =
      (Measure.pi fun _ : Fin (n + 1) => μ).prod μ := by
  exact (deleted_sample_and_heldout_measurePreserving μ i).map_eq

/-- Measurability of a real-valued section is preserved when it is composed
with the delete-one/held-out map.
-/
theorem deleted_section_measurable
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (i : Fin (n + 2))
    (f : Dataset (Observation k m) (n + 1) × Observation k m → ℝ)
    (hf : Measurable f) :
    Measurable (fun D : Dataset (Observation k m) (n + 2) =>
      f (deleteAt D i, D i)) := by
  exact hf.comp (deleted_sample_and_heldout_measurePreserving μ i).measurable

/-- Integrability of a real-valued section is preserved under the
delete-one/held-out map.
-/
theorem deleted_section_integrable
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (i : Fin (n + 2))
    (f : Dataset (Observation k m) (n + 1) × Observation k m → ℝ)
    (hf : Integrable f ((Measure.pi fun _ : Fin (n + 1) => μ).prod μ)) :
    Integrable
      (fun D : Dataset (Observation k m) (n + 2) => f (deleteAt D i, D i))
      (Measure.pi fun _ : Fin (n + 2) => μ) := by
  exact (deleted_sample_and_heldout_measurePreserving μ i).integrable_comp_of_integrable hf

/-- Under an a.e.-strongly-measurable product section, integrability is
equivalent before and after the delete-one/held-out map. This direction lets a
stability assumption stated on full samples provide product-law integrability.
-/
theorem deleted_section_integrable_iff
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (i : Fin (n + 2))
    (f : Dataset (Observation k m) (n + 1) × Observation k m → ℝ)
    (hf : AEStronglyMeasurable f ((Measure.pi fun _ : Fin (n + 1) => μ).prod μ)) :
    Integrable
      (fun D : Dataset (Observation k m) (n + 2) => f (deleteAt D i, D i))
      (Measure.pi fun _ : Fin (n + 2) => μ) ↔
    Integrable f ((Measure.pi fun _ : Fin (n + 1) => μ).prod μ) := by
  exact (deleted_sample_and_heldout_measurePreserving μ i).integrable_comp hf

/-- Integral transport for an integrable real-valued section. The composition
is integrable by `deleted_section_integrable`.
-/
theorem deleted_section_integral
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (i : Fin (n + 2))
    (f : Dataset (Observation k m) (n + 1) × Observation k m → ℝ)
    (hf : Integrable f ((Measure.pi fun _ : Fin (n + 1) => μ).prod μ)) :
    integral (Measure.pi fun _ : Fin (n + 2) => μ)
      (fun D : Dataset (Observation k m) (n + 2) => f (deleteAt D i, D i)) =
    integral ((Measure.pi fun _ : Fin (n + 1) => μ).prod μ)
      (fun p : Dataset (Observation k m) (n + 1) × Observation k m => f p) := by
  let hmp := deleted_sample_and_heldout_measurePreserving μ i
  have hfm : AEStronglyMeasurable f
      ((Measure.pi fun _ : Fin (n + 2) => μ).map
        (fun D : Dataset (Observation k m) (n + 2) => (deleteAt D i, D i))) := by
    rw [hmp.map_eq]
    exact hf.aestronglyMeasurable
  rw [← hmp.map_eq]
  exact (integral_map hmp.measurable.aemeasurable hfm).symm

/-- The probability of a measurable event in deleted-sample/held-out
coordinates equals the probability of its preimage in the original sample.
-/
theorem deleted_tail_integral
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (i : Fin (n + 2))
    (s : Set (Dataset (Observation k m) (n + 1) × Observation k m))
    (hs : MeasurableSet s) :
    (Measure.pi fun _ : Fin (n + 2) => μ)
      ((fun D : Dataset (Observation k m) (n + 2) => (deleteAt D i, D i)) ⁻¹' s) =
    ((Measure.pi fun _ : Fin (n + 1) => μ).prod μ) s := by
  let hmp := deleted_sample_and_heldout_measurePreserving μ i
  calc
    (Measure.pi fun _ : Fin (n + 2) => μ)
        ((fun D : Dataset (Observation k m) (n + 2) => (deleteAt D i, D i)) ⁻¹' s) =
        ((Measure.pi fun _ : Fin (n + 2) => μ).map
          (fun D : Dataset (Observation k m) (n + 2) => (deleteAt D i, D i))) s :=
      (Measure.map_apply hmp.measurable hs).symm
    _ = ((Measure.pi fun _ : Fin (n + 1) => μ).prod μ) s := by rw [hmp.map_eq]

/-- Transport the integral of a measurable nonnegative-valued integrand. This
applies in particular to `‖f ·‖ₑ ^ p`; no finiteness assumption is needed.
-/
theorem deleted_power_integral
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (i : Fin (n + 2))
    (g : Dataset (Observation k m) (n + 1) × Observation k m → ℝ≥0∞)
    (hg : Measurable g) :
    lintegral (Measure.pi fun _ : Fin (n + 2) => μ)
      (fun D : Dataset (Observation k m) (n + 2) => g (deleteAt D i, D i)) =
    lintegral ((Measure.pi fun _ : Fin (n + 1) => μ).prod μ)
      (fun p : Dataset (Observation k m) (n + 1) × Observation k m => g p) := by
  let hmp := deleted_sample_and_heldout_measurePreserving μ i
  rw [← hmp.map_eq]
  exact (lintegral_map hg hmp.measurable).symm

/-- The `eLpNorm'` of a measurable real-valued section is unchanged by the
delete-one/held-out transport, for every real exponent.
-/
theorem deleted_eLpNorm'_comp
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (i : Fin (n + 2))
    (f : Dataset (Observation k m) (n + 1) × Observation k m → ℝ)
    (q : ℝ) (hf : Measurable f) :
    eLpNorm' (fun D : Dataset (Observation k m) (n + 2) =>
      f (deleteAt D i, D i)) q (Measure.pi fun _ : Fin (n + 2) => μ) =
    eLpNorm' f q ((Measure.pi fun _ : Fin (n + 1) => μ).prod μ) := by
  rw [eLpNorm'_eq_lintegral_enorm, eLpNorm'_eq_lintegral_enorm]
  congr 1
  exact deleted_power_integral μ i (fun p => ‖f p‖ₑ ^ q) (hf.enorm.pow_const q)

end LOOConcentration
