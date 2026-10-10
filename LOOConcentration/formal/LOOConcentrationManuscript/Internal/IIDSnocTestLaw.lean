import LOOConcentration.Probability.SampleTestLaw
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal
open MeasureTheory

/-- Appending an independent draw produces the literal ordered iid law. -/
theorem iid_snoc_measurePreserving
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (N : ℕ) :
    MeasurePreserving (fun p : (Fin N → α) × α => Fin.snoc p.1 p.2)
      ((Measure.pi (fun _ : Fin N => μ)).prod μ)
      (Measure.pi (fun _ : Fin (N + 1) => μ)) := by
  have h := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (N + 1) => μ) (Fin.last N)).symm
  have hs := h.comp Measure.measurePreserving_swap
  simpa only [Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_last', Prod.swap] using hs

/-- The same append map retains an independent fresh test point. -/
theorem iid_snoc_fresh_test_measurePreserving
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (N : ℕ) :
    MeasurePreserving
      (fun p : ((Fin N → α) × α) × α => (Fin.snoc p.1.1 p.1.2, p.2))
      (((Measure.pi (fun _ : Fin N => μ)).prod μ).prod μ)
      ((Measure.pi (fun _ : Fin (N + 1) => μ)).prod μ) := by
  exact (iid_snoc_measurePreserving μ N).prod (MeasurePreserving.id μ)

/-- True integrability and exact full-fit expectation transport under the
actual append-and-test map, not a supplied iid distribution identity. -/
theorem iid_snoc_fresh_test_integrable_integral
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (N : ℕ) (f : (Fin (N + 1) → α) × α → ℝ)
    (hf : Integrable f ((Measure.pi (fun _ : Fin (N + 1) => μ)).prod μ)) :
    Integrable (fun p : ((Fin N → α) × α) × α => f (Fin.snoc p.1.1 p.1.2, p.2))
      (((Measure.pi (fun _ : Fin N => μ)).prod μ).prod μ) ∧
    (∫ p : ((Fin N → α) × α) × α, f (Fin.snoc p.1.1 p.1.2, p.2)
      ∂(((Measure.pi (fun _ : Fin N => μ)).prod μ).prod μ)) =
      ∫ p : (Fin (N + 1) → α) × α, f p
        ∂((Measure.pi (fun _ : Fin (N + 1) => μ)).prod μ) := by
  have h := iid_snoc_fresh_test_measurePreserving μ N
  refine ⟨h.integrable_comp_of_integrable hf, ?_⟩
  have hm : AEStronglyMeasurable f
      (Measure.map (fun p : ((Fin N → α) × α) × α =>
        (Fin.snoc p.1.1 p.1.2, p.2))
        (((Measure.pi (fun _ : Fin N => μ)).prod μ).prod μ)) := by
    rw [h.map_eq]
    exact hf.aestronglyMeasurable
  have heq := integral_map h.measurable.aemeasurable hm
  rw [h.map_eq] at heq
  exact heq.symm


/-- Ignoring the added observation keeps the original independent training
sample and fresh test law, even under the three-factor source law. -/
theorem iid_ignored_added_fresh_test_measurePreserving
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (N : ℕ) :
    MeasurePreserving
      (fun p : ((Fin N → α) × α) × α => (p.1.1, p.2))
      (((Measure.pi (fun _ : Fin N => μ)).prod μ).prod μ)
      ((Measure.pi (fun _ : Fin N => μ)).prod μ) := by
  have h := ((MeasurePreserving.id (Measure.pi (fun _ : Fin N => μ))).prod
    (measurePreserving_snd (μ := μ) (ν := μ))).comp
      (measurePreserving_prodAssoc (Measure.pi (fun _ : Fin N => μ)) μ μ)
  exact h

/-- True integrability and exact short-fit expectation transport under the
actual short-sample-and-test projection, not a supplied iid distribution identity. -/
theorem iid_ignored_added_fresh_test_integrable_integral
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (N : ℕ) (f : (Fin N → α) × α → ℝ)
    (hf : Integrable f ((Measure.pi (fun _ : Fin N => μ)).prod μ)) :
    Integrable (fun p : ((Fin N → α) × α) × α => f (p.1.1, p.2))
      (((Measure.pi (fun _ : Fin N => μ)).prod μ).prod μ) ∧
    (∫ p : ((Fin N → α) × α) × α, f (p.1.1, p.2)
      ∂(((Measure.pi (fun _ : Fin N => μ)).prod μ).prod μ)) =
      ∫ p : (Fin N → α) × α, f p
        ∂((Measure.pi (fun _ : Fin N => μ)).prod μ) := by
  have h := iid_ignored_added_fresh_test_measurePreserving μ N
  refine ⟨h.integrable_comp_of_integrable hf, ?_⟩
  have hm : AEStronglyMeasurable f
      (Measure.map (fun p : ((Fin N → α) × α) × α =>
        (p.1.1, p.2))
        (((Measure.pi (fun _ : Fin N => μ)).prod μ).prod μ)) := by
    rw [h.map_eq]
    exact hf.aestronglyMeasurable
  have heq := integral_map h.measurable.aemeasurable hm
  rw [h.map_eq] at heq
  exact heq.symm

end LOOConcentration.Manuscript.Internal
