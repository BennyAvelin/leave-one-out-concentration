import LOOConcentration.Frozen.Foundations.DeleteAt
import LOOConcentration.Frozen.Foundations.Observation
import Mathlib.Probability.Independence.Basic

/-!
# The ordered i.i.d. sample and independent test observation

These facts verify the probabilistic meaning of the product law used in the
conditional-risk bridge.
-/

set_option autoImplicit false

namespace LOOConcentration

open MeasureTheory
open ProbabilityTheory

theorem sample_coordinates_independent
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ] :
    iIndepFun
      (fun i : Fin n => fun D : Dataset (Observation k m) n => D i)
      (Measure.pi fun _ : Fin n => μ) := by
  exact iIndepFun_pi (X := fun _ : Fin n => id) (fun _ => aemeasurable_id)

theorem sample_coordinate_law
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (i : Fin n) :
    (Measure.pi fun _ : Fin n => μ).map
      (fun D : Dataset (Observation k m) n => D i) = μ := by
  simpa using Measure.pi_map_eval (μ := fun _ : Fin n => μ) i

theorem sample_coordinate_measurePreserving
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (i : Fin n) :
    MeasurePreserving
      (fun D : Dataset (Observation k m) n => D i)
      (Measure.pi fun _ : Fin n => μ) μ :=
  ⟨measurable_pi_apply i, sample_coordinate_law μ i⟩

theorem sample_test_independent
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ] :
    (Prod.fst : Dataset (Observation k m) n × Observation k m →
      Dataset (Observation k m) n) ⟂ᵢ[((Measure.pi fun _ : Fin n => μ).prod μ)]
    (Prod.snd : Dataset (Observation k m) n × Observation k m →
      Observation k m) := by
  exact indepFun_prod measurable_id measurable_id

theorem sample_test_marginals
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ] :
    (((Measure.pi fun _ : Fin n => μ).prod μ).map
      (Prod.fst : Dataset (Observation k m) n × Observation k m →
        Dataset (Observation k m) n) =
      Measure.pi fun _ : Fin n => μ) ∧
    (((Measure.pi fun _ : Fin n => μ).prod μ).map
      (Prod.snd : Dataset (Observation k m) n × Observation k m →
        Observation k m) = μ) := by
  constructor
  · exact measurePreserving_fst.map_eq
  · exact measurePreserving_snd.map_eq

theorem deleted_sample_and_heldout_measurePreserving
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (i : Fin (n + 2)) :
    MeasurePreserving
      (fun D : Dataset (Observation k m) (n + 2) => (deleteAt D i, D i))
      (Measure.pi fun _ : Fin (n + 2) => μ)
      ((Measure.pi fun _ : Fin (n + 1) => μ).prod μ) := by
  have h := (Measure.measurePreserving_swap.comp
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 2) => μ) i))
  change MeasurePreserving
    (fun D : Dataset (Observation k m) (n + 2) =>
      (fun j : Fin (n + 1) => D (i.succAbove j), D i))
    (Measure.pi fun _ : Fin (n + 2) => μ)
    ((Measure.pi fun _ : Fin (n + 1) => μ).prod μ) at h
  exact h

theorem deleted_sample_and_heldout_law
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (i : Fin (n + 2)) :
    (Measure.pi fun _ : Fin (n + 2) => μ).map
      (fun D : Dataset (Observation k m) (n + 2) => (deleteAt D i, D i)) =
      (Measure.pi fun _ : Fin (n + 1) => μ).prod μ :=
  (deleted_sample_and_heldout_measurePreserving μ i).map_eq

end LOOConcentration
