/-
Copyright (c) 2026 Benny Avelin and Lauri Viitasaari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin, Lauri Viitasaari
-/
import Mathlib.MeasureTheory.Constructions.Pi
import LOOConcentration.Frozen.Foundations.FittedLoss
import LOOConcentration.Probability.ProductConditionalRisk

/-!
# Existence and uniqueness of conditional risk

The independent-test integral determines the unique integrable risk class whose
pullback to the sample/test product is the conditional expected fitted loss.
The construction precedes the exported risk definition and uses its actual
joint-integrability premise.
-/

set_option autoImplicit false

namespace LOOConcentration.Revision

open MeasureTheory
open scoped ENNReal

/-- The conditional expected fitted loss determines a unique sample-law `L¹` class. -/
theorem exists_unique_conditional_risk {k m n : ℕ}
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : Estimator k m (n + 2)) (L : Responses m → Responses m → ℝ)
    (hf : Integrable
      (fun p : Dataset (Observation k m) (n + 2) × Observation k m =>
        fittedLoss T L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ)) :
    ∃! R : Dataset (Observation k m) (n + 2) →₁[
        Measure.pi fun _ : Fin (n + 2) => μ] ℝ,
      ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ)[
        (fun p : Dataset (Observation k m) (n + 2) × Observation k m =>
          fittedLoss T L p.1 p.2) | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[
          ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ)] fun p => R p.1 := by
  let R := (hf.integral_prod_left).toL1 (fun D => ∫ z, fittedLoss T L D z ∂μ)
  have hsource := condExp_fst_prod_eq_integral_test_of_integrable
    (Measure.pi fun _ : Fin (n + 2) => μ) μ
    (fun p : Dataset (Observation k m) (n + 2) × Observation k m =>
      fittedLoss T L p.1 p.2) hf
  have hclass : (fun D => R D) =ᵐ[Measure.pi fun _ : Fin (n + 2) => μ]
      (fun D => ∫ z, fittedLoss T L D z ∂μ) :=
    (hf.integral_prod_left).coeFn_toL1
  have hp := (Measure.quasiMeasurePreserving_fst
    (μ := Measure.pi fun _ : Fin (n + 2) => μ) (ν := μ)).ae_eq_comp hclass
  have hchar := hsource.trans (by simpa only [Function.comp_def] using hp.symm)
  refine ⟨R, hchar, ?_⟩
  intro S hS
  have hpair :
      (fun p : Dataset (Observation k m) (n + 2) × Observation k m => S p.1) =ᵐ[
        ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ)] fun p => R p.1 :=
    hS.symm.trans hchar
  have hset : MeasurableSet
      {D : Dataset (Observation k m) (n + 2) | S D = R D} :=
    measurableSet_eq_fun (L1.measurable_coeFn S) (L1.measurable_coeFn R)
  have hsample : (fun D => S D) =ᵐ[Measure.pi fun _ : Fin (n + 2) => μ]
      (fun D => R D) := by
    have hmap := (ae_map_iff (f := Prod.fst) measurable_fst.aemeasurable hset).2 hpair
    rw [(measurePreserving_fst
      (μ := Measure.pi fun _ : Fin (n + 2) => μ) (ν := μ)).map_eq] at hmap
    exact hmap
  exact Lp.ext hsample

end LOOConcentration.Revision
