import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Conditional expectation on a sample/test product space

The training sample is the first coordinate and an independent test observation
is the second coordinate. This reusable measure-theoretic lemma supplies the
conditional-risk identity used by the LOOConcentration manuscript.
-/

set_option autoImplicit false

namespace LOOConcentration

open MeasureTheory
open scoped MeasureTheory

theorem condExp_fst_prod_eq_integral_test
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (ν : Measure A) (μ : Measure B)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (f : A × B → ℝ) (hf : Integrable f (ν.prod μ))
    (hfm : StronglyMeasurable f) :
    (ν.prod μ)[f | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[ν.prod μ]
      fun p => ∫ z, f (p.1, z) ∂μ := by
  let g : A × B → ℝ := fun p => ∫ z, f (p.1, z) ∂μ
  have hg_int : Integrable g (ν.prod μ) := hf.integral_prod_left.comp_fst μ
  have hg_meas : StronglyMeasurable[MeasurableSpace.comap Prod.fst inferInstance] g :=
    hfm.integral_prod_right'.comp_measurable (comap_measurable Prod.fst)
  refine (ae_eq_condExp_of_forall_setIntegral_eq
    (measurable_fst.comap_le :
      MeasurableSpace.comap (Prod.fst : A × B → A) inferInstance ≤
        (inferInstance : MeasurableSpace (A × B)))
    hf (fun _ _ _ => hg_int.integrableOn) ?_ hg_meas.aestronglyMeasurable).symm
  rintro s ⟨t, ht, rfl⟩ _
  have hset : (Prod.fst : A × B → A) ⁻¹' t = t ×ˢ (Set.univ : Set B) := by
    ext p
    simp
  rw [hset]
  rw [setIntegral_prod g hg_int.integrableOn, setIntegral_prod f hf.integrableOn]
  simp only [setIntegral_univ]
  simp [g]

theorem condExp_fst_prod_eq_integral_test_of_integrable
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (ν : Measure A) (μ : Measure B)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (f : A × B → ℝ) (hf : Integrable f (ν.prod μ)) :
    (ν.prod μ)[f | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[ν.prod μ]
      fun p => ∫ z, f (p.1, z) ∂μ := by
  let f₀ : A × B → ℝ := hf.aestronglyMeasurable.mk f
  have h₀ : StronglyMeasurable f₀ :=
    hf.aestronglyMeasurable.stronglyMeasurable_mk
  have heq : f =ᵐ[ν.prod μ] f₀ := hf.aestronglyMeasurable.ae_eq_mk
  have h₀int : Integrable f₀ (ν.prod μ) := hf.congr heq
  have hcond := condExp_fst_prod_eq_integral_test ν μ f₀ h₀int h₀
  have hsection : ∀ᵐ D ∂ν,
      (fun z => f₀ (D, z)) =ᵐ[μ] (fun z => f (D, z)) :=
    Measure.ae_ae_of_ae_prod heq.symm
  have hmean :
      (fun D => ∫ z, f₀ (D, z) ∂μ) =ᵐ[ν]
        (fun D => ∫ z, f (D, z) ∂μ) :=
    hsection.mono (fun D hD => integral_congr_ae hD)
  have hp := (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := μ)).ae_eq_comp hmean
  exact (condExp_congr_ae heq).trans (hcond.trans (by
    simpa only [Function.comp_def] using hp))

end LOOConcentration
