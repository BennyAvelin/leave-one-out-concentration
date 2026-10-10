import LOOConcentration.FunctionalInequalities.EntropyTensorization
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Finite-coordinate entropy splitting

This generic split identifies the entropy of a finite product test with its
conditional entropy and the entropy of its section means. The carrier is an
arbitrary measurable space; the product laws are the actual finite `Measure.pi`
laws.
-/

set_option autoImplicit false

open MeasureTheory

namespace LOOConcentration.Revision

open LOOConcentration

/-- Split one coordinate from a finite i.i.d. product using the actual
two-factor entropy chain rule and coordinate insertion equivalence. -/
theorem entropy_piFin_succ_split
    {E : Type*} [MeasurableSpace E] {r : ℕ}
    (μ : Measure E) [IsProbabilityMeasure μ]
    (f : (Fin (r + 1) → E) → ℝ)
    (B : ℝ) (hf : Measurable f)
    (hf_nonneg : ∀ D, 0 ≤ f D) (hf_le : ∀ D, f D ≤ B)
    (i : Fin (r + 1)) :
    entropy (Measure.pi fun _ : Fin (r + 1) => μ) f =
      (∫ z, entropy (Measure.pi fun _ : Fin r => μ)
        (fun tail => f ((MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (r + 1) => E) i).symm (z, tail))) ∂μ) +
      entropy μ (fun z => ∫ tail, f ((MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (r + 1) => E) i).symm (z, tail))
          ∂Measure.pi fun _ : Fin r => μ) := by
  let e : (Fin (r + 1) → E) ≃ᵐ E × (Fin r → E) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => E) i
  let ν : Measure (Fin r → E) := Measure.pi fun _ : Fin r => μ
  let F : E × (Fin r → E) → ℝ := fun p => f (e.symm p)
  have hmp : MeasurePreserving e (Measure.pi fun _ : Fin (r + 1) => μ)
      (μ.prod ν) := by
    simpa [e, ν] using
      (measurePreserving_piFinSuccAbove (fun _ : Fin (r + 1) => μ) i)
  have hF : Measurable F := hf.comp e.symm.measurable
  have hF_nonneg : ∀ p, 0 ≤ F p := fun p => hf_nonneg (e.symm p)
  have hF_le : ∀ p, F p ≤ B := fun p => hf_le (e.symm p)
  have hchain := entropy_two_factor_chain_rule μ ν F B hF hF_nonneg hF_le
  have hphi :
      (∫ D, f D * Real.log (f D) ∂Measure.pi fun _ : Fin (r + 1) => μ) =
        ∫ p, F p * Real.log (F p) ∂(μ.prod ν) := by
    calc
      _ = ∫ D, F (e D) * Real.log (F (e D))
          ∂Measure.pi fun _ : Fin (r + 1) => μ := by simp [F]
      _ = _ := hmp.integral_comp' (fun p => F p * Real.log (F p))
  have hint :
      (∫ D, f D ∂Measure.pi fun _ : Fin (r + 1) => μ) =
        ∫ p, F p ∂(μ.prod ν) := by
    calc
      _ = ∫ D, F (e D) ∂Measure.pi fun _ : Fin (r + 1) => μ := by simp [F]
      _ = _ := hmp.integral_comp' F
  have htransport :
      entropy (Measure.pi fun _ : Fin (r + 1) => μ) f = entropy (μ.prod ν) F := by
    unfold entropy
    rw [hphi, hint]
  rw [htransport, hchain]

end LOOConcentration.Revision
