import LOOConcentration.Frozen.Foundations.Observation
import LOOConcentration.FunctionalInequalities.EntropyTensorization
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Finite-coordinate entropy splitting

This module specializes the two-factor entropy identity to the actual finite
product law on observations. The split isolates any chosen coordinate and
leaves the remaining coordinates in their `Measure.pi` law.
-/

set_option autoImplicit false

namespace LOOConcentration

open MeasureTheory

/-- Split one coordinate from a finite i.i.d. observation product. The identity
is an induction step for finite-product entropy tensorization. -/
theorem entropy_piFin_succ_split
    {k m r : ℕ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (f : (Fin (r + 1) → Observation (k + 1) (m + 1)) → ℝ)
    (B : ℝ) (hf : Measurable f)
    (hf_nonneg : ∀ D, 0 ≤ f D) (hf_le : ∀ D, f D ≤ B)
    (i : Fin (r + 1)) :
    entropy (Measure.pi fun _ : Fin (r + 1) => μ) f =
      (∫ z, entropy (Measure.pi fun _ : Fin r => μ)
        (fun tail => f ((MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (r + 1) => Observation (k + 1) (m + 1)) i).symm (z, tail))) ∂μ) +
      entropy μ (fun z => ∫ tail, f ((MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (r + 1) => Observation (k + 1) (m + 1)) i).symm (z, tail))
          ∂Measure.pi fun _ : Fin r => μ) := by
  let E := Observation (k + 1) (m + 1)
  let e : (Fin (r + 1) → E) ≃ᵐ E × (Fin r → E) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => E) i
  let ν : Measure (Fin r → E) := Measure.pi fun _ : Fin r => μ
  let F : E × (Fin r → E) → ℝ := fun p => f (e.symm p)
  have hmp : MeasurePreserving e (Measure.pi fun _ : Fin (r + 1) => μ)
      (μ.prod ν) := by
    simpa [e, ν, E] using
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

end LOOConcentration
