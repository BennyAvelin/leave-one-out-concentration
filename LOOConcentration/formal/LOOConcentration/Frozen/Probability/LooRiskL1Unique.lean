import LOOConcentration.Frozen.Probability.LooRiskL1Characterization
import Mathlib.MeasureTheory.Function.L1Space.AEEqFun

/-!
Source: `LOOConcentration/v3/BeLa-LOOConcentration-referee-revision.tex`, lines 247–257.
The conditional-risk definition, characterization, and uniqueness theorem
form one audited semantic unit.
-/

set_option autoImplicit false

namespace LOOConcentration

open MeasureTheory

theorem looRiskL1_unique {k m n : ℕ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (T : Estimator (k + 1) (m + 1) (n + 2))
    (L : Responses (m + 1) → Responses (m + 1) → ℝ)
    (hf : Integrable
      (fun p : Dataset (Observation (k + 1) (m + 1)) (n + 2) ×
        Observation (k + 1) (m + 1) => fittedLoss T L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ))
    (R : Dataset (Observation (k + 1) (m + 1)) (n + 2) →₁[
      Measure.pi fun _ : Fin (n + 2) => μ] ℝ)
    (hR : ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ)[
      (fun p : Dataset (Observation (k + 1) (m + 1)) (n + 2) ×
        Observation (k + 1) (m + 1) => fittedLoss T L p.1 p.2) |
        MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[
          ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ)]
      fun p => R p.1) :
    R = looRiskL1 μ T L hf := by
  have hchar := looRiskL1_characterization μ T L hf
  have hpair :
      (fun p : Dataset (Observation (k + 1) (m + 1)) (n + 2) ×
        Observation (k + 1) (m + 1) => R p.1) =ᵐ[
          ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ)]
      fun p => (looRiskL1 μ T L hf) p.1 := hR.symm.trans hchar
  have hset : MeasurableSet
      {D : Dataset (Observation (k + 1) (m + 1)) (n + 2) |
        R D = (looRiskL1 μ T L hf) D} :=
    measurableSet_eq_fun (L1.measurable_coeFn R)
      (L1.measurable_coeFn (looRiskL1 μ T L hf))
  have hsample :
      (fun D => R D) =ᵐ[Measure.pi fun _ : Fin (n + 2) => μ]
        (fun D => (looRiskL1 μ T L hf) D) := by
    have hmap := (ae_map_iff (f := Prod.fst) measurable_fst.aemeasurable hset).2 hpair
    rw [(measurePreserving_fst
      (μ := Measure.pi fun _ : Fin (n + 2) => μ) (ν := μ)).map_eq] at hmap
    exact hmap
  exact Lp.ext hsample

end LOOConcentration
