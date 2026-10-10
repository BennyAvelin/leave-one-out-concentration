import LOOConcentration.Geometry.NormTransport
import LOOConcentration.Frozen.Foundations.FittedLoss
import LOOConcentration.Frozen.Foundations.LooEstimate
import LOOConcentration.Probability.ProductConditionalRisk
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Data.EReal.Basic
import LOOConcentrationRevision.Frozen.Definitions.LooRiskL1
import LOOConcentrationRevision.Frozen.Definitions.LooRiskL1_characterization

/-! Exact revision command for pre-approval elaboration; no declaration approval inferred. -/

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory Filter
open scoped Topology ENNReal

theorem looRiskL1_unique {k m n : ℕ}
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : Estimator k m (n + 2))
    (L : Responses m → Responses m → ℝ)
    (hf : Integrable
      (fun p : Dataset (Observation k m) (n + 2) ×
        Observation k m => fittedLoss T L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ))
    (R : Dataset (Observation k m) (n + 2) →₁[
      Measure.pi fun _ : Fin (n + 2) => μ] ℝ)
    (hR : ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ)[
      (fun p : Dataset (Observation k m) (n + 2) ×
        Observation k m => fittedLoss T L p.1 p.2) |
        MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[
          ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ)]
      fun p => R p.1) :
    R = looRiskL1 μ T L hf := by
  have hchar := looRiskL1_characterization μ T L hf
  have hpair :
      (fun p : Dataset (Observation k m) (n + 2) ×
        Observation k m => R p.1) =ᵐ[
          ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ)]
      fun p => (looRiskL1 μ T L hf) p.1 := hR.symm.trans hchar
  have hset : MeasurableSet
      {D : Dataset (Observation k m) (n + 2) |
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

end LOOConcentration.Revision
