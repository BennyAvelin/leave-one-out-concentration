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

/-! Exact revision command for pre-approval elaboration; no declaration approval inferred. -/

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory Filter
open scoped Topology ENNReal

theorem looRiskL1_characterization {k m n : ℕ}
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : Estimator k m (n + 2))
    (L : Responses m → Responses m → ℝ)
    (hf : Integrable
      (fun p : Dataset (Observation k m) (n + 2) ×
        Observation k m => fittedLoss T L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ))
    :
    ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ)[
      (fun p : Dataset (Observation k m) (n + 2) ×
        Observation k m => fittedLoss T L p.1 p.2) |
        MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[
          ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ)]
      fun p => (looRiskL1 μ T L hf) p.1 := by
  have hsource := condExp_fst_prod_eq_integral_test_of_integrable
    (Measure.pi fun _ : Fin (n + 2) => μ) μ
    (fun p : Dataset (Observation k m) (n + 2) ×
      Observation k m => fittedLoss T L p.1 p.2) hf
  have hclass :
      (fun D => (looRiskL1 μ T L hf) D) =ᵐ[
        Measure.pi fun _ : Fin (n + 2) => μ]
        (fun D => ∫ z, fittedLoss T L D z ∂μ) := by
    exact (hf.integral_prod_left).coeFn_toL1
  have hp := (Measure.quasiMeasurePreserving_fst
    (μ := Measure.pi fun _ : Fin (n + 2) => μ) (ν := μ)).ae_eq_comp hclass
  exact hsource.trans (by simpa only [Function.comp_def] using hp.symm)

end LOOConcentration.Revision
