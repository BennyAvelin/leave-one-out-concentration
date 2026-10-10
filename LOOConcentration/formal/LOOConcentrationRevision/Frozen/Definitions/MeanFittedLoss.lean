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

/-! Exact revision command for pre-approval elaboration; no declaration approval inferred. -/

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory Filter
open scoped Topology ENNReal

noncomputable def meanFittedLoss {k m r : ℕ}
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : Estimator k m (r + 1)) (L : Responses m → Responses m → ℝ)
    (z : Observation k m)
    (_hfin : Integrable
      (fun D : Dataset (Observation k m) (r + 1) => fittedLoss T L D z)
      (Measure.pi fun _ : Fin (r + 1) => μ)) : ℝ :=
  ∫ D : Dataset (Observation k m) (r + 1),
    fittedLoss T L D z ∂Measure.pi fun _ : Fin (r + 1) => μ

end LOOConcentration.Revision
