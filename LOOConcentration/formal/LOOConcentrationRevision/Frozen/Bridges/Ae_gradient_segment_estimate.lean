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
import LOOConcentrationRevision.Providers.Bridges.Ae_gradient_segment_estimate

/-! Exact revision command for pre-approval elaboration; no declaration approval inferred. -/

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory Filter
open scoped Topology ENNReal

theorem ae_gradient_segment_estimate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : EuclideanSpace ℝ ι → ℝ) (_hloc : LocallyLipschitz F) (a b : NNReal)
    (_hgrad : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ ι)),
      DifferentiableAt ℝ F x ∧ ‖gradient F x‖ ≤ (a : ℝ) + (b : ℝ) * ‖x‖)
    (x y : EuclideanSpace ℝ ι) :
    |F x - F y| ≤ ‖x - y‖ * ((a : ℝ) + (b : ℝ) / 2 * (‖x‖ + ‖y‖)) := by
  exact Providers.ae_gradient_segment_estimate F _hloc a b _hgrad x y

end LOOConcentration.Revision
