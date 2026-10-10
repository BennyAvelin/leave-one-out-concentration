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

theorem measurable_observationToEuclidean {k m : ℕ} :
    Measurable (observationToEuclidean : Observation k m →
      EuclideanSpace ℝ (ObservationCoordinate k m)) := by
  apply Continuous.measurable
  exact (PiLp.continuous_toLp (p := (2 : ENNReal))
      (β := fun _ : ObservationCoordinate k m => ℝ)).comp (by
    apply continuous_pi
    intro q
    cases q with
    | inl j => exact (continuous_apply j).comp continuous_fst
    | inr j => exact (continuous_apply j).comp continuous_snd)

end LOOConcentration.Revision
