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
import LOOConcentrationRevision.Frozen.Definitions.LogSobolevConstant
import LOOConcentrationRevision.Frozen.Definitions.Measurable_observationToEuclidean

/-! Exact revision command for pre-approval elaboration; no declaration approval inferred. -/

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory Filter
open scoped Topology ENNReal

noncomputable def observationLogSobolevConstant {k m : ℕ}
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ] : ℝ≥0∞ :=
  letI := μ.isProbabilityMeasure_map measurable_observationToEuclidean.aemeasurable
  logSobolevConstant (μ.map observationToEuclidean)

end LOOConcentration.Revision
