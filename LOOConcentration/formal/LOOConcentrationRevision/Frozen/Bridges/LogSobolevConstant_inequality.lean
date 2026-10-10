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
import LOOConcentrationRevision.Frozen.Definitions.SobolevPair
import LOOConcentrationRevision.Frozen.Definitions.SobolevEnergy
import LOOConcentrationRevision.Frozen.Definitions.SquareEntropy
import LOOConcentrationRevision.Frozen.Definitions.LogSobolevConstant
import LOOConcentrationRevision.Providers.Bridges.LogSobolevConstant_inequality

/-! Exact revision command for pre-approval elaboration; no declaration approval inferred. -/

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory Filter
open scoped Topology ENNReal

theorem logSobolevConstant_inequality {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (_hfinite : logSobolevConstant μ < ⊤) (u : SobolevPair μ) :
    squareEntropy μ (WithLp.ofLp u.val).1 ≤
      2 * logSobolevConstant μ * sobolevEnergy μ u := by
  exact Providers.logSobolevConstant_inequality μ _hfinite u

end LOOConcentration.Revision
