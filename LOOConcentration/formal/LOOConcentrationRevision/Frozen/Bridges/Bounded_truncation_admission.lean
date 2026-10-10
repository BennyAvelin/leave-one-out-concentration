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
import LOOConcentrationRevision.Providers.Bridges.Bounded_truncation_admission

/-! Exact revision command for pre-approval elaboration; no declaration approval inferred. -/

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory Filter
open scoped Topology ENNReal

theorem bounded_truncation_admission {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (_hmoment : Integrable (fun x => ‖x‖ ^ 2) μ)
    (F : EuclideanSpace ℝ ι → ℝ) (_hloc : LocallyLipschitz F) (a b R : NNReal)
    (_hgrad : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ ι)),
      DifferentiableAt ℝ F x ∧ ‖gradient F x‖ ≤ (a : ℝ) + (b : ℝ) * ‖x‖) :
    ∃ u : SobolevPair μ,
      ((WithLp.ofLp u.val).1 : EuclideanSpace ℝ ι → ℝ) =ᵐ[μ]
        (fun x => max (-(R : ℝ)) (min (F x) (R : ℝ))) ∧
      ∀ᵐ x ∂μ,
        ‖((WithLp.ofLp u.val).2 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x‖ ≤
          (a : ℝ) + (b : ℝ) * ‖x‖ := by
  exact LOOConcentration.Revision.Providers.bounded_truncation_admission μ _hmoment F _hloc a b R _hgrad

end LOOConcentration.Revision
