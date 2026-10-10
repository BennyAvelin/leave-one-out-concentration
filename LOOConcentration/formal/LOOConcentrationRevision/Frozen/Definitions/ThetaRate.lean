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

noncomputable def thetaRate
    (C M₂ : ℝ) (_hC : 0 ≤ C) (_hM₂ : 0 ≤ M₂)
    (r : ℕ) (_hr : 1 ≤ r)
    (t : ℝ) (_ht : 0 < t)
    (a b : ℝ) (_ha : 0 ≤ a) (_hb : 0 ≤ b) : ℝ :=
  if C = 0 then 0 else
  if a ^ 2 + 2 * b ^ 2 * (r : ℝ) * M₂ = 0 then
    if b = 0 then 0 else Real.exp (-(t / (8 * C * b)))
  else if b = 0 then
    Real.exp (-(t ^ 2 / (8 * C * (a ^ 2 + 2 * b ^ 2 * (r : ℝ) * M₂))))
  else
    Real.exp (-(min
      (t ^ 2 / (8 * C * (a ^ 2 + 2 * b ^ 2 * (r : ℝ) * M₂)))
      (t / (8 * C * b))))

end LOOConcentration.Revision
