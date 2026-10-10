import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory

/-- The supplied raw second moment produces integrability for every actual
Lipschitz function, including on zero-dimensional Euclidean spaces. -/
theorem integrable_lipschitz_of_norm_sq
    {ι : Type*} [Fintype ι] (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hM2 : Integrable (fun x => ‖x‖^2) μ)
    (F : EuclideanSpace ℝ ι → ℝ) (L : NNReal) (hLip : LipschitzWith L F) :
    Integrable F μ := by
  have hNorm : Integrable (fun x : EuclideanSpace ℝ ι => ‖x‖) μ := by
    apply (hM2.add (integrable_const 1)).mono' continuous_norm.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (norm_nonneg _)]
      change ‖x‖ ≤ ‖x‖^2 + 1
      nlinarith [sq_nonneg (‖x‖ - 1)]
  apply integrable_of_norm_sub_le hLip.continuous.aestronglyMeasurable
    (integrable_const (F 0)) (hNorm.const_mul (L : ℝ))
  exact Filter.Eventually.of_forall fun x => by
    simpa only [dist_eq_norm, zero_sub, norm_neg] using hLip.dist_le_mul 0 x

#print axioms integrable_lipschitz_of_norm_sq
end LOOConcentration.Revision
