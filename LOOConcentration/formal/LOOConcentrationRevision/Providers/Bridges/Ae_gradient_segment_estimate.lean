import LOOConcentrationRevision.FunctionalInequalities.GradientAllPairs

set_option autoImplicit false
namespace LOOConcentration.Revision.Providers
open MeasureTheory Filter
open scoped Topology ENNReal

theorem ae_gradient_segment_estimate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : EuclideanSpace ℝ ι → ℝ) (_hloc : LocallyLipschitz F) (a b : NNReal)
    (_hgrad : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ ι)),
      DifferentiableAt ℝ F x ∧ ‖gradient F x‖ ≤ (a : ℝ) + (b : ℝ) * ‖x‖)
    (x y : EuclideanSpace ℝ ι) :
    |F x - F y| ≤ ‖x - y‖ * ((a : ℝ) + (b : ℝ) / 2 * (‖x‖ + ‖y‖)) := by
  exact LOOConcentration.Revision.ae_gradient_segment_estimate_of_ae F _hloc a b _hgrad x y

end LOOConcentration.Revision.Providers
