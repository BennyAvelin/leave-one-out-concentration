import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Gradient.Basic
import LOOConcentrationRevision.Frozen.Bridges.Ae_gradient_segment_estimate
import LOOConcentrationRevision.Correspondence.SourceGradient

set_option autoImplicit false
namespace LOOConcentration.Manuscript
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem expected_loss_segment_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : EuclideanSpace ℝ ι → ℝ) (hLip : LocallyLipschitz f)
    (c d : NNReal)
    (hGradient : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ ι)),
      ‖gradient f x‖ ≤ (c : ℝ) + (d : ℝ) * ‖x‖)
    (x y : EuclideanSpace ℝ ι) :
    |f x - f y| ≤ ‖x - y‖ * ((c : ℝ) + (d : ℝ) / 2 * (‖x‖ + ‖y‖)) := by
  exact LOOConcentration.Revision.ae_gradient_segment_estimate f hLip c d
    ((LOOConcentration.Correspondence.mean_gradient_iff_native_bound f hLip
      (c : ℝ) (d : ℝ)).mpr hGradient) x y

end LOOConcentration.Manuscript
