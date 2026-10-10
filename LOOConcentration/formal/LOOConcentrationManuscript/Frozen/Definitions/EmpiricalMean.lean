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

noncomputable def empiricalMean (r : ℕ)
    (D : EuclideanSpace ℝ (Fin (r + 1))) : ℝ :=
  ((r + 1 : ℕ) : ℝ)⁻¹ * ∑ i : Fin (r + 1), D i

end LOOConcentration.Manuscript
