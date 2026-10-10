import LOOConcentration.Frozen.Foundations.Estimator
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Positivity

set_option autoImplicit false
namespace LOOConcentration.Manuscript
open MeasureTheory

noncomputable def coordinateClip (b : {b : ℝ // 0 ≤ b}) (x : ℝ) : ℝ :=
  max (min x b.val) (-b.val)

end LOOConcentration.Manuscript
