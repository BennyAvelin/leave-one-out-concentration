import LOOConcentrationManuscript.Internal.GaussianKernelAmbientRegularity
import Mathlib.Analysis.Calculus.Gradient.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open ProbabilityTheory
open scoped ContDiff

/-- Whole-dataset smoothness supplies the actual gradient of the literal
Gaussian predictor; no differentiability gate is exposed to the caller. -/
theorem gaussianKernel_predictor_ambient_hasGradientAt
    (h δ : ℝ) (hh : 0 < h) (hδ : 0 < δ) (r : ℕ) (x : ℝ)
    (D : EuclideanSpace ℝ (Fin (r+1) × (Fin 1 ⊕ Fin 1))) :
    let Kh := fun t : ℝ => gaussianPDFReal 0 1 (t/h)/h
    let T := fun E : EuclideanSpace ℝ (Fin (r+1) × (Fin 1 ⊕ Fin 1)) =>
      (∑ i : Fin (r+1), Kh (x-E (i,Sum.inl 0))*E (i,Sum.inr 0)) /
        ((∑ i : Fin (r+1), Kh (x-E (i,Sum.inl 0)))+(r+1 : ℝ)*δ)
    HasGradientAt T (gradient T D) D := by
  intro Kh T
  have hSmooth : ContDiff ℝ ∞ T := gaussianKernel_predictor_ambient_contDiff h δ hh hδ r x
  exact (hSmooth.differentiable (by norm_num) D).hasGradientAt

end LOOConcentration.Manuscript.Internal
