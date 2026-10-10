import LOOConcentrationManuscript.Internal.GaussianKernelAmbientRegularity
import LOOConcentrationManuscript.Internal.GaussianKernelFeatureDerivative
import LOOConcentrationManuscript.Internal.KernelResponseQuotientDerivative
import LOOConcentration.Geometry.LipschitzCoordinateEnergy
import Mathlib.Analysis.Calculus.Gradient.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open ProbabilityTheory
open scoped ContDiff

private theorem gradient_coordinate_eq_updated_section
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : EuclideanSpace ℝ ι → ℝ) (D : EuclideanSpace ℝ ι) (q : ι)
    (hf : DifferentiableAt ℝ f D) :
    gradient f D q =
      deriv (fun t : ℝ => f (WithLp.toLp 2 (Function.update (fun k => D k) q t))) (D q) := by
  have hPath (t : ℝ) :
      LOOConcentration.euclideanCoordinatePath D q t =
        WithLp.toLp 2 (Function.update (fun k => D k) q t) := by
    ext k
    by_cases hk : k=q
    · subst k
      simp [LOOConcentration.euclideanCoordinatePath]
    · simp [LOOConcentration.euclideanCoordinatePath,hk]
  have hSection :
      LOOConcentration.euclideanCoordinateSection f D q =
        fun t : ℝ => f (WithLp.toLp 2 (Function.update (fun k => D k) q t)) := by
    funext t
    exact congrArg f (hPath t)
  have hDeriv := LOOConcentration.deriv_euclideanCoordinateSection_eq_fderiv f D q hf
  rw [hSection] at hDeriv
  have hDual : fderiv ℝ f D (EuclideanSpace.single q (1 : ℝ)) = gradient f D q := by
    rw [← toDual_gradient]
    rw [InnerProductSpace.toDual_apply_apply,EuclideanSpace.inner_single_right]
    simp
  have hDeriv' : deriv (fun t : ℝ => f (WithLp.toLp 2 (Function.update (fun k => D k) q t))) (D q) =
      fderiv ℝ f D (EuclideanSpace.single q (1 : ℝ)) := by
    convert hDeriv using 1
    apply congrArg (fderiv ℝ f D)
    ext k
    simp
  exact (hDeriv'.trans hDual).symm

/-- Both types of coordinate of the actual whole-dataset Gaussian gradient
are the source quotient coefficients, with the shared literal denominator. -/
theorem gaussianKernel_predictor_ambient_gradient_coordinates
    (h δ : ℝ) (hh : 0 < h) (hδ : 0 < δ) (r : ℕ) (x : ℝ)
    (D : EuclideanSpace ℝ (Fin (r+1) × (Fin 1 ⊕ Fin 1))) :
    let Kh := fun t : ℝ => gaussianPDFReal 0 1 (t/h)/h
    let B := (∑ i : Fin (r+1), Kh (x-D (i,Sum.inl 0)))+(r+1 : ℝ)*δ
    let T := fun E : EuclideanSpace ℝ (Fin (r+1) × (Fin 1 ⊕ Fin 1)) =>
      (∑ i : Fin (r+1), Kh (x-E (i,Sum.inl 0))*E (i,Sum.inr 0)) /
        ((∑ i : Fin (r+1), Kh (x-E (i,Sum.inl 0)))+(r+1 : ℝ)*δ)
    ∀ j : Fin (r+1),
      gradient T D (j,Sum.inl 0) =
        (deriv Kh (x-D (j,Sum.inl 0))/B)*(-D (j,Sum.inr 0)+T D) ∧
      gradient T D (j,Sum.inr 0) = Kh (x-D (j,Sum.inl 0))/B := by
  classical
  intro Kh B T j
  let X := fun i : Fin (r+1) => D (i,Sum.inl (0 : Fin 1))
  let Y := fun i : Fin (r+1) => D (i,Sum.inr (0 : Fin 1))
  have hSmooth : ContDiff ℝ ∞ T := gaussianKernel_predictor_ambient_contDiff h δ hh hδ r x
  have hDiff : DifferentiableAt ℝ T D := hSmooth.differentiable (by norm_num) D
  have hFeature (t : ℝ) (i : Fin (r+1)) :
      Function.update (fun q => D q) (j,Sum.inl (0 : Fin 1)) t (i,Sum.inl 0) = Function.update X j t i := by
    simp [X,Function.update_apply]
  have hResponse (t : ℝ) (i : Fin (r+1)) :
      Function.update (fun q => D q) (j,Sum.inl (0 : Fin 1)) t (i,Sum.inr 0) = Y i := by
    simp [Y]
  have hFeatureFunction :
      (fun t : ℝ => T (WithLp.toLp 2
        (Function.update (fun q => D q) (j,Sum.inl (0 : Fin 1)) t))) =
      (fun t : ℝ =>
        (∑ i : Fin (r+1), Kh (x-Function.update X j t i)*Y i) /
        ((∑ i : Fin (r+1), Kh (x-Function.update X j t i))+(r+1 : ℝ)*δ)) := by
    funext t
    dsimp only [T]
    simp only [hFeature,hResponse]
  constructor
  · rw [gradient_coordinate_eq_updated_section T D (j,Sum.inl 0) hDiff,hFeatureFunction]
    exact (gaussianKernel_feature_coordinate_hasDerivAt h δ hh hδ r X Y x j).deriv
  · have hF (t : ℝ) (i : Fin (r+1)) :
        Function.update (fun q => D q) (j,Sum.inr (0 : Fin 1)) t (i,Sum.inl 0) = X i := by
      simp [X]
    have hY (t : ℝ) (i : Fin (r+1)) :
        Function.update (fun q => D q) (j,Sum.inr (0 : Fin 1)) t (i,Sum.inr 0) = Function.update Y j t i := by
      simp [Y,Function.update_apply]
    have hFunction :
        (fun t : ℝ => T (WithLp.toLp 2
          (Function.update (fun q => D q) (j,Sum.inr (0 : Fin 1)) t))) =
        (fun t : ℝ => (∑ i : Fin (r+1), Kh (x-X i)*Function.update Y j t i)/B) := by
      funext t
      dsimp only [T,B]
      simp only [hF,hY]
      rfl
    let E : Fin (r+1) → LOOConcentration.Observation 1 1 :=
      fun i => ((fun _ : Fin 1 => X i),(fun _ : Fin 1 => Y i))
    have hK : ∀ t : ℝ, 0 ≤ gaussianPDFReal 0 1 t :=
      gaussianKernel_normalization_and_bounds.2.1
    rw [gradient_coordinate_eq_updated_section T D (j,Sum.inr 0) hDiff,hFunction]
    exact (stabilizedKernel_response_coordinate_hasDerivAt
      (gaussianPDFReal 0 1) hK h δ hh hδ r E x j).deriv

end LOOConcentration.Manuscript.Internal
