import LOOConcentrationManuscript.Internal.GaussianKernelSharedGradientConstantConsumer
import LOOConcentrationManuscript.Internal.GaussianKernelAmbientRegularity
import LOOConcentration.Geometry.LocallyLipschitzDifferentiability
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Abs

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

/-- The source absolute fitted loss is locally Lipschitz on the full ambient
Euclidean training carrier and has the stated gradient bound almost everywhere.
The zero-residual branch uses a genuine local minimum, not a smoothness claim. -/
theorem gaussianKernel_actual_absoluteLoss_ambient_gradient_bound
    (h δ : ℝ) (hh : 0 < h) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℕ) (x y : ℝ),
      let Kh := fun t : ℝ => gaussianPDFReal 0 1 (t/h)/h
      let T := fun E : EuclideanSpace ℝ (Fin (r+1) × (Fin 1 ⊕ Fin 1)) =>
        (∑ i : Fin (r+1), Kh (x-E (i,Sum.inl 0))*E (i,Sum.inr 0)) /
          ((∑ i : Fin (r+1), Kh (x-E (i,Sum.inl 0)))+(r+1 : ℝ)*δ)
      let f := fun E => |T E-y|
      LocallyLipschitz f ∧
        ∀ᵐ E ∂(volume : Measure (EuclideanSpace ℝ (Fin (r+1) × (Fin 1 ⊕ Fin 1)))),
          DifferentiableAt ℝ f E ∧
          ‖gradient f E‖ ≤ C/Real.sqrt (r+1 : ℝ)+C*‖E‖/(r+1 : ℝ) := by
  obtain ⟨C,hC,hGradient⟩ := gaussianKernel_source_shared_gradient_constant h δ hh hδ
  refine ⟨C,hC,?_⟩
  intro r x y Kh T f
  have hSmooth : ContDiff ℝ 1 T :=
    (gaussianKernel_predictor_ambient_contDiff h δ hh hδ r x).of_le (by simp)
  have hSub : ContDiff ℝ 1 (fun E => T E-y) := hSmooth.sub contDiff_const
  have hLocal : LocallyLipschitz f := by
    simpa only [Function.comp_def,Real.norm_eq_abs] using
      (lipschitzWith_one_norm.locallyLipschitz.comp hSub.locallyLipschitz)
  refine ⟨hLocal,?_⟩
  have hAE := LOOConcentration.locallyLipschitz_ae_differentiableAt_euclidean f hLocal
  filter_upwards [hAE] with E hDiff
  refine ⟨hDiff,?_⟩
  have hTDeriv : HasFDerivAt T (fderiv ℝ T E) E :=
    (hSmooth.differentiable (by norm_num) E).hasFDerivAt
  have hSubDeriv : HasFDerivAt (fun D => T D-y) (fderiv ℝ T E) E := hTDeriv.sub_const y
  rcases lt_trichotomy (T E-y) 0 with hNeg | hZero | hPos
  · have hAbs := hSubDeriv.abs_of_neg hNeg
    have hNorm : ‖gradient f E‖ = ‖gradient T E‖ := by
      rw [gradient,hAbs.fderiv,map_neg,norm_neg]
      rfl
    rw [hNorm]
    exact hGradient r x E
  · have hMin : IsLocalMin f E := by
      change ∀ᶠ D in 𝓝 E, f E ≤ f D
      apply Filter.Eventually.of_forall
      intro D
      have hValue : f E = 0 := by change |T E-y| = 0; rw [hZero,abs_zero]
      rw [hValue]
      exact abs_nonneg _
    rw [gradient,hMin.fderiv_eq_zero,map_zero,norm_zero]
    positivity
  · have hAbs := hSubDeriv.abs_of_pos hPos
    have hNorm : ‖gradient f E‖ = ‖gradient T E‖ := by
      rw [gradient,hAbs.fderiv]
      rfl
    rw [hNorm]
    exact hGradient r x E

end LOOConcentration.Manuscript.Internal
