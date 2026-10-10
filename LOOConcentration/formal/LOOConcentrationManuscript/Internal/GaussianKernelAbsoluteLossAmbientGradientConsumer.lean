import LOOConcentrationManuscript.Internal.GaussianKernelAbsoluteLossAmbientGradient

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open MeasureTheory ProbabilityTheory

/-- The actual paired observation queries satisfy both regularity obligations
of the source Stable field, using the same constant before all sizes and queries. -/
theorem gaussianKernel_actual_observation_loss_gradient_fields
    (h δ : ℝ) (hh : 0 < h) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℕ) (z : LOOConcentration.Observation 1 1),
      let Kh := fun t : ℝ => gaussianPDFReal 0 1 (t/h)/h
      let f := fun E : EuclideanSpace ℝ (Fin (r+1) × (Fin 1 ⊕ Fin 1)) =>
        |(∑ i : Fin (r+1), Kh (z.1 0-E (i,Sum.inl 0))*E (i,Sum.inr 0)) /
          ((∑ i : Fin (r+1), Kh (z.1 0-E (i,Sum.inl 0)))+(r+1 : ℝ)*δ)-z.2 0|
      LocallyLipschitz f ∧
        ∀ᵐ E ∂(volume : Measure (EuclideanSpace ℝ (Fin (r+1) × (Fin 1 ⊕ Fin 1)))),
          DifferentiableAt ℝ f E ∧
          ‖gradient f E‖ ≤ C/Real.sqrt (r+1 : ℝ)+C*‖E‖/(r+1 : ℝ) := by
  obtain ⟨C,hC,hLoss⟩ := gaussianKernel_actual_absoluteLoss_ambient_gradient_bound h δ hh hδ
  refine ⟨C,hC,?_⟩
  intro r z
  exact hLoss r (z.1 0) (z.2 0)

end LOOConcentration.Manuscript.Internal
