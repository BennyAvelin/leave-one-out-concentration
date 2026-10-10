import LOOConcentrationManuscript.Internal.KernelDensityCrossIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open MeasureTheory

/-- On the approved finite-loss comparison domain, the cross term is exactly
expectation of the literal fitted KDE under the true density law. -/
theorem genericKDE_finite_loss_density_expectation_expansion
    (K : ℝ → ℝ) (h : ℝ) (hh : 0 < h)
    (hK_nonneg : ∀ x, 0 ≤ K x) (C : ℝ)
    (hK_bound : ∀ x, |K x| ≤ C) (hK_integral : ∫ x : ℝ, K x = 1)
    (g : ℝ → ℝ) (hg_nonneg : ∀ x, 0 ≤ g x) (hg_integral : ∫ x : ℝ, g x = 1)
    (hg : MemLp g 2 volume) (r : ℕ) (X : Fin (r+1) → ℝ) :
    let f := fun z : ℝ => (r+1 : ℝ)⁻¹ * ∑ j : Fin (r+1), K ((z-X j)/h)/h
    let ν := volume.withDensity (fun z => ENNReal.ofReal (g z))
    IsProbabilityMeasure ν ∧ Integrable f ν ∧
      Integrable (fun z => (g z-f z)^2) volume ∧
      (∫ z : ℝ, (g z-f z)^2) =
        (∫ z : ℝ, (g z)^2)-2*(∫ z, f z ∂ν)+(∫ z : ℝ, (f z)^2) := by
  intro f ν
  have hCross := genericKDE_density_cross_integral K h hh hK_nonneg C hK_bound hK_integral
    g hg_nonneg hg_integral r X
  have hLoss := genericKernelDensityEstimator_finite_integrated_loss_expansion
    K h hh hK_nonneg C hK_bound hK_integral r X g hg
  refine ⟨hCross.1,hCross.2.2.1,hLoss.1,?_⟩
  rw [hCross.2.2.2]
  exact hLoss.2

end LOOConcentration.Manuscript.Internal
