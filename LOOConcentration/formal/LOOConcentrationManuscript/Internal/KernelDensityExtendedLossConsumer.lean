import LOOConcentrationManuscript.Internal.KernelDensityExtendedLoss

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open MeasureTheory

/-- The actual extended loss has the finite quadratic expansion on the approved
L² comparison domain and is infinite outside that domain. -/
theorem genericKDE_extended_squaredLoss_dichotomy
    (K : ℝ → ℝ) (h : ℝ) (hh : 0 < h)
    (hK_nonneg : ∀ x, 0 ≤ K x) (C : ℝ)
    (hK_bound : ∀ x, |K x| ≤ C) (hK_integral : ∫ x : ℝ, K x = 1)
    (g : ℝ → ℝ) (hg_nonneg : ∀ x, 0 ≤ g x) (hg_integral : ∫ x : ℝ, g x = 1)
    (r : ℕ) (X : Fin (r+1) → ℝ) :
    let f := fun z : ℝ => (r+1 : ℝ)⁻¹ * ∑ j : Fin (r+1), K ((z-X j)/h)/h
    let L := ∫⁻ z : ℝ, ENNReal.ofReal ((g z-f z)^2)
    (MemLp g 2 volume →
      L = ENNReal.ofReal ((∫ z : ℝ, (g z)^2)-2*(∫ z : ℝ, g z*f z)+(∫ z : ℝ, (f z)^2)) ∧
      0 ≤ (∫ z : ℝ, (g z)^2)-2*(∫ z : ℝ, g z*f z)+(∫ z : ℝ, (f z)^2)) ∧
    (¬ MemLp g 2 volume → L = ⊤) := by
  intro f L
  have hFinite := genericKDE_extended_squaredLoss_finite_iff K h hh hK_nonneg C hK_bound
    hK_integral g hg_nonneg hg_integral r X
  constructor
  · intro hgLp
    have hLoss := genericKernelDensityEstimator_finite_integrated_loss_expansion
      K h hh hK_nonneg C hK_bound hK_integral r X g hgLp
    have hNonneg : 0 ≤ ∫ z : ℝ, (g z-f z)^2 := integral_nonneg (fun z => sq_nonneg _)
    have hReal : L = ENNReal.ofReal (∫ z : ℝ, (g z-f z)^2) :=
      (ofReal_integral_eq_lintegral_ofReal hLoss.1
        (Filter.Eventually.of_forall (fun z => sq_nonneg (g z-f z)))).symm
    rw [hLoss.2] at hReal hNonneg
    exact ⟨hReal,hNonneg⟩
  · intro hgNotLp
    by_contra hNotTop
    exact hgNotLp (hFinite.mp (lt_top_iff_ne_top.mpr hNotTop))

end LOOConcentration.Manuscript.Internal
