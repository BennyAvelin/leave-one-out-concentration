import LOOConcentrationManuscript.Internal.KernelDensityFiniteLoss

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open MeasureTheory

/-- The literal extended KDE squared loss is finite exactly when the true
probability density belongs to L². No L² premise restricts the public carrier. -/
theorem genericKDE_extended_squaredLoss_finite_iff
    (K : ℝ → ℝ) (h : ℝ) (hh : 0 < h)
    (hK_nonneg : ∀ x, 0 ≤ K x) (C : ℝ)
    (hK_bound : ∀ x, |K x| ≤ C) (hK_integral : ∫ x : ℝ, K x = 1)
    (g : ℝ → ℝ) (_hg_nonneg : ∀ x, 0 ≤ g x) (hg_integral : ∫ x : ℝ, g x = 1)
    (r : ℕ) (X : Fin (r+1) → ℝ) :
    let f := fun z : ℝ => (r+1 : ℝ)⁻¹ * ∑ j : Fin (r+1), K ((z-X j)/h)/h
    (∫⁻ z : ℝ, ENNReal.ofReal ((g z-f z)^2)) < ⊤ ↔ MemLp g 2 volume := by
  intro f
  have hFacts := genericKernelDensityEstimator_facts K h hh hK_nonneg C hK_bound hK_integral r X
  have hfLp : MemLp f 2 volume := hFacts.2.2.2
  have hgInt : Integrable g volume := integrable_of_integral_eq_one hg_integral
  have hDiff : AEStronglyMeasurable (fun z => g z-f z) volume :=
    hgInt.aestronglyMeasurable.sub hFacts.1.aestronglyMeasurable
  have hSq : AEStronglyMeasurable (fun z => (g z-f z)^2) volume := hDiff.pow 2
  rw [lt_top_iff_ne_top,lintegral_ofReal_ne_top_iff_integrable hSq
    (Filter.Eventually.of_forall (fun z => sq_nonneg (g z-f z))),
    ← memLp_two_iff_integrable_sq hDiff]
  constructor
  · intro hLp
    have hSum := hLp.add hfLp
    have hFun : (fun z => g z-f z) + f = g := by
      funext z
      exact sub_add_cancel (g z) (f z)
    rw [hFun] at hSum
    exact hSum
  · intro hgLp
    exact hgLp.sub hfLp

end LOOConcentration.Manuscript.Internal
