import LOOConcentrationManuscript.Internal.KernelDensityFiniteLoss
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open MeasureTheory

/-- The actual literal KDE has a finite cross term against any true probability
density. Its expectation under that density equals the Lebesgue cross integral,
without a square-integrability premise on the true density. -/
theorem genericKDE_density_cross_integral
    (K : ℝ → ℝ) (h : ℝ) (hh : 0 < h)
    (hK_nonneg : ∀ x, 0 ≤ K x) (C : ℝ)
    (hK_bound : ∀ x, |K x| ≤ C) (hK_integral : ∫ x : ℝ, K x = 1)
    (g : ℝ → ℝ) (hg_nonneg : ∀ x, 0 ≤ g x) (hg_integral : ∫ x : ℝ, g x = 1)
    (r : ℕ) (X : Fin (r+1) → ℝ) :
    let f := fun z : ℝ => (r+1 : ℝ)⁻¹ * ∑ j : Fin (r+1), K ((z-X j)/h)/h
    let ν := volume.withDensity (fun z => ENNReal.ofReal (g z))
    IsProbabilityMeasure ν ∧ Integrable (fun z => g z*f z) volume ∧
      Integrable f ν ∧ (∫ z, f z ∂ν) = ∫ z : ℝ, g z*f z := by
  intro f ν
  have hFacts := genericKernelDensityEstimator_facts K h hh hK_nonneg C hK_bound hK_integral r X
  have hfInt : Integrable f volume := hFacts.1
  have hgInt : Integrable g volume := integrable_of_integral_eq_one hg_integral
  have hGMeas : AEMeasurable (fun z => ENNReal.ofReal (g z)) volume :=
    hgInt.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hGFinite : ∀ᵐ z : ℝ ∂volume, ENNReal.ofReal (g z) < ⊤ :=
    Filter.Eventually.of_forall (fun z => ENNReal.ofReal_lt_top)
  have hfBound (z : ℝ) : |f z| ≤ C/h := by
    rw [abs_of_nonneg (hFacts.2.1 z)]
    have hSum : (∑ j : Fin (r+1), K ((z-X j)/h)/h) ≤ (r+1 : ℝ)*(C/h) := by
      calc
        _ ≤ ∑ _j : Fin (r+1), C/h := Finset.sum_le_sum (fun j _ =>
          div_le_div_of_nonneg_right ((le_abs_self _).trans (hK_bound _)) hh.le)
        _ = _ := by simp
    change (r+1 : ℝ)⁻¹ * _ ≤ _
    calc
      _ ≤ (r+1 : ℝ)⁻¹ * ((r+1 : ℝ)*(C/h)) :=
        mul_le_mul_of_nonneg_left hSum (by positivity)
      _ = C/h := by rw [← mul_assoc,inv_mul_cancel₀ (by positivity : (r+1 : ℝ) ≠ 0),one_mul]
  have hCross : Integrable (fun z => g z*f z) volume :=
    hgInt.mul_bdd hfInt.aestronglyMeasurable (Filter.Eventually.of_forall
      (fun z => by simpa only [Real.norm_eq_abs] using hfBound z))
  have hWeighted : Integrable (fun z => (ENNReal.ofReal (g z)).toReal • f z) volume := by
    simpa only [ENNReal.toReal_ofReal (hg_nonneg _),smul_eq_mul] using hCross
  have hDensityInt : Integrable f ν :=
    (integrable_withDensity_iff_integrable_smul₀' hGMeas hGFinite).2 hWeighted
  refine ⟨?_,hCross,hDensityInt,?_⟩
  · constructor
    change volume.withDensity (fun z => ENNReal.ofReal (g z)) Set.univ = 1
    rw [withDensity_apply _ MeasurableSet.univ,setLIntegral_univ,
      ← ofReal_integral_eq_lintegral_ofReal hgInt (Filter.Eventually.of_forall hg_nonneg),
      hg_integral,ENNReal.ofReal_one]
  · rw [integral_withDensity_eq_integral_toReal_smul₀ hGMeas hGFinite]
    simp only [ENNReal.toReal_ofReal (hg_nonneg _),smul_eq_mul]

end LOOConcentration.Manuscript.Internal
