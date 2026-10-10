import LOOConcentrationManuscript.Frozen.Results.EmpiricalMeanAbsoluteLossLipschitz
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Order.Filter.ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LOOConcentration.Manuscript.Internal

open Filter
open scoped Topology ENNReal

theorem lipschitz_euclidean_slope_and_gradient_le
    (r : ℕ) (f : EuclideanSpace ℝ (Fin (r + 1)) → ℝ)
    (K : NNReal) (hLip : LipschitzWith K f)
    (D : EuclideanSpace ℝ (Fin (r + 1))) :
    (limsup (fun E : EuclideanSpace ℝ (Fin (r + 1)) =>
      |f E - f D| / ‖E - D‖) (𝓝[≠] D) ≤ (K : ℝ)) ∧
    ‖gradient f D‖ ≤ (K : ℝ) := by
  let quotient : EuclideanSpace ℝ (Fin (r + 1)) → ℝ := fun E =>
    |f E - f D| / ‖E - D‖
  have hquotient_le : ∀ E, quotient E ≤ (K : ℝ) := by
    intro E
    by_cases hED : E = D
    · simp [quotient, hED]
    · have hdist : |f E - f D| ≤ (K : ℝ) * ‖E - D‖ := by
        have h := hLip.norm_sub_le E D
        simpa only [Real.norm_eq_abs] using h
      have hnorm : 0 < ‖E - D‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hED)
      dsimp [quotient]
      exact (div_le_iff₀ hnorm).2 hdist
  have hquotient_nonneg : ∀ E, 0 ≤ quotient E := by
    intro E
    exact div_nonneg (abs_nonneg _) (norm_nonneg _)
  have hfilter_bounded : (𝓝[≠] D).IsBoundedUnder (· ≤ ·) quotient := by
    refine ⟨(K : ℝ), ?_⟩
    change ∀ᶠ E in 𝓝[≠] D, quotient E ≤ (K : ℝ)
    exact Filter.Eventually.of_forall hquotient_le
  have hneBot : NeBot (𝓝[≠] D) := by infer_instance
  have hfilter_cobounded : (𝓝[≠] D).IsCoboundedUnder (· ≤ ·) quotient := by
    change (Filter.map quotient (𝓝[≠] D)).IsCobounded (· ≤ ·)
    refine ⟨0, ?_⟩
    intro a ha
    have hqa : ∀ᶠ E in 𝓝[≠] D, quotient E ≤ a := by
      simpa only [Filter.eventually_map] using ha
    have hzero : ∀ᶠ E in 𝓝[≠] D, (0 : ℝ) ≤ quotient E :=
      Filter.Eventually.of_forall hquotient_nonneg
    have hconstant : ∀ᶠ E in 𝓝[≠] D, (0 : ℝ) ≤ a :=
      (hzero.and hqa).mono fun _ ⟨hzeroE, hqaE⟩ => hzeroE.trans hqaE
    obtain ⟨E, hE⟩ := @Filter.Eventually.exists _ _ _ hneBot hconstant
    exact hE
  have hlimsup' : limsup quotient (𝓝[≠] D) ≤ (K : ℝ) := by
    apply (Filter.limsup_le_iff hfilter_cobounded hfilter_bounded).2
    intro a ha
    exact (Filter.Eventually.of_forall hquotient_le).mono fun _ hE => hE.trans_lt ha
  have hlimsup : (limsup (fun E : EuclideanSpace ℝ (Fin (r + 1)) =>
      |f E - f D| / ‖E - D‖) (𝓝[≠] D)) ≤ (K : ℝ) := by
    simpa only [quotient] using hlimsup'
  have hgradient : ‖gradient f D‖ ≤ (K : ℝ) := by
    by_cases hdiff : DifferentiableAt ℝ f D
    · have hfderiv : HasFDerivAt f (fderiv ℝ f D) D := hdiff.hasFDerivAt
      have hderivBound : ‖fderiv ℝ f D‖ ≤ (K : ℝ) := by
        exact_mod_cast hfderiv.le_of_lipschitz hLip
      calc
        ‖gradient f D‖ = ‖(InnerProductSpace.toDual ℝ
            (EuclideanSpace ℝ (Fin (r + 1)))).symm (fderiv ℝ f D)‖ := rfl
        _ = ‖fderiv ℝ f D‖ :=
          (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin (r + 1)))).symm.norm_map _
        _ ≤ (K : ℝ) := hderivBound
    · rw [gradient_eq_zero_of_not_differentiableAt hdiff]
      simp
  exact ⟨hlimsup, hgradient⟩

end LOOConcentration.Manuscript.Internal
