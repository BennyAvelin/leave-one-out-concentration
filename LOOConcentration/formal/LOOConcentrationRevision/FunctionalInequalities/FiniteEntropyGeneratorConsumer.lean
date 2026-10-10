import LOOConcentrationRevision.FunctionalInequalities.NonnegativeFiniteEntropyTensorization
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

set_option autoImplicit false

open MeasureTheory

namespace LOOConcentration.Revision

/-- The actual square-plus-epsilon generator consumes the full nonnegative
finite-entropy theorem. Its two integrability conditions are produced from the
same scalar bound, including epsilon zero. -/
theorem entropy_square_add_epsilon_piFin_subadditive_of_finite_entropy
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (F : (Fin (r + 1) → EuclideanSpace ℝ ι) → ℝ)
    (hF : Measurable F) (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hF_bound : ∀ D, ‖F D‖ ≤ B) :
    LOOConcentration.entropy (Measure.pi fun _ : Fin (r + 1) => μ)
        (fun D => (F D) ^ 2 + ε) ≤
      ∑ i : Fin (r + 1),
        ∫ tail : Fin r → EuclideanSpace ℝ ι,
          LOOConcentration.entropy μ (fun z =>
            (F ((MeasurableEquiv.piFinSuccAbove
              (fun _ : Fin (r + 1) => EuclideanSpace ℝ ι) i).symm
                (z, tail))) ^ 2 + ε) ∂Measure.pi fun _ : Fin r => μ := by
  let g : (Fin (r + 1) → EuclideanSpace ℝ ι) → ℝ := fun D => (F D)^2 + ε
  have hg : Measurable g := (hF.pow_const 2).add_const ε
  have hnonneg (D : Fin (r + 1) → EuclideanSpace ℝ ι) : 0 ≤ g D :=
    add_nonneg (sq_nonneg _) hε
  have hbound (D : Fin (r + 1) → EuclideanSpace ℝ ι) : g D ≤ B^2 + ε := by
    have habs : |F D| ≤ B := by simpa only [Real.norm_eq_abs] using hF_bound D
    have hs : (F D)^2 ≤ B^2 := by
      rw [sq_le_sq, abs_of_nonneg hB]
      exact habs
    exact add_le_add hs le_rfl
  have hgInt : Integrable g (Measure.pi fun _ : Fin (r + 1) => μ) := by
    apply Integrable.of_bound hg.aestronglyMeasurable (B^2 + ε)
    exact Filter.Eventually.of_forall fun D => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg D)]
      exact hbound D
  have hcompact := isCompact_Icc.bddAbove_image
    (Real.continuous_mul_log.norm.continuousOn :
      ContinuousOn (fun x : ℝ => ‖x * Real.log x‖) (Set.Icc 0 (B^2 + ε)))
  obtain ⟨A, hA⟩ := hcompact
  have hphiInt : Integrable (fun D => g D * Real.log (g D))
      (Measure.pi fun _ : Fin (r + 1) => μ) := by
    apply Integrable.of_bound
      (Real.continuous_mul_log.measurable.comp hg).aestronglyMeasurable A
    exact Filter.Eventually.of_forall fun D =>
      hA ⟨g D, ⟨hnonneg D, hbound D⟩, rfl⟩
  exact entropy_piFin_succ_subadditive_nonnegative_finite_entropy μ g hg
    hnonneg hgInt hphiInt

#print axioms entropy_square_add_epsilon_piFin_subadditive_of_finite_entropy

end LOOConcentration.Revision
