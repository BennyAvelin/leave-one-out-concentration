import LOOConcentrationRevision.FunctionalInequalities.TruncationAdmission
import LOOConcentrationRevision.FunctionalInequalities.IntrinsicPoincareClosure
import LOOConcentrationRevision.FunctionalInequalities.SobolevEnergyNorm
import LOOConcentrationRevision.Probability.ProductNormCapExpectations
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal
open MeasureTheory Filter
open scoped Topology ENNReal

/-- Internally build the actual bounded cap of a source function and retain its
native gradient energy, without transferring volume-a.e. differentiability to
an arbitrary possibly singular product law. This is a cap ingredient, not a
claim about the unbounded function's variance. -/
theorem generic_product_source_growth_cap_energy
    (μ : Measure (EuclideanSpace ℝ (Fin 1))) [IsProbabilityMeasure μ]
    (hM2 : Integrable (fun x => ‖x‖ ^ 2) μ)
    (hUnit : (∫ x, ‖x‖ ^ 2 ∂μ) = 1) (r : ℕ)
    (F : EuclideanSpace ℝ (Fin (r + 1) × Fin 1) → ℝ)
    (hLoc : LocallyLipschitz F) (b R : NNReal)
    (hGrad : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin (r + 1) × Fin 1))),
      DifferentiableAt ℝ F x ∧ ‖gradient F x‖ ≤ (b : ℝ) * ‖x‖) :
    let ν := LOOConcentration.Revision.euclideanProductLaw (κ := Fin (r + 1)) μ
    let : IsProbabilityMeasure ν :=
      LOOConcentration.Revision.euclideanProductLaw_isProbabilityMeasure μ
    ∃ u : LOOConcentration.Revision.SobolevPair ν,
      ((WithLp.ofLp u.val).1 : EuclideanSpace ℝ (Fin (r + 1) × Fin 1) → ℝ) =ᵐ[ν]
        (fun x => max (-(R : ℝ)) (min (F x) (R : ℝ))) ∧
      (LOOConcentration.Revision.sobolevEnergy ν u).toReal ≤
        (b : ℝ) ^ 2 * ((r + 1 : ℕ) : ℝ) := by
  intro ν
  let : IsProbabilityMeasure ν :=
    LOOConcentration.Revision.euclideanProductLaw_isProbabilityMeasure μ
  have hνM2 : Integrable
      (fun x : EuclideanSpace ℝ (Fin (r + 1) × Fin 1) => ‖x‖ ^ 2) ν :=
    LOOConcentration.Revision.integrable_euclideanProductLaw_norm_sq μ hM2
  have hνUnit : (∫ x : EuclideanSpace ℝ (Fin (r + 1) × Fin 1), ‖x‖ ^ 2 ∂ν) =
      ((r + 1 : ℕ) : ℝ) := by
    rw [LOOConcentration.Revision.integral_euclideanProductLaw_norm_sq μ hM2, hUnit]
    simp
  have hGrad' : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin (r + 1) × Fin 1))),
      DifferentiableAt ℝ F x ∧ ‖gradient F x‖ ≤ (0 : NNReal) + (b : ℝ) * ‖x‖ := by
    simpa only [NNReal.coe_zero, zero_add] using hGrad
  obtain ⟨u, hScalar, hNative⟩ :=
    LOOConcentration.Revision.bounded_truncation_admission_of_ae_gradient
      ν hνM2 F hLoc 0 b R hGrad'
  let G : Lp (EuclideanSpace ℝ (Fin (r + 1) × Fin 1)) 2 ν := (WithLp.ofLp u.val).2
  have hG2 : Integrable (fun x => ‖G x‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp G).aestronglyMeasurable).mp (Lp.memLp G)
  have hSq : ∀ᵐ x ∂ν, ‖G x‖ ^ 2 ≤ (b : ℝ) ^ 2 * ‖x‖ ^ 2 := by
    filter_upwards [hNative] with x hx
    have hBound : ‖G x‖ ≤ (b : ℝ) * ‖x‖ := by
      simpa only [NNReal.coe_zero, zero_add] using hx
    calc
      ‖G x‖ ^ 2 ≤ ((b : ℝ) * ‖x‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hBound 2
      _ = _ := mul_pow _ _ _
  have hEnergy : (LOOConcentration.Revision.sobolevEnergy ν u).toReal =
      ∫ x, ‖G x‖ ^ 2 ∂ν := by
    rw [LOOConcentration.Revision.sobolevEnergy_eq_ofReal_norm_sq,
      ENNReal.toReal_ofReal (sq_nonneg _)]
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq, G]
  refine ⟨u, hScalar, ?_⟩
  rw [hEnergy]
  calc
    _ ≤ ∫ x, (b : ℝ) ^ 2 * ‖x‖ ^ 2 ∂ν :=
      integral_mono_ae hG2 (hνM2.const_mul _) hSq
    _ = (b : ℝ) ^ 2 * ((r + 1 : ℕ) : ℝ) := by
      rw [integral_const_mul, hνUnit]

end LOOConcentration.Manuscript.Internal
