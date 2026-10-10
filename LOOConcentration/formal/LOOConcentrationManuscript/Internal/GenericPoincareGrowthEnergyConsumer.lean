import LOOConcentrationManuscript.Internal.GenericPoincareGrowthEnergy

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

/-- The actual cap's variance is bounded by the base native constant times
`b²N`, using the same internally produced native pair and energy. The
unbounded source variance and its limiting rates remain a separate obligation. -/
theorem generic_product_source_growth_cap_variance
    (μ : Measure (EuclideanSpace ℝ (Fin 1))) [IsProbabilityMeasure μ]
    (hM2 : Integrable (fun x => ‖x‖ ^ 2) μ)
    (hUnit : (∫ x, ‖x‖ ^ 2 ∂μ) = 1)
    (hFinite : LOOConcentration.Revision.logSobolevConstant μ < ⊤) (r : ℕ)
    (F : EuclideanSpace ℝ (Fin (r + 1) × Fin 1) → ℝ)
    (hLoc : LocallyLipschitz F) (b R : NNReal)
    (hGrad : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin (r + 1) × Fin 1))),
      DifferentiableAt ℝ F x ∧ ‖gradient F x‖ ≤ (b : ℝ) * ‖x‖) :
    let ν := LOOConcentration.Revision.euclideanProductLaw (κ := Fin (r + 1)) μ
    let cap := fun x => max (-(R : ℝ)) (min (F x) (R : ℝ))
    Integrable (fun x => (cap x - ∫ y, cap y ∂ν) ^ 2) ν ∧
      (∫ x, (cap x - ∫ y, cap y ∂ν) ^ 2 ∂ν) ≤
        (LOOConcentration.Revision.logSobolevConstant μ).toReal *
          ((b : ℝ) ^ 2 * ((r + 1 : ℕ) : ℝ)) := by
  intro ν cap
  let : IsProbabilityMeasure ν :=
    LOOConcentration.Revision.euclideanProductLaw_isProbabilityMeasure μ
  obtain ⟨u, hScalar, hEnergy⟩ :=
    generic_product_source_growth_cap_energy μ hM2 hUnit r F hLoc b R hGrad
  have hCap2 : MemLp cap 2 ν := (memLp_congr_ae hScalar).mp (Lp.memLp ((WithLp.ofLp u.val).1))
  have hCentered : MemLp (fun x => cap x - ∫ y, cap y ∂ν) 2 ν :=
    hCap2.sub (memLp_const _)
  have hMean : (∫ y, (WithLp.ofLp u.val).1 y ∂ν) = ∫ y, cap y ∂ν :=
    integral_congr_ae hScalar
  have hVar : (∫ x, ((WithLp.ofLp u.val).1 x -
        ∫ y, (WithLp.ofLp u.val).1 y ∂ν) ^ 2 ∂ν) =
      ∫ x, (cap x - ∫ y, cap y ∂ν) ^ 2 ∂ν := by
    apply integral_congr_ae
    filter_upwards [hScalar] with x hx
    rw [hx, hMean]
  have hPoincare :=
    LOOConcentration.Revision.all_pairs_poincare_euclideanProductLaw r μ hFinite u
  change _ ≤ (LOOConcentration.Revision.logSobolevConstant μ).toReal *
    (LOOConcentration.Revision.sobolevEnergy ν u).toReal at hPoincare
  rw [hVar] at hPoincare
  exact ⟨(memLp_two_iff_integrable_sq hCentered.aestronglyMeasurable).mp hCentered,
    hPoincare.trans (mul_le_mul_of_nonneg_left hEnergy ENNReal.toReal_nonneg)⟩

end LOOConcentration.Manuscript.Internal
