import LOOConcentrationManuscript.Internal.IsometryLSITransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal

open MeasureTheory
open scoped ENNReal

noncomputable def coordinatePaddingFinOneFinTwo :
    EuclideanSpace ℝ (Fin 1) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toLinearMap :=
    { toFun := fun x => EuclideanSpace.single 0 (x 0)
      map_add' := by
        intro x y
        ext i
        fin_cases i <;> simp [EuclideanSpace.single]
      map_smul' := by
        intro a x
        ext i
        fin_cases i <;> simp [EuclideanSpace.single] }
  norm_map' := by
    intro x
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    simp [EuclideanSpace.single]

theorem coordinatePaddingFinOneFinTwo_logSobolevConstant_le
    (μ : Measure (EuclideanSpace ℝ (Fin 1))) [IsProbabilityMeasure μ] :
    letI : IsProbabilityMeasure (μ.map coordinatePaddingFinOneFinTwo) :=
      μ.isProbabilityMeasure_map coordinatePaddingFinOneFinTwo.continuous.measurable.aemeasurable
    LOOConcentration.Revision.logSobolevConstant (μ.map coordinatePaddingFinOneFinTwo) ≤
      LOOConcentration.Revision.logSobolevConstant μ := by
  exact logSobolevConstant_map_linearIsometry_le μ coordinatePaddingFinOneFinTwo

theorem identityFinOne_logSobolevConstant_map_le
    (μ : Measure (EuclideanSpace ℝ (Fin 1))) [IsProbabilityMeasure μ] :
    letI : IsProbabilityMeasure
        (μ.map (LinearIsometry.id : EuclideanSpace ℝ (Fin 1) →ₗᵢ[ℝ]
          EuclideanSpace ℝ (Fin 1))) :=
      μ.isProbabilityMeasure_map
        (LinearIsometry.id : EuclideanSpace ℝ (Fin 1) →ₗᵢ[ℝ]
          EuclideanSpace ℝ (Fin 1)).continuous.measurable.aemeasurable
    LOOConcentration.Revision.logSobolevConstant
        (μ.map (LinearIsometry.id : EuclideanSpace ℝ (Fin 1) →ₗᵢ[ℝ]
          EuclideanSpace ℝ (Fin 1))) ≤
      LOOConcentration.Revision.logSobolevConstant μ := by
  have h := logSobolevConstant_map_linearIsometry_le μ
    (LinearIsometry.id : EuclideanSpace ℝ (Fin 1) →ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin 1))
  exact h

end LOOConcentration.Manuscript.Internal
