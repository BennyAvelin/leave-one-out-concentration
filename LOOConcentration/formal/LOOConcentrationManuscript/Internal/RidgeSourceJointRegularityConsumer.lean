import LOOConcentrationManuscript.Internal.RidgeSourceJointRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal

/-- The source's stability growth rates apply to the actual absolute fitted
loss at every training dataset, with the constant chosen before all sizes
and queries and inherited from the joint source regularity producer. -/
theorem ridge_actual_absoluteLoss_source_localSlope_rates
    (b δ : {t : ℝ // 0 < t}) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℕ) (z : LOOConcentration.Observation 1 1),
      ∃ f : LOOConcentration.LocallyLipschitzDataFunction 0 0 r,
        (∀ D, f.1 D = LOOConcentration.fittedLoss
          (LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r)
          (fun u v : Fin 1 → ℝ => |u 0 - v 0|) D z) ∧
        (∀ D, LOOConcentration.datasetLocalSlope f D ≤
          C * (1 + |z.1 0|) / Real.sqrt ((r + 1 : ℕ) : ℝ) +
            C / ((r + 1 : ℕ) : ℝ) * LOOConcentration.datasetNorm D) := by
  obtain ⟨C, hC, hSource⟩ := stabilizedLinearEstimator_actual_source_joint_regularity b δ
  refine ⟨C, hC, ?_⟩
  intro r z
  obtain ⟨_B, _P, L, _hB, _hP, hL, hSlope⟩ := (hSource r z).2.2.2.2.1
  refine ⟨L, hL, ?_⟩
  intro D
  simpa only [div_mul_eq_mul_div] using (hSlope D).2.2

end LOOConcentration.Manuscript.Internal
