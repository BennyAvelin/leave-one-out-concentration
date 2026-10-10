import LOOConcentrationManuscript.Internal.RidgeExpectedLossQuery
import LOOConcentration.Geometry.LocallyLipschitzDifferentiability
import LOOConcentration.Geometry.NormTransport
import LOOConcentrationRevision.Frozen.Definitions.MeanFittedLoss
import LOOConcentrationRevision.Frozen.Definitions.ObservationOfEuclidean
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

/-!
The actual frozen mean-fitted-loss consumer of stabilized ridge expected-loss
regularity, including the volume-a.e. gradient bound.
-/

namespace LOOConcentrationManuscript.Internal
open MeasureTheory ProbabilityTheory

private abbrev ridgeExpectedLoss :
    LOOConcentration.Responses 1 → LOOConcentration.Responses 1 → ℝ :=
  fun u v => |u 0 - v 0|

/-- The public stabilized ridge estimator supplies true-L1 expected-loss
regularity to the actual frozen `meanFittedLoss` carrier. -/
theorem stabilizedLinearEstimator_actual_meanFittedLoss_regularity
    (μ : Measure (LOOConcentration.Observation 1 1)) [IsProbabilityMeasure μ]
    (hSecond : Integrable LOOConcentration.observationNormSq μ)
    (b δ : {t : ℝ // 0 < t}) :
    ∀ r : ℕ,
      let P := Measure.pi (fun _ : Fin (r + 1) => μ)
      let T : LOOConcentration.Estimator 1 1 (r + 1) :=
        LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r
      let L := ridgeExpectedLoss
      let fields := stabilizedLinearEstimator_expected_absoluteLoss_query_fields
        μ hSecond b δ r
      let hFin := fun z : LOOConcentration.Observation 1 1 => fields.1 z
      let G := fun E : EuclideanSpace ℝ (LOOConcentration.ObservationCoordinate 1 1) =>
        LOOConcentration.Revision.meanFittedLoss μ T L
          (LOOConcentration.Revision.observationOfEuclidean E)
          (hFin (LOOConcentration.Revision.observationOfEuclidean E))
      @Integrable ℝ PseudoMetricSpace.toUniformSpace.toTopologicalSpace
        NormedAddCommGroup.toENormedAddCommMonoid.toContinuousENorm
        (LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) ×
          LOOConcentration.Observation 1 1) _
        (fun p : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) ×
            LOOConcentration.Observation 1 1 =>
          LOOConcentration.fittedLoss T L p.1 p.2) (P.prod μ) ∧
      Integrable
        (fun z : LOOConcentration.Observation 1 1 =>
          LOOConcentration.fittedLoss T L
            (0 : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1)) z) μ ∧
      LipschitzWith
        (Real.toNNReal (Real.sqrt (1 + b.val ^ 2 / (4 * δ.val)))) G ∧
      LocallyLipschitz G ∧
      ∀ᵐ E ∂(volume : Measure (EuclideanSpace ℝ (LOOConcentration.ObservationCoordinate 1 1))),
        DifferentiableAt ℝ G E ∧
          ‖gradient G E‖ ≤ Real.sqrt (1 + b.val ^ 2 / (4 * δ.val)) := by
  intro r P T L fields hFin G
  have hC : 0 < Real.sqrt (1 + b.val ^ 2 / (4 * δ.val)) := by
    have hFrac : 0 ≤ b.val ^ 2 / (4 * δ.val) :=
      div_nonneg (sq_nonneg _) (le_of_lt (mul_pos (by norm_num) δ.property))
    exact Real.sqrt_pos.2 (by linarith)
  have hLip : LipschitzWith
      (Real.toNNReal (Real.sqrt (1 + b.val ^ 2 / (4 * δ.val)))) G := by
    apply LipschitzWith.of_dist_le_mul
    intro E F
    rw [Real.dist_eq, dist_eq_norm,
      Real.coe_toNNReal (Real.sqrt (1 + b.val ^ 2 / (4 * δ.val))) hC.le]
    have hNorm : LOOConcentration.observationNorm
        (LOOConcentration.Revision.observationOfEuclidean E -
          LOOConcentration.Revision.observationOfEuclidean F) = ‖E - F‖ := by
      change LOOConcentration.observationNorm
        (LOOConcentration.observationFromEuclidean E -
          LOOConcentration.observationFromEuclidean F) = _
      rw [LOOConcentration.observationNorm_sub_eq_euclidean,
        LOOConcentration.observationToEuclidean_fromEuclidean,
        LOOConcentration.observationToEuclidean_fromEuclidean]
    have hPair := fields.2.2.2.2
      (LOOConcentration.Revision.observationOfEuclidean E)
      (LOOConcentration.Revision.observationOfEuclidean F)
    rw [← hNorm]
    change |G E - G F| ≤
      Real.sqrt (1 + b.val ^ 2 / (4 * δ.val)) *
        LOOConcentration.observationNorm
          (LOOConcentration.Revision.observationOfEuclidean E -
            LOOConcentration.Revision.observationOfEuclidean F)
    simpa only [G, LOOConcentration.Revision.meanFittedLoss] using hPair
  refine ⟨fields.2.1, fields.2.2.2.1, hLip, hLip.locallyLipschitz, ?_⟩
  have hAE := LOOConcentration.locallyLipschitz_ae_differentiableAt_euclidean G
    hLip.locallyLipschitz
  filter_upwards [hAE] with E hDiff
  refine ⟨hDiff, ?_⟩
  have hGradNorm : ‖gradient G E‖ = ‖fderiv ℝ G E‖ := by
    change ‖(InnerProductSpace.toDual ℝ _).symm (fderiv ℝ G E)‖ = _
    exact (InnerProductSpace.toDual ℝ _).symm.norm_map _
  rw [hGradNorm]
  exact (norm_fderiv_le_of_lipschitz ℝ hLip).trans_eq
    (Real.coe_toNNReal (Real.sqrt (1 + b.val ^ 2 / (4 * δ.val))) hC.le)

end LOOConcentrationManuscript.Internal
