import LOOConcentrationManuscript.Internal.GaussianKernelExpectedLossQueryConsumer
import LOOConcentration.Geometry.LocallyLipschitzDifferentiability
import LOOConcentrationRevision.Frozen.Definitions.ObservationOfEuclidean
import Mathlib.Analysis.Calculus.Gradient.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open MeasureTheory ProbabilityTheory

/-- The actual expected Gaussian absolute fitted loss has one ambient query
Lipschitz and gradient bound, uniform in the training-sample size. -/
theorem gaussianKernel_actual_expectedLoss_ambient_gradient_fields
    (μ : Measure (LOOConcentration.Observation 1 1)) [IsProbabilityMeasure μ]
    (hSecond : Integrable LOOConcentration.observationNormSq μ)
    (h δ : ℝ) (hh : 0 < h) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ,
      let P := Measure.pi (fun _ : Fin (r+1) => μ)
      let Kh := fun t : ℝ => gaussianPDFReal 0 1 (t/h)/h
      let L := fun (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+1))
          (z : LOOConcentration.Observation 1 1) =>
        |(∑ i : Fin (r+1), Kh (z.1 0-(D i).1 0)*(D i).2 0)/
          ((∑ i : Fin (r+1), Kh (z.1 0-(D i).1 0))+(r+1 : ℝ)*δ)-z.2 0|
      let G := fun E : EuclideanSpace ℝ (LOOConcentration.ObservationCoordinate 1 1) =>
        ∫ D, L D (LOOConcentration.Revision.observationOfEuclidean E) ∂P
      (∀ z, Integrable (fun D => L D z) P) ∧
      LipschitzWith (Real.toNNReal C) G ∧ LocallyLipschitz G ∧
      ∀ᵐ E ∂(volume : Measure (EuclideanSpace ℝ (LOOConcentration.ObservationCoordinate 1 1))),
        DifferentiableAt ℝ G E ∧ ‖gradient G E‖ ≤ C := by
  obtain ⟨C,hC,hFields⟩ := gaussianKernel_expected_absoluteLoss_shared_query_constant μ hSecond h δ hh hδ
  refine ⟨C,hC,?_⟩
  intro r P Kh L G
  have hField := hFields r
  have hLip : LipschitzWith (Real.toNNReal C) G := by
    apply LipschitzWith.of_dist_le_mul
    intro E F
    rw [Real.dist_eq,dist_eq_norm,Real.coe_toNNReal C hC.le]
    have hNorm : LOOConcentration.observationNorm
        (LOOConcentration.Revision.observationOfEuclidean E-
          LOOConcentration.Revision.observationOfEuclidean F) = ‖E-F‖ := by
      change LOOConcentration.observationNorm
        (LOOConcentration.observationFromEuclidean E-LOOConcentration.observationFromEuclidean F) = _
      rw [LOOConcentration.observationNorm_sub_eq_euclidean,
        LOOConcentration.observationToEuclidean_fromEuclidean,
        LOOConcentration.observationToEuclidean_fromEuclidean]
    have hPoint := hField.2
      (LOOConcentration.Revision.observationOfEuclidean E)
      (LOOConcentration.Revision.observationOfEuclidean F)
    change |G E-G F| ≤ C*LOOConcentration.observationNorm
      (LOOConcentration.Revision.observationOfEuclidean E-
        LOOConcentration.Revision.observationOfEuclidean F) at hPoint
    rw [hNorm] at hPoint
    exact hPoint
  refine ⟨hField.1,hLip,hLip.locallyLipschitz,?_⟩
  have hAE := LOOConcentration.locallyLipschitz_ae_differentiableAt_euclidean G hLip.locallyLipschitz
  filter_upwards [hAE] with E hDiff
  refine ⟨hDiff,?_⟩
  have hNorm : ‖gradient G E‖ = ‖fderiv ℝ G E‖ := by
    change ‖(InnerProductSpace.toDual ℝ _).symm (fderiv ℝ G E)‖ = _
    exact (InnerProductSpace.toDual ℝ _).symm.norm_map _
  rw [hNorm]
  exact (norm_fderiv_le_of_lipschitz ℝ hLip).trans_eq (Real.coe_toNNReal C hC.le)

end LOOConcentration.Manuscript.Internal
