import LOOConcentrationManuscript.Internal.GaussianKernelExpectedLossAmbientGradient
import LOOConcentrationRevision.Frozen.Definitions.MeanFittedLoss

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open MeasureTheory ProbabilityTheory

/-- Actual finite-loss witnesses and the frozen mean-loss carrier inherit the
same uniform expected-loss gradient constant. -/
theorem gaussianKernel_actual_frozen_meanLoss_regularity_fields
    (μ : Measure (LOOConcentration.Observation 1 1)) [IsProbabilityMeasure μ]
    (hSecond : Integrable LOOConcentration.observationNormSq μ)
    (h δ : ℝ) (hh : 0 < h) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ,
      let Kh := fun t : ℝ => gaussianPDFReal 0 1 (t/h)/h
      let T : LOOConcentration.Estimator 1 1 (r+1) := fun D =>
        { toFun := fun x => fun _ =>
            (∑ i : Fin (r+1), Kh (x 0-(D i).1 0)*(D i).2 0)/
              ((∑ i : Fin (r+1), Kh (x 0-(D i).1 0))+(r+1 : ℝ)*δ)
          continuous_toFun := by
            apply continuous_pi
            intro _
            have hKh : ∀ t, 0 ≤ Kh t := fun t =>
              div_nonneg (gaussianPDFReal_nonneg 0 1 (t/h)) hh.le
            have hDen (x : LOOConcentration.Features 1) :
                (∑ i : Fin (r+1), Kh (x 0-(D i).1 0))+(r+1 : ℝ)*δ ≠ 0 := by
              exact ne_of_gt (add_pos_of_nonneg_of_pos
                (Finset.sum_nonneg (fun i _ => hKh _)) (by positivity))
            have hCont : Continuous Kh :=
              (gaussianKernel_normalization_and_bounds.1.continuous.comp
                (continuous_id.div_const h)).div_const h
            have hAtom (i : Fin (r+1)) : Continuous
                (fun x : LOOConcentration.Features 1 => Kh (x 0-(D i).1 0)) :=
              hCont.comp ((continuous_apply 0).sub continuous_const)
            apply Continuous.div
              (continuous_finsetSum _ (fun i _ => (hAtom i).mul continuous_const))
              ((continuous_finsetSum _ (fun i _ => hAtom i)).add continuous_const) hDen }
      let L := fun u v : LOOConcentration.Responses 1 => |u 0-v 0|
      ∃ hFin : ∀ z : LOOConcentration.Observation 1 1,
        Integrable (fun D => LOOConcentration.fittedLoss T L D z)
          (Measure.pi (fun _ : Fin (r+1) => μ)),
        let G := fun E : EuclideanSpace ℝ (LOOConcentration.ObservationCoordinate 1 1) =>
          LOOConcentration.Revision.meanFittedLoss μ T L
            (LOOConcentration.Revision.observationOfEuclidean E)
            (hFin (LOOConcentration.Revision.observationOfEuclidean E))
        LocallyLipschitz G ∧
          ∀ᵐ E ∂(volume : Measure (EuclideanSpace ℝ (LOOConcentration.ObservationCoordinate 1 1))),
            DifferentiableAt ℝ G E ∧ ‖gradient G E‖ ≤ C := by
  obtain ⟨C,hC,hFields⟩ := gaussianKernel_actual_expectedLoss_ambient_gradient_fields μ hSecond h δ hh hδ
  refine ⟨C,hC,?_⟩
  intro r Kh T L
  have hField := hFields r
  refine ⟨fun z => hField.1 z,?_⟩
  exact ⟨hField.2.2.1,hField.2.2.2⟩

end LOOConcentration.Manuscript.Internal
