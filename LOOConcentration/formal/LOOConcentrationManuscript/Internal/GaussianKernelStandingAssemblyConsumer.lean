import LOOConcentrationManuscript.Internal.GaussianKernelStandingAssembly
import LOOConcentrationRevision.Frozen.Definitions.LooRiskL1_characterization

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

/-- The actual Gaussian standing inputs construct the frozen conditional risk
with its sample-conditioned expectation characterization. -/
theorem gaussianKernel_actual_standing_and_conditionalRisk
    (μ : Measure (LOOConcentration.Observation 1 1)) [IsProbabilityMeasure μ]
    (hSecond : Integrable LOOConcentration.observationNormSq μ)
    (hLSI : LOOConcentration.Revision.observationLogSobolevConstant μ < ⊤)
    (h δ : ℝ) (hh : 0 < h) (hδ : 0 < δ) :
      let Kh := fun t : ℝ => gaussianPDFReal 0 1 (t/h)/h
      let T : ∀ r : ℕ, LOOConcentration.Estimator 1 1 (r+1) := fun r D =>
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
      ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, 0 ≤ B ∧ ∃ M : ℝ, 0 < M ∧ ∀ n : ℕ,
        ∃ hStanding : LOOConcentration.Revision.StandingAssumption (n := n) μ T L
          (fun N _ => C/Real.sqrt (N : ℝ)) (fun N _ => C/(N : ℝ))
          (fun N => B/(N : ℝ)) M 0,
          ((Measure.pi (fun _ : Fin (n+2) => μ)).prod μ)[
            (fun p : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (n+2) ×
              LOOConcentration.Observation 1 1 =>
              LOOConcentration.fittedLoss (T (n+1)) L p.1 p.2) |
            MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[
              ((Measure.pi (fun _ : Fin (n+2) => μ)).prod μ)]
            fun p => (LOOConcentration.Revision.looRiskL1 μ (T (n+1)) L
              (hStanding.stable.integrable_full n)) p.1 := by
  intro Kh T L
  obtain ⟨C,hC,B,hB,M,hM,hAll⟩ := gaussianKernel_actual_complete_standing μ hSecond hLSI h δ hh hδ
  refine ⟨C,hC,B,hB,M,hM,?_⟩
  intro n
  exact ⟨hAll n,LOOConcentration.Revision.looRiskL1_characterization μ (T (n+1)) L
    ((hAll n).stable.integrable_full n)⟩

end LOOConcentration.Manuscript.Internal
