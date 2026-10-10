import LOOConcentrationManuscript.Internal.GaussianKernelStandingAssemblyConsumer
import LOOConcentrationManuscript.Frozen.Definitions.StabilizedKernelEstimator
import LOOConcentrationRevision.Frozen.Results.MainConcentration

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

/-- The literal author-approved estimator consumes every proved Standing field. -/
theorem gaussianKernel_approved_estimator_complete_standing
    (μ : Measure (LOOConcentration.Observation 1 1)) [IsProbabilityMeasure μ]
    (hSecond : Integrable LOOConcentration.observationNormSq μ)
    (hLSI : LOOConcentration.Revision.observationLogSobolevConstant μ < ⊤)
    (h δ : ℝ) (hh : 0 < h) (hδ : 0 < δ) :
    let K : {K : ℝ → ℝ // Continuous K ∧ ∀ x, 0 ≤ K x} :=
      ⟨gaussianPDFReal 0 1, gaussianKernel_normalization_and_bounds.1.continuous,
        gaussianPDFReal_nonneg 0 1⟩
    let T := stabilizedKernelEstimator K ⟨h, hh⟩ ⟨δ, hδ⟩
    let L := fun u v : LOOConcentration.Responses 1 => |u 0 - v 0|
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, 0 ≤ B ∧ ∃ M : ℝ, 0 < M ∧ ∀ n : ℕ,
      LOOConcentration.Revision.StandingAssumption (n := n) μ T L
        (fun N _ => C / Real.sqrt (N : ℝ)) (fun N _ => C / (N : ℝ))
        (fun N => B / (N : ℝ)) M 0 := by
  intro K T L
  let Kh := fun t : ℝ => gaussianPDFReal 0 1 (t/h)/h
  let T' : ∀ r : ℕ, LOOConcentration.Estimator 1 1 (r+1) := fun r D =>
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
  have hEq : T = T' := by
    funext r D
    apply ContinuousMap.ext
    intro x
    funext j
    simp only [T, T', stabilizedKernelEstimator, K, Kh, ContinuousMap.coe_mk,
      div_eq_mul_inv, mul_comm]
  rw [hEq]
  exact gaussianKernel_actual_complete_standing μ hSecond hLSI h δ hh hδ

end LOOConcentration.Manuscript.Internal
