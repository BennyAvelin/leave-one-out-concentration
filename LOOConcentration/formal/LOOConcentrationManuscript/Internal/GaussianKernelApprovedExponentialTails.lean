import LOOConcentrationManuscript.Internal.GaussianKernelApprovedMainTails
import LOOConcentrationManuscript.Internal.ScaledThetaExponential
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

theorem gaussianKernel_approved_estimator_exponential_main_tails
    (μ : Measure (LOOConcentration.Observation 1 1)) [IsProbabilityMeasure μ]
    (hSecond : Integrable LOOConcentration.observationNormSq μ)
    (hLSI : LOOConcentration.Revision.observationLogSobolevConstant μ < ⊤)
    (h δ : ℝ) (hh : 0 < h) (hδ : 0 < δ) (ε : ℝ) (hε : 0 < ε) :
    let K : {K : ℝ → ℝ // Continuous K ∧ ∀ x, 0 ≤ K x} :=
      ⟨gaussianPDFReal 0 1, gaussianKernel_normalization_and_bounds.1.continuous,
        gaussianPDFReal_nonneg 0 1⟩
    let T := stabilizedKernelEstimator K ⟨h, hh⟩ ⟨δ, hδ⟩
    let L := fun u v : LOOConcentration.Responses 1 => |u 0 - v 0|
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, 0 ≤ B ∧ ∃ M : ℝ, 0 < M ∧
      ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ hStanding : LOOConcentration.Revision.StandingAssumption (n := n) μ T L
        (fun N _ => C / Real.sqrt (N : ℝ)) (fun N _ => C / (N : ℝ))
        (fun N => B / (N : ℝ)) M 0,
        let H := fun D =>
          (LOOConcentration.Revision.looRiskL1 μ (T (n + 1)) L
            (hStanding.stable.integrable_full n)) D -
          LOOConcentration.looEstimate (T n) L D
        (Measure.pi fun _ : Fin (n + 2) => μ).real {D | H D > ε} ≤
          3 * Real.exp (-c * (n : ℝ)) ∧
        (Measure.pi fun _ : Fin (n + 2) => μ).real {D | -H D > ε} ≤
          3 * Real.exp (-c * (n : ℝ)) := by
  intro K T L
  obtain ⟨C,hC,B,hB,M,hM,hTails⟩ :=
    gaussianKernel_approved_estimator_uniform_main_tails μ hSecond hLSI h δ hh hδ
  obtain ⟨c,hc,n₀,hNumeric⟩ := thetaRate_three_scaled_exponential_bound
    (LOOConcentration.Revision.observationLogSobolevConstant μ).toReal
    (∫ z, LOOConcentration.observationNormSq z ∂μ) C B M ε
    ENNReal.toReal_nonneg (integral_nonneg (fun _ => by
      unfold LOOConcentration.observationNormSq; positivity)) hC.le hM.le hε
  refine ⟨C,hC,B,hB,M,hM,c,hc,n₀,?_⟩
  intro n hn
  obtain ⟨hStanding,hBound⟩ := hTails n
  obtain ⟨hThreshold,hRates⟩ := hNumeric n hn
  refine ⟨hStanding,?_⟩
  have hTail := hBound ε hThreshold
  exact ⟨hTail.1.trans hRates, hTail.2.trans hRates⟩

end LOOConcentration.Manuscript.Internal
