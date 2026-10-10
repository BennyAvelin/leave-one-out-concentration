import LOOConcentrationManuscript.Internal.GaussianKernelApprovedExponentialTails

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

theorem gaussianKernel_approved_estimator_pointwise_risk_exponential_tails
    (μ : Measure (LOOConcentration.Observation 1 1)) [IsProbabilityMeasure μ]
    (hSecond : Integrable LOOConcentration.observationNormSq μ)
    (hLSI : LOOConcentration.Revision.observationLogSobolevConstant μ < ⊤)
    (h δ : ℝ) (hh : 0 < h) (hδ : 0 < δ) (ε : ℝ) (hε : 0 < ε) :
    let K : {K : ℝ → ℝ // Continuous K ∧ ∀ x, 0 ≤ K x} :=
      ⟨gaussianPDFReal 0 1, gaussianKernel_normalization_and_bounds.1.continuous,
        gaussianPDFReal_nonneg 0 1⟩
    let T := stabilizedKernelEstimator K ⟨h, hh⟩ ⟨δ, hδ⟩
    let L := fun u v : LOOConcentration.Responses 1 => |u 0 - v 0|
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      let H := fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (n + 2) =>
        (∫ z, LOOConcentration.fittedLoss (T (n + 1)) L D z ∂μ) -
          LOOConcentration.looEstimate (T n) L D
      (Measure.pi fun _ : Fin (n + 2) => μ).real {D | H D > ε} ≤
        3 * Real.exp (-c * (n : ℝ)) ∧
      (Measure.pi fun _ : Fin (n + 2) => μ).real {D | -H D > ε} ≤
        3 * Real.exp (-c * (n : ℝ)) := by
  intro K T L
  obtain ⟨_C,_hC,_B,_hB,_M,_hM,c,hc,n₀,hAll⟩ :=
    gaussianKernel_approved_estimator_exponential_main_tails μ hSecond hLSI h δ hh hδ ε hε
  refine ⟨c,hc,n₀,?_⟩
  intro n hn H
  obtain ⟨hStanding,hTails⟩ := hAll n hn
  let P := Measure.pi fun _ : Fin (n + 2) => μ
  let hf := hStanding.stable.integrable_full n
  have hRisk : (fun D => (LOOConcentration.Revision.looRiskL1 μ (T (n + 1)) L hf) D) =ᵐ[P]
      (fun D => ∫ z, LOOConcentration.fittedLoss (T (n + 1)) L D z ∂μ) := by
    exact hf.integral_prod_left.coeFn_toL1
  have hPos : P.real {D | H D > ε} = P.real {D |
      (LOOConcentration.Revision.looRiskL1 μ (T (n + 1)) L hf) D -
        LOOConcentration.looEstimate (T n) L D > ε} := by
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [hRisk] with D hD
    change ((∫ z, LOOConcentration.fittedLoss (T (n + 1)) L D z ∂μ) -
      LOOConcentration.looEstimate (T n) L D > ε) =
      ((LOOConcentration.Revision.looRiskL1 μ (T (n + 1)) L hf) D -
        LOOConcentration.looEstimate (T n) L D > ε)
    rw [hD]
  have hNeg : P.real {D | -H D > ε} = P.real {D |
      -((LOOConcentration.Revision.looRiskL1 μ (T (n + 1)) L hf) D -
        LOOConcentration.looEstimate (T n) L D) > ε} := by
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [hRisk] with D hD
    change (-((∫ z, LOOConcentration.fittedLoss (T (n + 1)) L D z ∂μ) -
      LOOConcentration.looEstimate (T n) L D) > ε) =
      (-((LOOConcentration.Revision.looRiskL1 μ (T (n + 1)) L hf) D -
        LOOConcentration.looEstimate (T n) L D) > ε)
    rw [hD]
  exact ⟨hPos ▸ hTails.1, hNeg ▸ hTails.2⟩

end LOOConcentration.Manuscript.Internal
