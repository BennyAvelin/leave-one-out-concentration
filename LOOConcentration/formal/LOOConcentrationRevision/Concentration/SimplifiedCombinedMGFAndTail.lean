import LOOConcentration.Concentration.SubGaussianSum
import LOOConcentrationRevision.Concentration.StandingRiskSubGaussian
import LOOConcentrationRevision.Concentration.StandingValidationSubGaussian
import LOOConcentrationRevision.Concentration.StandingI1UniformMGF
import LOOConcentrationRevision.Results.StandingLossDecomposition
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

open MeasureTheory Filter
open scoped Topology ENNReal

namespace LOOConcentration.Revision

noncomputable section

/-- The actual risk-error remainder after removing the deterministic source bias
has the source-constant sub-Gaussian MGF, obtained by Hölder addition of the
three actual standing MGF providers. -/
theorem simplified_combined_mgf
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (h : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)
    (hzero : ∀ z, δ₂ (n + 1) z = 0 ∧ δ₂ (n + 2) z = 0)
    (hLip : ∀ z w,
      |meanFittedLoss μ (T n) L z (h.mean_integrable z) -
        meanFittedLoss μ (T n) L w (h.mean_integrable w)| ≤
          c * observationNorm (z - w))
    (a : NNReal)
    (ha : ∀ᵐ z ∂μ, δ₁ (n + 1) z ≤ (a : ℝ)) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun D : Dataset (Observation k m) (n + 2) =>
        (looRiskL1 μ (T (n + 1)) L (h.stable.integrable_full n)) D -
          looEstimate (T n) L D -
          standingB μ T L δ₁ δ₂ δ₃ c d h)
      (NNReal.mk
        ((observationLogSobolevConstant μ).toReal *
          ((a : ℝ) + c / Real.sqrt (n + 2 : ℝ) +
            ∫ z, δ₁ (n + 2) z ∂μ) ^ 2)
        (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)))
      (Measure.pi fun _ : Fin (n + 2) => μ) := by
  let ν : Measure (Dataset (Observation k m) (n + 2)) :=
    Measure.pi fun _ : Fin (n + 2) => μ
  let C : ℝ := (observationLogSobolevConstant μ).toReal
  let N : ℝ := (n + 2 : ℝ)
  let mbar : ℝ := ∫ z, δ₁ (n + 2) z ∂μ
  let Cnn : NNReal := ⟨C, ENNReal.toReal_nonneg⟩
  let sA : NNReal := a
  let sV : NNReal := ⟨c / Real.sqrt N,
    div_nonneg h.c_nonneg (Real.sqrt_nonneg _)⟩
  have hN : 0 < N := by dsimp [N]; positivity
  have hmbar : 0 ≤ mbar := by
    dsimp [mbar]
    exact integral_nonneg fun z => h.stable.delta₁_nonneg (n + 1) z
  let sR : NNReal := ⟨mbar, hmbar⟩
  let sourceScale : ℝ := (a : ℝ) + c / Real.sqrt N + mbar
  let sourceProxy : NNReal := ⟨C * sourceScale ^ 2,
    mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)⟩
  have hI1 := standing_I1_uniform_hasSubgaussianMGF
    μ T L δ₁ δ₂ δ₃ c d h (fun z => (hzero z).1) a ha
  have hV := validationAverage_hasSubgaussianMGF_of_revisedStanding
    μ T L δ₁ δ₂ δ₃ c d h hLip
  have hRisk := standing_risk_hasSubgaussianMGF
    μ T L δ₁ δ₂ δ₃ c d h (fun z => (hzero z).2)
  have hParamA : NNReal.mk (C * (a : ℝ) ^ 2)
      (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)) =
      LOOConcentration.Concentration.subGaussianProxy Cnn sA := by
    apply NNReal.eq
    rw [LOOConcentration.Concentration.coe_subGaussianProxy]
    change C * (a : ℝ) ^ 2 = C * (sA : ℝ) ^ 2
    rfl
  have hParamV : NNReal.mk (C * c ^ 2 / N)
      (div_nonneg (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg c)) (le_of_lt hN)) =
      LOOConcentration.Concentration.subGaussianProxy Cnn sV := by
    apply NNReal.eq
    rw [LOOConcentration.Concentration.coe_subGaussianProxy]
    change C * c ^ 2 / N = C * (c / Real.sqrt N) ^ 2
    rw [div_pow, Real.sq_sqrt (le_of_lt hN)]
    ring
  have hParamR : NNReal.mk (C * mbar ^ 2)
      (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)) =
      LOOConcentration.Concentration.subGaussianProxy Cnn sR := by
    apply NNReal.eq
    rw [LOOConcentration.Concentration.coe_subGaussianProxy]
    change C * mbar ^ 2 = C * (sR : ℝ) ^ 2
    rfl
  rw [hParamA] at hI1
  rw [hParamV] at hV
  rw [hParamR] at hRisk
  have hI1' : ProbabilityTheory.HasSubgaussianMGF
      (standingI1 μ T L δ₁ δ₂ δ₃ c d h)
      (LOOConcentration.Concentration.subGaussianProxy Cnn sA) ν := by
    apply hI1.congr
    filter_upwards with D
    simp [standingI1, standingV]
  have hVneg := hV.neg
  have hI2 : ProbabilityTheory.HasSubgaussianMGF
      (standingI2 μ T L δ₁ δ₂ δ₃ c d h)
      (LOOConcentration.Concentration.subGaussianProxy Cnn sV) ν := by
    apply hVneg.congr
    filter_upwards with D
    simp [standingI2, standingEV, standingV]
    
  have hI3 : ProbabilityTheory.HasSubgaussianMGF
      (standingI3 μ T L δ₁ δ₂ δ₃ c d h)
      (LOOConcentration.Concentration.subGaussianProxy Cnn sR) ν := by
    apply hRisk.congr
    filter_upwards with D
    simp [standingI3, standingRisk, standingER]
  have h12 := hI1'.add hI2
  have h123 := h12.add hI3
  have hproxy :
      ((((LOOConcentration.Concentration.subGaussianProxy Cnn sA).sqrt +
          (LOOConcentration.Concentration.subGaussianProxy Cnn sV).sqrt) ^ 2).sqrt +
        (LOOConcentration.Concentration.subGaussianProxy Cnn sR).sqrt) ^ 2 =
        LOOConcentration.Concentration.subGaussianProxy Cnn (sA + sV + sR) := by
    simp [LOOConcentration.Concentration.subGaussianProxy, mul_add]
  have h123' : ProbabilityTheory.HasSubgaussianMGF
      (fun D => (standingI1 μ T L δ₁ δ₂ δ₃ c d h D +
        standingI2 μ T L δ₁ δ₂ δ₃ c d h D) +
          standingI3 μ T L δ₁ δ₂ δ₃ c d h D)
      (LOOConcentration.Concentration.subGaussianProxy Cnn (sA + sV + sR)) ν := by
    simpa only [hproxy] using h123
  have hdecomp := standingLoss_decomposition μ T L δ₁ δ₂ δ₃ c d h
  have hEq : (fun D => (standingI1 μ T L δ₁ δ₂ δ₃ c d h D +
      standingI2 μ T L δ₁ δ₂ δ₃ c d h D) +
        standingI3 μ T L δ₁ δ₂ δ₃ c d h D) =ᵐ[ν]
      (fun D => standingH μ T L δ₁ δ₂ δ₃ c d h D -
        standingB μ T L δ₁ δ₂ δ₃ c d h) := by
    filter_upwards with D
    have hD := hdecomp D
    dsimp [standingH, standingB] at hD ⊢
    linarith
  have hcombined := h123'.congr hEq
  have hFinalParam : sourceProxy =
      LOOConcentration.Concentration.subGaussianProxy Cnn (sA + sV + sR) := by
    apply NNReal.eq
    rw [LOOConcentration.Concentration.coe_subGaussianProxy]
    change C * sourceScale ^ 2 = C * ((sA : ℝ) + (sV : ℝ) + (sR : ℝ)) ^ 2
    have hscale : sourceScale = (sA : ℝ) + (sV : ℝ) + (sR : ℝ) := by
      change (a : ℝ) + c / Real.sqrt N + mbar =
        (a : ℝ) + (c / Real.sqrt N) + mbar
      rfl
    rw [hscale]
  have hCombined' : ProbabilityTheory.HasSubgaussianMGF
      (fun D => standingH μ T L δ₁ δ₂ δ₃ c d h D -
        standingB μ T L δ₁ δ₂ δ₃ c d h)
      sourceProxy ν := by
    simpa only [hFinalParam] using hcombined
  change ProbabilityTheory.HasSubgaussianMGF
      (fun D => standingH μ T L δ₁ δ₂ δ₃ c d h D -
        standingB μ T L δ₁ δ₂ δ₃ c d h)
      sourceProxy ν at hCombined'
  change ProbabilityTheory.HasSubgaussianMGF
    (fun D => standingH μ T L δ₁ δ₂ δ₃ c d h D -
      standingB μ T L δ₁ δ₂ δ₃ c d h)
    sourceProxy ν
  exact hCombined'

end
end LOOConcentration.Revision
