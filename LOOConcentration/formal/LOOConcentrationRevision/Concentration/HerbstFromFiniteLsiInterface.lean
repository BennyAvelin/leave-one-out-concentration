import LOOConcentrationRevision.FunctionalInequalities.FiniteLsiTruncation
import LOOConcentrationRevision.Concentration.LipschitzHerbstTail
import LOOConcentrationRevision.Probability.LipschitzIntegrability

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory

/-- The actual completed-pair interface supplies the bound used by Herbst. -/
theorem lipschitz_hasSubgaussianMGF_via_finite_lsi_interface
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hfinite : logSobolevConstant μ < ⊤)
    (F : EuclideanSpace ℝ ι → ℝ) (L : NNReal)
    (hLip : LipschitzWith L F) (hF : Integrable F μ) :
    ProbabilityTheory.HasSubgaussianMGF (fun x => F x - ∫ y, F y ∂μ)
      (NNReal.mk ((logSobolevConstant μ).toReal * (L : ℝ)^2)
        (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))) μ := by
  have hAll := (completed_lsi_and_bounded_truncations_of_finite μ hfinite).1
  have hLC : logSobolevConstant μ ≤ logSobolevConstant μ :=
    (logSobolevConstant_le_iff _).2 (fun u _ => hAll u)
  have hReal : logSobolevConstant μ ≤ ENNReal.ofReal (logSobolevConstant μ).toReal := by
    exact hLC.trans_eq (ENNReal.ofReal_toReal hfinite.ne).symm
  exact lipschitz_hasSubgaussianMGF_of_constant_bound μ _ ENNReal.toReal_nonneg
    hReal F L hLip hF

/-- One genuine finite proxy works for the whole source class before choosing
an observable or parameter, and bounds its literal infimum. -/
theorem sInf_integrable_lipschitz_subgaussian_proxies_le_via_finite_lsi_interface
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hfinite : logSobolevConstant μ < ⊤) :
    sInf {c : ENNReal | ∃ c₀ : NNReal, c = (c₀ : ENNReal) ∧
      ∀ F : EuclideanSpace ℝ ι → ℝ, Integrable F μ → LipschitzWith 1 F →
        ProbabilityTheory.HasSubgaussianMGF (fun x => F x - ∫ y, F y ∂μ) c₀ μ} ≤
      logSobolevConstant μ := by
  let c₀ : NNReal := (logSobolevConstant μ).toNNReal
  have hc : (c₀ : ENNReal) = logSobolevConstant μ := ENNReal.coe_toNNReal hfinite.ne
  rw [← hc]
  apply sInf_le
  refine ⟨c₀, rfl, ?_⟩
  intro F hF hLip
  have h := lipschitz_hasSubgaussianMGF_via_finite_lsi_interface μ hfinite F 1 hLip hF
  have hp : NNReal.mk ((logSobolevConstant μ).toReal * ((1 : NNReal) : ℝ)^2)
      (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)) = c₀ := by
    apply Subtype.ext
    change (logSobolevConstant μ).toReal * (1:ℝ)^2 = (logSobolevConstant μ).toReal
    ring
  rw [hp] at h
  exact h

/-- The ordered dataset interface supplies the same base constant and internally
produces the raw moment and integrability of the actual global observable. -/
theorem dataset_lipschitz_hasSubgaussianMGF_via_finite_lsi_interface
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (hfinite : observationLogSobolevConstant μ < ⊤)
    (F : EuclideanSpace ℝ (DatasetCoordinate k m (n+2)) → ℝ) (L : NNReal)
    (hLip : LipschitzWith L F) :
    let Q := datasetLawOfObservation (r := n+2) μ
    ProbabilityTheory.HasSubgaussianMGF (fun x => F x - ∫ y, F y ∂Q)
      (NNReal.mk ((observationLogSobolevConstant μ).toReal * (L : ℝ)^2)
        (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))) Q := by
  let Q := datasetLawOfObservation (r := n+2) μ
  let : IsProbabilityMeasure Q := datasetLawOfObservation_isProbabilityMeasure μ
  have hAll := (dataset_completed_lsi_and_bounded_truncations_of_finite (n := n) μ hfinite).1
  have hLC : logSobolevConstant Q ≤ observationLogSobolevConstant μ :=
    (logSobolevConstant_le_iff _).2 (fun u _ => hAll u)
  have hReal : logSobolevConstant Q ≤ ENNReal.ofReal (observationLogSobolevConstant μ).toReal := by
    exact hLC.trans_eq (ENNReal.ofReal_toReal hfinite.ne).symm
  have hM2 := integrable_datasetLaw_norm_sq (r := n+2) μ
    (integrable_observationNormSq_of_finite_lsi μ hfinite)
  have hInt := integrable_lipschitz_of_norm_sq Q hM2 F L hLip
  exact lipschitz_hasSubgaussianMGF_of_constant_bound Q _ ENNReal.toReal_nonneg
    hReal F L hLip hInt

end LOOConcentration.Revision
