import LOOConcentrationRevision.Concentration.LipschitzHerbst
import LOOConcentrationRevision.Probability.LipschitzIntegrability
import LOOConcentrationRevision.FunctionalInequalities.DatasetProductLSI

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory

/-- Every globally Lipschitz test of the actual ordered dataset law has the
same base-constant centered MGF. Its integrability and product LSI are produced
from the exact observation constant and raw observation second moment. -/
theorem dataset_lipschitz_hasSubgaussianMGF
    {k m n : ℕ} (μ : Measure (LOOConcentration.Observation k m)) [IsProbabilityMeasure μ]
    (hfinite : observationLogSobolevConstant μ < ⊤)
    (hM2 : Integrable LOOConcentration.observationNormSq μ)
    (F : EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (n + 2)) → ℝ)
    (L : NNReal) (hLip : LipschitzWith L F) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun x => F x - ∫ y, F y ∂datasetLawOfObservation (r := n + 2) μ)
      (NNReal.mk ((observationLogSobolevConstant μ).toReal * (L : ℝ)^2)
        (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)))
      (datasetLawOfObservation (r := n + 2) μ) := by
  let ν := datasetLawOfObservation (r := n + 2) μ
  let : IsProbabilityMeasure ν := datasetLawOfObservation_isProbabilityMeasure μ
  have hInt : Integrable F ν := integrable_lipschitz_of_norm_sq ν
    (integrable_datasetLaw_norm_sq μ hM2) F L hLip
  have hLC : logSobolevConstant ν ≤ ENNReal.ofReal (observationLogSobolevConstant μ).toReal := by
    rw [ENNReal.ofReal_toReal hfinite.ne]
    exact logSobolevConstant_datasetLaw_le μ hfinite
  constructor
  · intro lam
    exact (lipschitz_centered_exp_integrable_and_mgf_le ν _ ENNReal.toReal_nonneg
      hLC F L hLip hInt lam).1
  · intro lam
    have h := (lipschitz_centered_exp_integrable_and_mgf_le ν _ ENNReal.toReal_nonneg
      hLC F L hLip hInt lam).2
    change (∫ x, Real.exp (lam * (F x - ∫ y, F y ∂ν)) ∂ν) ≤
      Real.exp (((observationLogSobolevConstant μ).toReal * (L : ℝ)^2) * lam^2 / 2)
    exact h.trans_eq (congrArg Real.exp (by ring))

#print axioms dataset_lipschitz_hasSubgaussianMGF
end LOOConcentration.Revision
