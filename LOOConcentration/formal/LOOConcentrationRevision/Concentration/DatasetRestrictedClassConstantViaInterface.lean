import LOOConcentrationRevision.Probability.RestrictionSubgaussianClass
import LOOConcentrationRevision.Concentration.HerbstFromFiniteLsiInterface
import LOOConcentrationRevision.FunctionalInequalities.DatasetProductLSI

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory

/-- The actual ordered dataset conditioning event consumes the whole BNT
class-infimum comparison, followed by the exact base-constant Herbst and
product LSI bounds. All laws, events and normalization are produced internally. -/
theorem dataset_normalizedRestriction_subgaussian_class_infimum_le_via_finite_lsi_interface
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (hfinite : observationLogSobolevConstant μ < ⊤)
    (K : Set (Dataset (Observation k m) (n + 2))) (hK : MeasurableSet K)
    (hq : 0 < (Measure.pi fun _ : Fin (n + 2) => μ).real K) :
    let Q := datasetLawOfObservation (r := n + 2) μ
    let A := datasetOfEuclidean ⁻¹' K
    let ν := normalizedRestriction Q A
    sInf {d : ENNReal | ∃ c : NNReal, d = (c : ENNReal) ∧
      ∀ F : EuclideanSpace ℝ (DatasetCoordinate k m (n + 2)) → ℝ,
        Integrable F ν → (∀ x ∈ A, ∀ y ∈ A, |F x - F y| ≤ ‖x-y‖) →
        ProbabilityTheory.HasSubgaussianMGF
          (fun x => F x - ∫ y, F y ∂ν) c ν} ≤
    ENNReal.ofReal ((3*(2:ℝ)^12*Real.exp 2)*
      Real.log (Real.exp 1/(Measure.pi fun _ : Fin (n + 2) => μ).real K)) *
      observationLogSobolevConstant μ := by
  let P := Measure.pi fun _ : Fin (n + 2) => μ
  let Q := datasetLawOfObservation (r := n + 2) μ
  let A := datasetOfEuclidean ⁻¹' K
  let : IsProbabilityMeasure Q := datasetLawOfObservation_isProbabilityMeasure μ
  have hA : MeasurableSet A := hK.preimage measurable_datasetOfEuclidean
  have hPreimage : datasetToEuclidean ⁻¹' A = K := by
    ext D
    simp only [A, Set.mem_preimage, datasetOfEuclidean_datasetToEuclidean]
  have hqeq : Q.real A = P.real K := by
    change ((Measure.pi fun _ : Fin (n + 2) => μ).map datasetToEuclidean).real A = _
    unfold Measure.real
    rw [Measure.map_apply measurable_datasetToEuclidean hA, hPreimage]
  have hqa : 0 < Q.real A := hqeq ▸ hq
  have hAll := (dataset_completed_lsi_and_bounded_truncations_of_finite (n := n) μ hfinite).1
  have hLC : logSobolevConstant Q ≤ observationLogSobolevConstant μ :=
    (logSobolevConstant_le_iff _).2 (fun u _ => hAll u)
  have hQfinite : logSobolevConstant Q < ⊤ := lt_of_le_of_lt hLC hfinite
  have hSG := sInf_integrable_lipschitz_subgaussian_proxies_le_via_finite_lsi_interface Q hQfinite
  have hBNT := normalizedRestriction_local_subgaussian_class_infimum_le Q A hA hqa
  rw [hqeq] at hBNT
  apply hBNT.trans
  gcongr
  exact hSG.trans hLC

end LOOConcentration.Revision
