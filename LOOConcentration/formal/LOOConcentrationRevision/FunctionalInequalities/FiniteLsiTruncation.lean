import LOOConcentrationRevision.FunctionalInequalities.TruncationLsiFromMoments
import LOOConcentrationRevision.Probability.FiniteLsiSecondMoment
import LOOConcentrationRevision.Probability.EuclideanProductSecondMoment
import LOOConcentrationRevision.FunctionalInequalities.DatasetProductLSI

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory

/-- Finite intrinsic LSI alone discharges the source truncation and completed
pair inequality premises; the raw moment is derived inside this producer. -/
theorem completed_lsi_and_bounded_truncations_of_finite
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hfinite : logSobolevConstant μ < ⊤) :
    (∀ u : SobolevPair μ, squareEntropy μ (WithLp.ofLp u.val).1 ≤
      2*logSobolevConstant μ*sobolevEnergy μ u) ∧
    (∀ (F : EuclideanSpace ℝ ι → ℝ), LocallyLipschitz F →
      ∀ (a b R : NNReal),
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ ι)),
          DifferentiableAt ℝ F x ∧ ‖gradient F x‖ ≤ (a:ℝ)+(b:ℝ)*‖x‖) →
        ∃ u : SobolevPair μ,
          ((WithLp.ofLp u.val).1 : EuclideanSpace ℝ ι → ℝ) =ᵐ[μ]
            (fun x => max (-(R:ℝ)) (min (F x) (R:ℝ))) ∧
          (∀ᵐ x ∂μ, ‖((WithLp.ofLp u.val).2 :
              EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x‖ ≤ (a:ℝ)+(b:ℝ)*‖x‖) ∧
          squareEntropy μ (WithLp.ofLp u.val).1 ≤ 2*logSobolevConstant μ*sobolevEnergy μ u) := by
  exact completed_lsi_and_bounded_truncations_of_norm_sq μ (logSobolevConstant μ)
    hfinite le_rfl (norm_sq_integrable_of_finite_logSobolevConstant μ hfinite)

/-- Every positive finite product has the same base-constant completed LSI and
joint truncation witnesses. Both base and product moments are proved internally. -/
theorem product_completed_lsi_and_bounded_truncations_of_finite_base
    {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℕ)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hfinite : logSobolevConstant μ < ⊤) :
    let ν := euclideanProductLaw (κ := Fin (r+1)) μ
    let _ : IsProbabilityMeasure ν := euclideanProductLaw_isProbabilityMeasure μ
    (∀ u : SobolevPair ν, squareEntropy ν (WithLp.ofLp u.val).1 ≤
      2*logSobolevConstant μ*sobolevEnergy ν u) ∧
    (∀ (F : EuclideanSpace ℝ (Fin (r+1) × ι) → ℝ), LocallyLipschitz F →
      ∀ (a b R : NNReal),
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin (r+1) × ι))),
          DifferentiableAt ℝ F x ∧ ‖gradient F x‖ ≤ (a:ℝ)+(b:ℝ)*‖x‖) →
        ∃ u : SobolevPair ν,
          ((WithLp.ofLp u.val).1 : EuclideanSpace ℝ (Fin (r+1) × ι) → ℝ) =ᵐ[ν]
            (fun x => max (-(R:ℝ)) (min (F x) (R:ℝ))) ∧
          (∀ᵐ x ∂ν, ‖((WithLp.ofLp u.val).2 :
              EuclideanSpace ℝ (Fin (r+1) × ι) → EuclideanSpace ℝ (Fin (r+1) × ι)) x‖ ≤ (a:ℝ)+(b:ℝ)*‖x‖) ∧
          squareEntropy ν (WithLp.ofLp u.val).1 ≤ 2*logSobolevConstant μ*sobolevEnergy ν u) := by
  let ν := euclideanProductLaw (κ := Fin (r+1)) μ
  let : IsProbabilityMeasure ν := euclideanProductLaw_isProbabilityMeasure μ
  have hBaseM2 := norm_sq_integrable_of_finite_logSobolevConstant μ hfinite
  have hProdM2 := integrable_euclideanProductLaw_norm_sq (κ := Fin (r+1)) μ hBaseM2
  have hLC := logSobolevConstant_euclideanProductLaw_le r μ hfinite
  exact completed_lsi_and_bounded_truncations_of_norm_sq ν (logSobolevConstant μ)
    hfinite hLC hProdM2

/-- The actual observation pushforward moment returns to the source observation
carrier with its unnormalized sum of squares, including empty coordinates. -/
theorem integrable_observationNormSq_of_finite_lsi
    {k m : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (hfinite : observationLogSobolevConstant μ < ⊤) :
    Integrable observationNormSq μ := by
  let ρ := μ.map observationToEuclidean
  let : IsProbabilityMeasure ρ :=
    Measure.isProbabilityMeasure_map measurable_observationToEuclidean.aemeasurable
  have hρfinite : logSobolevConstant ρ < ⊤ := hfinite
  have hρM2 := norm_sq_integrable_of_finite_logSobolevConstant ρ hρfinite
  have hRaw := (integrable_map_measure (continuous_norm.pow 2).aestronglyMeasurable
    measurable_observationToEuclidean.aemeasurable).1 hρM2
  convert hRaw using 1
  funext z
  change observationNormSq z = ‖observationToEuclidean z‖^2
  rw [← observationNorm_eq_euclidean, observationNorm_sq]

/-- The same observation constant and actual ordered dataset law provide both
full LSI and all source truncations without an external moment premise. -/
theorem dataset_completed_lsi_and_bounded_truncations_of_finite
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (hfinite : observationLogSobolevConstant μ < ⊤) :
    let ν := datasetLawOfObservation (r := n+2) μ
    let _ : IsProbabilityMeasure ν := datasetLawOfObservation_isProbabilityMeasure μ
    (∀ u : SobolevPair ν, squareEntropy ν (WithLp.ofLp u.val).1 ≤
      2*observationLogSobolevConstant μ*sobolevEnergy ν u) ∧
    (∀ (F : EuclideanSpace ℝ (DatasetCoordinate k m (n+2)) → ℝ), LocallyLipschitz F →
      ∀ (a b R : NNReal),
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (DatasetCoordinate k m (n+2)))),
          DifferentiableAt ℝ F x ∧ ‖gradient F x‖ ≤ (a:ℝ)+(b:ℝ)*‖x‖) →
        ∃ u : SobolevPair ν,
          ((WithLp.ofLp u.val).1 : EuclideanSpace ℝ (DatasetCoordinate k m (n+2)) → ℝ) =ᵐ[ν]
            (fun x => max (-(R:ℝ)) (min (F x) (R:ℝ))) ∧
          (∀ᵐ x ∂ν, ‖((WithLp.ofLp u.val).2 :
              EuclideanSpace ℝ (DatasetCoordinate k m (n+2)) → EuclideanSpace ℝ (DatasetCoordinate k m (n+2))) x‖ ≤ (a:ℝ)+(b:ℝ)*‖x‖) ∧
          squareEntropy ν (WithLp.ofLp u.val).1 ≤ 2*observationLogSobolevConstant μ*sobolevEnergy ν u) := by
  let ν := datasetLawOfObservation (r := n+2) μ
  let : IsProbabilityMeasure ν := datasetLawOfObservation_isProbabilityMeasure μ
  have hObsM2 := integrable_observationNormSq_of_finite_lsi μ hfinite
  have hProdM2 := integrable_datasetLaw_norm_sq (r := n+2) μ hObsM2
  have hLC := logSobolevConstant_datasetLaw_le (n := n) μ hfinite
  exact completed_lsi_and_bounded_truncations_of_norm_sq ν (observationLogSobolevConstant μ)
    hfinite hLC hProdM2

end LOOConcentration.Revision
