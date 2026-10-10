import LOOConcentrationRevision.FunctionalInequalities.BoundedProductLSI
import LOOConcentrationRevision.Probability.ProductLawTransport
import LOOConcentrationRevision.Frozen.Definitions.ObservationLogSobolevConstant

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory

/-- The actual ordered dataset law inherits the observation's intrinsic
constant, including empty observation coordinate carriers. -/
theorem logSobolevConstant_datasetLaw_le {k m n : ℕ}
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (hfinite : observationLogSobolevConstant μ < ⊤) :
    let ν := datasetLawOfObservation (r := n + 2) μ
    let _ : IsProbabilityMeasure ν := datasetLawOfObservation_isProbabilityMeasure μ
    logSobolevConstant ν ≤ observationLogSobolevConstant μ := by
  let : IsProbabilityMeasure (μ.map observationToEuclidean) :=
    Measure.isProbabilityMeasure_map measurable_observationToEuclidean.aemeasurable
  have hbase : logSobolevConstant (μ.map observationToEuclidean) < ⊤ := hfinite
  have h := logSobolevConstant_euclideanProductLaw_le (n + 1)
    (μ.map observationToEuclidean) hbase
  simpa only [euclideanProductLaw_observation_map_eq_datasetLaw μ,
    observationLogSobolevConstant] using h

/-- The source's product LSI acts on the same actual completed dataset pair;
no product inequality, gradient identity or pair witness is supplied. -/
theorem all_pairs_lsi_datasetLaw {k m n : ℕ}
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (hfinite : observationLogSobolevConstant μ < ⊤)
    (u : let ν := datasetLawOfObservation (r := n + 2) μ
      let _ : IsProbabilityMeasure ν := datasetLawOfObservation_isProbabilityMeasure μ
      SobolevPair ν) :
    let ν := datasetLawOfObservation (r := n + 2) μ
    let _ : IsProbabilityMeasure ν := datasetLawOfObservation_isProbabilityMeasure μ
    squareEntropy ν (WithLp.ofLp u.val).1 ≤
      2 * observationLogSobolevConstant μ * sobolevEnergy ν u := by
  let : IsProbabilityMeasure (μ.map observationToEuclidean) :=
    Measure.isProbabilityMeasure_map measurable_observationToEuclidean.aemeasurable
  have hbase : logSobolevConstant (μ.map observationToEuclidean) < ⊤ := hfinite
  let νP := euclideanProductLaw (κ := Fin (n + 2)) (μ.map observationToEuclidean)
  let : IsProbabilityMeasure νP := euclideanProductLaw_isProbabilityMeasure _
  let νD := datasetLawOfObservation (r := n + 2) μ
  let : IsProbabilityMeasure νD := datasetLawOfObservation_isProbabilityMeasure μ
  have h : ∀ v : SobolevPair νP,
      squareEntropy νP (WithLp.ofLp v.val).1 ≤
        2 * logSobolevConstant (μ.map observationToEuclidean) * sobolevEnergy νP v := by
    intro v
    exact all_pairs_lsi_euclideanProductLaw (n + 1) (μ.map observationToEuclidean) hbase v
  have hTransfer (ν : Measure (EuclideanSpace ℝ (DatasetCoordinate k m (n + 2))))
      [IsProbabilityMeasure ν] (heq : ν = νP) :
      ∀ v : SobolevPair ν, squareEntropy ν (WithLp.ofLp v.val).1 ≤
        2 * observationLogSobolevConstant μ * sobolevEnergy ν v := by
    subst ν
    exact h
  exact hTransfer νD (euclideanProductLaw_observation_map_eq_datasetLaw μ).symm u

end LOOConcentration.Revision
