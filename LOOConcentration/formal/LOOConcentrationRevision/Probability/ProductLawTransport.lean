import LOOConcentrationRevision.Geometry.ProductEuclidean
import LOOConcentrationRevision.Probability.ProductSecondMoment
import LOOConcentrationRevision.Frozen.Definitions.Measurable_observationToEuclidean

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory

/-- The observation pushforward used by the intrinsic constant, tensorized and
flattened in order, is exactly the approved Euclidean dataset law. -/
theorem euclideanProductLaw_observation_map_eq_datasetLaw {k m r : ℕ}
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ] :
    euclideanProductLaw (κ := Fin r) (μ.map observationToEuclidean) =
      datasetLawOfObservation (r := r) μ := by
  let : IsProbabilityMeasure (μ.map observationToEuclidean) :=
    Measure.isProbabilityMeasure_map measurable_observationToEuclidean.aemeasurable
  have hm : Measurable (fun D : Dataset (Observation k m) r =>
      fun i : Fin r => observationToEuclidean (D i)) :=
    measurable_pi_lambda _ fun i => measurable_observationToEuclidean.comp (measurable_pi_apply i)
  have hmap := Measure.pi_map_pi (μ := fun _ : Fin r => μ)
    (f := fun _ : Fin r => observationToEuclidean)
    (fun _ => measurable_observationToEuclidean.aemeasurable)
  unfold euclideanProductLaw datasetLawOfObservation
  rw [← hmap, Measure.map_map continuous_productToEuclidean.measurable hm]
  congr 1
end LOOConcentration.Revision
