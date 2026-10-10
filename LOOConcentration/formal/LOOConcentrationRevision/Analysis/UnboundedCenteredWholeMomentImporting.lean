import LOOConcentrationRevision.Analysis.UnboundedCenteredWholeMomentSource

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal

namespace LOOConcentration.Revision

/-- Typed deleted-product application: the observation product has exactly
`n + 1` factors, matching the `Qdeleted` cardinality in `looMoments`. -/
theorem unbounded_centered_deleted_observation_application
    {k m n : ℕ}
    (μ : Measure (LOOConcentration.Observation k m))
    [IsProbabilityMeasure μ]
    (hfinite : observationLogSobolevConstant μ < ⊤)
    (hM2 : Integrable LOOConcentration.observationNormSq μ)
    (F : EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (n + 1)) → ℝ)
    (hF : LocallyLipschitz F) (a b : NNReal)
    (hgrad : ∀ᵐ x ∂(volume : Measure
      (EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (n + 1)))),
      ‖gradient F x‖ ≤ (a : ℝ) + (b : ℝ) * ‖x‖)
    {p : ℝ} (hp : 2 ≤ p) :
    Integrable F (datasetLawOfObservation (r := n + 1) μ) ∧
      MemLp (fun x => F x -
        ∫ y, F y ∂datasetLawOfObservation (r := n + 1) μ)
        (ENNReal.ofReal p) (datasetLawOfObservation (r := n + 1) μ) ∧
      eLpNorm (fun x => F x -
        ∫ y, F y ∂datasetLawOfObservation (r := n + 1) μ)
        (ENNReal.ofReal p) (datasetLawOfObservation (r := n + 1) μ) ≤
        ENNReal.ofReal
          (Real.sqrt ((observationLogSobolevConstant μ).toReal * (p - 1)) *
            ((a : ℝ) + (b : ℝ) * Real.sqrt
              ((n + 1 : ℝ) *
                (∫ z, LOOConcentration.observationNormSq z ∂μ) +
                (observationLogSobolevConstant μ).toReal * (p - 2)))) := by
  simpa [Nat.cast_add] using
    (unbounded_centered_observation_product (r := n)
      μ hfinite hM2 F hF a b hgrad hp)

/-- Typed full-product application: the observation product has exactly
`n + 2` factors, matching the `Qfull` cardinality in `looMoments`. -/
theorem unbounded_centered_full_observation_application
    {k m n : ℕ}
    (μ : Measure (LOOConcentration.Observation k m))
    [IsProbabilityMeasure μ]
    (hfinite : observationLogSobolevConstant μ < ⊤)
    (hM2 : Integrable LOOConcentration.observationNormSq μ)
    (F : EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (n + 2)) → ℝ)
    (hF : LocallyLipschitz F) (a b : NNReal)
    (hgrad : ∀ᵐ x ∂(volume : Measure
      (EuclideanSpace ℝ (LOOConcentration.DatasetCoordinate k m (n + 2)))),
      ‖gradient F x‖ ≤ (a : ℝ) + (b : ℝ) * ‖x‖)
    {p : ℝ} (hp : 2 ≤ p) :
    Integrable F (datasetLawOfObservation (r := n + 2) μ) ∧
      MemLp (fun x => F x -
        ∫ y, F y ∂datasetLawOfObservation (r := n + 2) μ)
        (ENNReal.ofReal p) (datasetLawOfObservation (r := n + 2) μ) ∧
      eLpNorm (fun x => F x -
        ∫ y, F y ∂datasetLawOfObservation (r := n + 2) μ)
        (ENNReal.ofReal p) (datasetLawOfObservation (r := n + 2) μ) ≤
        ENNReal.ofReal
          (Real.sqrt ((observationLogSobolevConstant μ).toReal * (p - 1)) *
            ((a : ℝ) + (b : ℝ) * Real.sqrt
              ((n + 2 : ℝ) *
                (∫ z, LOOConcentration.observationNormSq z ∂μ) +
                (observationLogSobolevConstant μ).toReal * (p - 2)))) := by
  simpa [Nat.add_assoc, Nat.cast_add] using
    (unbounded_centered_observation_product (r := n + 1)
      μ hfinite hM2 F hF a b hgrad hp)

end LOOConcentration.Revision
