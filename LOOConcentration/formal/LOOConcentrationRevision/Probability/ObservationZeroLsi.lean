import LOOConcentrationRevision.Probability.ZeroLsiEndpoint
import LOOConcentrationRevision.Geometry.CoordinateTransport
import LOOConcentrationRevision.Frozen.Definitions.ObservationLogSobolevConstant

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory Filter
open scoped ENNReal

theorem exists_dirac_of_observationLogSobolevConstant_eq_zero {k m : ℕ}
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (hzero : observationLogSobolevConstant μ = 0) : ∃ z, μ = Measure.dirac z := by
  let := μ.isProbabilityMeasure_map measurable_observationToEuclidean.aemeasurable
  change logSobolevConstant (μ.map observationToEuclidean) = 0 at hzero
  obtain ⟨a, ha⟩ := exists_dirac_of_logSobolevConstant_eq_zero
    (μ.map observationToEuclidean) hzero
  have hmap := congrArg
    (fun ν : Measure (EuclideanSpace ℝ (ObservationCoordinate k m)) =>
      ν.map observationOfEuclidean) ha
  rw [Measure.map_map measurable_observationOfEuclidean
    measurable_observationToEuclidean, Measure.map_dirac' measurable_observationOfEuclidean a] at hmap
  have hinv : (observationOfEuclidean : EuclideanSpace ℝ (ObservationCoordinate k m) →
      Observation k m) ∘ observationToEuclidean = id := by
    funext z
    exact observationOfEuclidean_observationToEuclidean z
  rw [hinv, Measure.map_id] at hmap
  exact ⟨observationOfEuclidean a, hmap⟩

/-- The zero-constant endpoint on the exact observation carrier used by the
frozen concentration roots. All products and thresholds retain the same law. -/
theorem observation_zero_lsi_product_bias_endpoint {k m : ℕ} {κ : Type*} [Fintype κ]
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (hzero : observationLogSobolevConstant μ = 0)
    (H : (κ → Observation k m) → ℝ) (hH : Measurable H)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hmean : |∫ x, H x ∂Measure.pi fun _ : κ => μ| ≤ δ) :
    let ν := Measure.pi fun _ : κ => μ
    H =ᵐ[ν] (fun _ => ∫ x, H x ∂ν) ∧
      (∀ r : ℝ≥0∞, eLpNorm (fun x => H x - ∫ y, H y ∂ν) r ν = 0) ∧
      (∀ ε : ℝ, δ < ε → ν.real {x | ε < H x} = 0 ∧
        ν.real {x | ε < -H x} = 0) := by
  obtain ⟨a, ha⟩ := exists_dirac_of_observationLogSobolevConstant_eq_zero μ hzero
  subst μ
  exact product_dirac_bias_endpoint a H hH δ hδ hmean

end LOOConcentration.Revision
