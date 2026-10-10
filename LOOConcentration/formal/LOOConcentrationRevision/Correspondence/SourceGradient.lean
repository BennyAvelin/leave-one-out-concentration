import LOOConcentrationRevision.Correspondence.ParameterizedGradient
import LOOConcentrationRevision.Correspondence.AEExchange
import LOOConcentrationRevision.Geometry.CoordinateTransport
import LOOConcentrationRevision.Frozen.Definitions.Stable
import LOOConcentrationRevision.Frozen.Definitions.StandingAssumption

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LOOConcentration.Correspondence
open Filter MeasureTheory
open scoped Topology ENNReal

/-- Exchange the original data-first gradient assertion while preserving arbitrary rate
functions. The differentiability conjunct in this internal assertion will be derived
from source regularity by the measurable derivative-locus producer. -/
theorem data_first_nativeGradient_to_observation_first
    {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    (F : EuclideanSpace ℝ ι × α → ℝ) (hF : Measurable F)
    (a b : α → ℝ)
    (hLip : ∀ᵐ z ∂μ, LocallyLipschitz (fun x => F (x, z)))
    (hSource : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ ι)), ∀ᵐ z ∂μ,
      DifferentiableAt ℝ (fun y => F (y, z)) x ∧
        ‖gradient (fun y => F (y, z)) x‖ ≤ a z + b z * ‖x‖) :
    ∀ᵐ z ∂μ, ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ ι)),
      DifferentiableAt ℝ (fun y => F (y, z)) x ∧
        ‖gradient (fun y => F (y, z)) x‖ ≤ a z + b z * ‖x‖ := by
  have hRep : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ ι)), ∀ᵐ z ∂μ,
      partialGradientNormRepresentative F (x, z) ≤ a z + b z * ‖x‖ := by
    filter_upwards [hSource] with x hx
    filter_upwards [hx] with z hz
    rw [partialGradientNormRepresentative_eq_gradient_norm F x z hz.1]
    exact hz.2
  have hRep' := (_root_.LOOConcentration.Correspondence.ae_ae_exchange_real_rates
    (partialGradientNormRepresentative F) (fun x => ‖x‖) a b
    (measurable_partialGradientNormRepresentative F hF) measurable_norm norm_nonneg).mp hRep
  filter_upwards [hLip, hRep'] with z hz hb
  exact locallyLipschitz_section_ae_nativeGradient_bound F (fun x => a z + b z * ‖x‖) z hz hb

/-- Instantiate the exchange on the actual fitted loss and the exact coordinate map.
This ordinary helper has a source-order differentiability assertion as an internal
premise; it does not yet discharge the derivative-locus producer. -/
theorem data_first_fittedLoss_to_stable_gradient_loss {k m : ℕ}
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (r : ℕ)
    (hMeas : Measurable (fun p : Dataset (Observation k m) (r + 1) × Observation k m =>
      fittedLoss (T r) L p.1 p.2))
    (hLip : ∀ᵐ z ∂μ, LocallyLipschitz
      (fun x : EuclideanSpace ℝ (DatasetCoordinate k m (r + 1)) =>
        fittedLoss (T r) L (Revision.datasetOfEuclidean x) z))
    (hSource : ∀ᵐ x ∂(volume : Measure
        (EuclideanSpace ℝ (DatasetCoordinate k m (r + 1)))), ∀ᵐ z ∂μ,
      let f := fun y => fittedLoss (T r) L (Revision.datasetOfEuclidean y) z
      DifferentiableAt ℝ f x ∧ ‖gradient f x‖ ≤
        δ₁ (r + 1) z + δ₂ (r + 1) z * ‖x‖) :
    ∀ᵐ z ∂μ, ∀ᵐ x ∂(volume : Measure
        (EuclideanSpace ℝ (DatasetCoordinate k m (r + 1)))),
      let f := fun y => fittedLoss (T r) L (Revision.datasetOfEuclidean y) z
      DifferentiableAt ℝ f x ∧ ‖gradient f x‖ ≤
        δ₁ (r + 1) z + δ₂ (r + 1) z * ‖x‖ := by
  apply data_first_nativeGradient_to_observation_first μ
    (fun p => fittedLoss (T r) L (Revision.datasetOfEuclidean p.1) p.2)
    (hMeas.comp ((Revision.measurable_datasetOfEuclidean.comp measurable_fst).prodMk
      measurable_snd)) (δ₁ (r + 1)) (δ₂ (r + 1)) hLip hSource

/-- Local Lipschitz regularity supplies the differentiability conjunct in the
standing mean-gradient field, with the original constants unchanged. -/
theorem mean_gradient_iff_native_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : EuclideanSpace ℝ ι → ℝ) (hLip : LocallyLipschitz f) (c d : ℝ) :
    (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ ι)),
      DifferentiableAt ℝ f x ∧ ‖gradient f x‖ ≤ c + d * ‖x‖) ↔
    (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ ι)),
      ‖gradient f x‖ ≤ c + d * ‖x‖) := by
  constructor
  · intro h
    filter_upwards [h] with x hx
    exact hx.2
  · intro h
    filter_upwards [locallyLipschitz_ae_differentiableAt f hLip, h] with x hx hb
    exact ⟨hx, hb⟩

end LOOConcentration.Correspondence
