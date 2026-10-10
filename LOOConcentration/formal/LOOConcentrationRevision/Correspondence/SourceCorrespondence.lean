import LOOConcentrationRevision.Correspondence.SourceGradient
import LOOConcentrationRevision.Correspondence.CandidateDerivative
import LOOConcentrationRevision.Correspondence.JointDifferentiability
import LOOConcentrationRevision.Correspondence.ContinuousSectionCutoff

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LOOConcentration.Correspondence
open Filter MeasureTheory MeasureTheory.Measure
open scoped Topology ENNReal

/-- The manuscript's joint measurability and AE local Lipschitz hypotheses supply
AE differentiability in the original data-first order. No regularity of rates or
joint continuity is assumed. The cutoff is an internal proof object only. -/
theorem jointlyMeasurable_locallyLipschitz_ae_ae_differentiableAt
    {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    (F : EuclideanSpace ℝ ι × α → ℝ) (hF : Measurable F)
    (hLip : ∀ᵐ z ∂μ, LocallyLipschitz (fun x => F (x, z))) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ ι)), ∀ᵐ z ∂μ,
      DifferentiableAt ℝ (fun y => F (y, z)) x := by
  obtain ⟨Z, _hZm, hZfull, _hZvalid, hF0, hLip0, hCont0, hEq⟩ :=
    Revision.exists_measurable_full_sectionCutoff F hF hLip
  let F0 := Revision.sectionCutoff Z F
  have hMeas : MeasurableSet {p : EuclideanSpace ℝ ι × α |
      HasFDerivAt (fun y => F0 (y, p.2)) (candidateContinuousLinearMap F0 p) p.1} :=
    _root_.LOOConcentration.Correspondence.measurableSet_hasFDerivAt_with_param hF0 hCont0
      (candidateContinuousLinearMap F0) (measurable_candidateContinuousLinearMap F0 hF0)
  have hzFirst : ∀ᵐ z ∂μ, ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ ι)),
      HasFDerivAt (fun y => F0 (y, z)) (candidateContinuousLinearMap F0 (x, z)) x :=
    ae_of_all μ fun z => locallyLipschitz_section_ae_hasFDerivAt_candidate F0 z (hLip0 z)
  have hxFirst := (ae_ae_comm hMeas).mpr hzFirst
  filter_upwards [hxFirst] with x hx
  filter_upwards [hZfull, hx] with z hz hd
  simpa only [F0, hEq z hz] using hd.differentiableAt

/-- Full source-order characterization of the frozen stable gradient field.
Both sides use the same original function and the same arbitrary real rates. -/
theorem observation_first_gradient_iff_data_first_bound
    {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    (F : EuclideanSpace ℝ ι × α → ℝ) (hF : Measurable F)
    (a b : α → ℝ)
    (hLip : ∀ᵐ z ∂μ, LocallyLipschitz (fun x => F (x, z))) :
    (∀ᵐ z ∂μ, ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ ι)),
      DifferentiableAt ℝ (fun y => F (y, z)) x ∧
        ‖gradient (fun y => F (y, z)) x‖ ≤ a z + b z * ‖x‖) ↔
    (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ ι)), ∀ᵐ z ∂μ,
      ‖gradient (fun y => F (y, z)) x‖ ≤ a z + b z * ‖x‖) := by
  have hDiff := jointlyMeasurable_locallyLipschitz_ae_ae_differentiableAt μ F hF hLip
  constructor
  · intro h
    have hRep : ∀ᵐ z ∂μ, ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ ι)),
        partialGradientNormRepresentative F (x, z) ≤ a z + b z * ‖x‖ := by
      filter_upwards [h] with z hz
      exact nativeGradient_ae_bound_to_representative_ae_bound F
        (fun x => a z + b z * ‖x‖) z hz
    have hRep' := (_root_.LOOConcentration.Correspondence.ae_ae_exchange_real_rates
      (partialGradientNormRepresentative F) (fun x => ‖x‖) a b
      (measurable_partialGradientNormRepresentative F hF) measurable_norm norm_nonneg).mpr hRep
    filter_upwards [hRep', hDiff] with x hb hd
    filter_upwards [hb, hd] with z hb hd
    rw [← partialGradientNormRepresentative_eq_gradient_norm F x z hd]
    exact hb
  · intro h
    apply data_first_nativeGradient_to_observation_first μ F hF a b hLip
    filter_upwards [hDiff, h] with x hd hb
    filter_upwards [hd, hb] with z hd hb
    exact ⟨hd, hb⟩

/-- The exact frozen fitted-loss gradient field agrees with the literal data-first
manuscript bound under its joint measurable-loss and AE locally Lipschitz premises. -/
theorem stable_gradient_loss_iff_manuscript_bound {k m : ℕ}
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (r : ℕ)
    (hMeas : Measurable (fun p : Dataset (Observation k m) (r + 1) × Observation k m =>
      fittedLoss (T r) L p.1 p.2))
    (hLip : ∀ᵐ z ∂μ, LocallyLipschitz
      (fun x : EuclideanSpace ℝ (DatasetCoordinate k m (r + 1)) =>
        fittedLoss (T r) L (Revision.datasetOfEuclidean x) z)) :
    (∀ᵐ z ∂μ, ∀ᵐ x ∂(volume : Measure
        (EuclideanSpace ℝ (DatasetCoordinate k m (r + 1)))),
      let f := fun y => fittedLoss (T r) L (Revision.datasetOfEuclidean y) z
      DifferentiableAt ℝ f x ∧ ‖gradient f x‖ ≤
        δ₁ (r + 1) z + δ₂ (r + 1) z * ‖x‖) ↔
    (∀ᵐ x ∂(volume : Measure
        (EuclideanSpace ℝ (DatasetCoordinate k m (r + 1)))), ∀ᵐ z ∂μ,
      ‖gradient (fun y => fittedLoss (T r) L (Revision.datasetOfEuclidean y) z) x‖ ≤
        δ₁ (r + 1) z + δ₂ (r + 1) z * ‖x‖) := by
  exact observation_first_gradient_iff_data_first_bound μ
    (fun p => fittedLoss (T r) L (Revision.datasetOfEuclidean p.1) p.2)
    (hMeas.comp ((Revision.measurable_datasetOfEuclidean.comp measurable_fst).prodMk
      measurable_snd)) (δ₁ (r + 1)) (δ₂ (r + 1)) hLip

end LOOConcentration.Correspondence
