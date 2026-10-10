import LOOConcentrationRevision.Correspondence.SourceCorrespondence

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LOOConcentration.Correspondence
open Filter MeasureTheory
open scoped Topology ENNReal

/-- Complete literal-clause characterization of the frozen stability predicate,
with its gradient clause in the manuscript's original data-first order. All
other fields are exactly the frozen clauses; no extra proof premise is added. -/
theorem stable_iff_manuscript_clauses {k m : ℕ}
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (hlsi : Revision.observationLogSobolevConstant μ < ⊤)
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) :
    Revision.Stable μ hlsi T L δ₁ δ₂ δ₃ ↔
    (∀ r, Measurable
    (fun p : Dataset (Observation k m) (r + 1) × Observation k m =>
      fittedLoss (T r) L p.1 p.2)) ∧
    (∀ r z, 0 ≤ δ₁ (r + 1) z) ∧
    (∀ r z, 0 ≤ δ₂ (r + 1) z) ∧
    (∀ n, 0 ≤ δ₃ (n + 2)) ∧
    (∀ᵐ z ∂μ, Tendsto (fun r => δ₁ (r + 1) z) atTop (𝓝 0)) ∧
    (∀ᵐ z ∂μ, Tendsto (fun r => δ₂ (r + 1) z) atTop (𝓝 0)) ∧
    (Tendsto (fun n => δ₃ (n + 2)) atTop (𝓝 0)) ∧
    (∀ r, ∀ᵐ z ∂μ, LocallyLipschitz
    (fun x : EuclideanSpace ℝ (DatasetCoordinate k m (r + 1)) =>
      fittedLoss (T r) L (Revision.datasetOfEuclidean x) z)) ∧
    (∀ r, ∀ᵐ x ∂(volume :
      Measure (EuclideanSpace ℝ (DatasetCoordinate k m (r + 1)))), ∀ᵐ z ∂μ,
    ‖gradient (fun y => fittedLoss (T r) L (Revision.datasetOfEuclidean y) z) x‖ ≤
      δ₁ (r + 1) z + δ₂ (r + 1) z * ‖x‖) ∧
    (∀ n (i : Fin (n + 2)), Integrable
    (fun D : Dataset (Observation k m) (n + 2) =>
      fittedLoss (T n) L (deleteAt D i) (D i))
    (Measure.pi fun _ : Fin (n + 2) => μ)) ∧
    (∀ n, Integrable
    (fun p : Dataset (Observation k m) (n + 2) × Observation k m =>
      fittedLoss (T (n + 1)) L p.1 p.2)
    ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ)) ∧
    (∀ n (i : Fin (n + 2)),
    |(∫ D : Dataset (Observation k m) (n + 2),
      fittedLoss (T n) L (deleteAt D i) (D i)
        ∂Measure.pi fun _ : Fin (n + 2) => μ) -
      (∫ p : Dataset (Observation k m) (n + 2) × Observation k m,
        fittedLoss (T (n + 1)) L p.1 p.2
          ∂((Measure.pi fun _ : Fin (n + 2) => μ).prod μ))| ≤ δ₃ (n + 2)) := by
  constructor
  · intro h
    exact ⟨h.measurable_loss,
      h.delta₁_nonneg,
      h.delta₂_nonneg,
      h.delta₃_nonneg,
      h.delta₁_tendsto,
      h.delta₂_tendsto,
      h.delta₃_tendsto,
      h.locallyLipschitz_loss,
      fun r => (stable_gradient_loss_iff_manuscript_bound μ T L δ₁ δ₂ r
      (h.measurable_loss r) (h.locallyLipschitz_loss r)).mp (h.gradient_loss r),
      h.integrable_deleted,
      h.integrable_full,
      h.bias⟩
  · intro h
    rcases h with ⟨h_measurable_loss, h_delta₁_nonneg, h_delta₂_nonneg, h_delta₃_nonneg, h_delta₁_tendsto, h_delta₂_tendsto, h_delta₃_tendsto, h_locallyLipschitz_loss, h_gradient_loss, h_integrable_deleted, h_integrable_full, h_bias⟩
    refine {
      measurable_loss := h_measurable_loss
      delta₁_nonneg := h_delta₁_nonneg
      delta₂_nonneg := h_delta₂_nonneg
      delta₃_nonneg := h_delta₃_nonneg
      delta₁_tendsto := h_delta₁_tendsto
      delta₂_tendsto := h_delta₂_tendsto
      delta₃_tendsto := h_delta₃_tendsto
      locallyLipschitz_loss := h_locallyLipschitz_loss
      gradient_loss := fun r => (stable_gradient_loss_iff_manuscript_bound μ T L δ₁ δ₂ r
        (h_measurable_loss r) (h_locallyLipschitz_loss r)).mpr (h_gradient_loss r)
      integrable_deleted := h_integrable_deleted
      integrable_full := h_integrable_full
      bias := h_bias
    }

end LOOConcentration.Correspondence
