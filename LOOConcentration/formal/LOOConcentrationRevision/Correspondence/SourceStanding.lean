import LOOConcentrationRevision.Correspondence.SourceStable

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LOOConcentration.Correspondence
open Filter MeasureTheory
open scoped Topology ENNReal

/-- Literal standing-assumption clauses, with the extra differentiability
conjunct in the mean-gradient field supplied by its locally Lipschitz premise.
The literal source stability clauses are expanded by `stable_iff_manuscript_clauses`.
The same pointwise mean-integrability witness is used in both mean clauses. -/
theorem standingAssumption_iff_manuscript_clauses {k m n : ℕ}
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ) :
    Revision.StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d ↔
    ∃ (_hlsi : Revision.observationLogSobolevConstant μ < ⊤)
      (hMean : ∀ z, Integrable
        (fun D : Dataset (Observation k m) (n + 1) => fittedLoss (T n) L D z)
        (Measure.pi fun _ : Fin (n + 1) => μ)),
      Integrable observationNormSq μ ∧
      (
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
          ∂((Measure.pi fun _ : Fin (n + 2) => μ).prod μ))| ≤ δ₃ (n + 2))
      ) ∧
      Integrable (δ₁ (n + 1)) μ ∧ Integrable (δ₂ (n + 1)) μ ∧
      Integrable (δ₁ (n + 2)) μ ∧ Integrable (δ₂ (n + 2)) μ ∧
      Integrable (fun z => fittedLoss (T n) L 0 z) μ ∧
      Integrable (fun z => fittedLoss (T (n + 1)) L 0 z) μ ∧
      0 ≤ c ∧ 0 ≤ d ∧
      LocallyLipschitz (fun x : EuclideanSpace ℝ (ObservationCoordinate k m) =>
        Revision.meanFittedLoss μ (T n) L (Revision.observationOfEuclidean x)
          (hMean (Revision.observationOfEuclidean x))) ∧
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (ObservationCoordinate k m))),
        ‖gradient (fun y => Revision.meanFittedLoss μ (T n) L
          (Revision.observationOfEuclidean y) (hMean (Revision.observationOfEuclidean y))) x‖ ≤
          c + d * ‖x‖) := by
  constructor
  · intro h
    exact ⟨h.lsi, h.mean_integrable, h.second_moment,
      (stable_iff_manuscript_clauses μ h.lsi T L δ₁ δ₂ δ₃).mp h.stable,
      h.delta₁_deleted_integrable, h.delta₂_deleted_integrable,
      h.delta₁_full_integrable, h.delta₂_full_integrable,
      h.zero_deleted_integrable, h.zero_full_integrable, h.c_nonneg, h.d_nonneg,
      h.mean_locallyLipschitz,
      (mean_gradient_iff_native_bound _ h.mean_locallyLipschitz c d).mp h.mean_gradient⟩
  · rintro ⟨hlsi, hMean, hSecond, hStable, hD1Del, hD2Del, hD1Full, hD2Full,
      hZeroDel, hZeroFull, hc, hd, hMeanLip, hMeanGrad⟩
    exact {
      lsi := hlsi
      second_moment := hSecond
      stable := (stable_iff_manuscript_clauses μ hlsi T L δ₁ δ₂ δ₃).mpr hStable
      delta₁_deleted_integrable := hD1Del
      delta₂_deleted_integrable := hD2Del
      delta₁_full_integrable := hD1Full
      delta₂_full_integrable := hD2Full
      zero_deleted_integrable := hZeroDel
      zero_full_integrable := hZeroFull
      c_nonneg := hc
      d_nonneg := hd
      mean_integrable := hMean
      mean_locallyLipschitz := hMeanLip
      mean_gradient := (mean_gradient_iff_native_bound _ hMeanLip c d).mpr hMeanGrad
    }

end LOOConcentration.Correspondence
