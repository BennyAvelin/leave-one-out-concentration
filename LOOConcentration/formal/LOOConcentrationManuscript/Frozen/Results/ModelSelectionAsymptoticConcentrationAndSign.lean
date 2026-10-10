import LOOConcentrationManuscript.Internal.ModelSelectionSignedAsymptoticUniformConstant

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript
open MeasureTheory Filter
open LOOConcentration.Revision LOOConcentration.Manuscript.Internal
open scoped Gradient Topology ENNReal

theorem modelSelection_asymptotic_concentration_and_sign
    (C A B : NNReal) :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ {k m : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ],
        observationLogSobolevConstant μ = (C : ENNReal) →
        Integrable observationNormSq μ →
      ∀ (T₀ T₁ : ∀ r : ℕ, Estimator k m (r + 1))
        (L : Responses m → Responses m → ℝ)
        (δ₁ δ₂ : ℕ → Observation k m → ℝ) (c δ₃ : ℕ → ℝ),
        (hSignedMeas : ∀ n, Measurable
          (fun p : Dataset (Observation k m) (n + 2) × Observation k m =>
            fittedLoss (T₀ (n + 1)) L p.1 p.2 -
              fittedLoss (T₁ (n + 1)) L p.1 p.2)) →
        (hδ₁_nonneg : ∀ N z, 0 ≤ δ₁ (N + 1) z) →
        (hδ₂_nonneg : ∀ N z, 0 ≤ δ₂ (N + 1) z) →
        (hδ₁_int : ∀ N, Integrable (fun z => δ₁ (N + 1) z) μ) →
        (hδ₂_int : ∀ N, Integrable (fun z => δ₂ (N + 1) z) μ) →
        (hzero : ∀ n, Integrable (fun z =>
          fittedLoss (T₀ (n + 1)) L (0 : Dataset (Observation k m) (n + 2)) z -
            fittedLoss (T₁ (n + 1)) L (0 : Dataset (Observation k m) (n + 2)) z) μ) →
        (hFullLoc : ∀ n, ∀ᵐ z ∂μ, LocallyLipschitz (fun x : EuclideanSpace ℝ
          (DatasetCoordinate k m (n + 2)) =>
            fittedLoss (T₀ (n + 1)) L (Revision.datasetOfEuclidean x) z -
              fittedLoss (T₁ (n + 1)) L (Revision.datasetOfEuclidean x) z)) →
        (hFullGrad : ∀ n, ∀ᵐ z ∂μ, ∀ᵐ x ∂(volume : Measure
          (EuclideanSpace ℝ (DatasetCoordinate k m (n + 2)))),
          DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (DatasetCoordinate k m (n + 2)) =>
            fittedLoss (T₀ (n + 1)) L (Revision.datasetOfEuclidean y) z -
              fittedLoss (T₁ (n + 1)) L (Revision.datasetOfEuclidean y) z) x ∧
          ‖gradient (fun y : EuclideanSpace ℝ (DatasetCoordinate k m (n + 2)) =>
            fittedLoss (T₀ (n + 1)) L (Revision.datasetOfEuclidean y) z -
              fittedLoss (T₁ (n + 1)) L (Revision.datasetOfEuclidean y) z) x‖ ≤
            δ₁ (n + 2) z + δ₂ (n + 2) z * ‖x‖) →
        (hf₀ : ∀ n, Integrable
          (fun p : Dataset (Observation k m) (n + 2) × Observation k m =>
            fittedLoss (T₀ (n + 1)) L p.1 p.2)
          ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ)) →
        (hf₁ : ∀ n, Integrable
          (fun p : Dataset (Observation k m) (n + 2) × Observation k m =>
            fittedLoss (T₁ (n + 1)) L p.1 p.2)
          ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ)) →
        (hShortMeas : ∀ n, Measurable
          (fun p : Dataset (Observation k m) (n + 1) × Observation k m =>
            fittedLoss (T₀ n) L p.1 p.2 - fittedLoss (T₁ n) L p.1 p.2)) →
        (hShortLoc : ∀ n, ∀ᵐ z ∂μ, LocallyLipschitz (fun x : EuclideanSpace ℝ
          (DatasetCoordinate k m (n + 1)) =>
            fittedLoss (T₀ n) L (datasetOfEuclidean x) z -
              fittedLoss (T₁ n) L (datasetOfEuclidean x) z)) →
        (hShortGrad : ∀ n, ∀ᵐ z ∂μ, ∀ᵐ x ∂(volume : Measure
          (EuclideanSpace ℝ (DatasetCoordinate k m (n + 1)))),
          DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (DatasetCoordinate k m (n + 1)) =>
            fittedLoss (T₀ n) L (datasetOfEuclidean y) z -
              fittedLoss (T₁ n) L (datasetOfEuclidean y) z) x ∧
          ‖gradient (fun y : EuclideanSpace ℝ (DatasetCoordinate k m (n + 1)) =>
            fittedLoss (T₀ n) L (datasetOfEuclidean y) z -
              fittedLoss (T₁ n) L (datasetOfEuclidean y) z) x‖ ≤
            δ₁ (n + 1) z + δ₂ (n + 1) z * ‖x‖) →
        (hHeld : ∀ (n : ℕ) (i : Fin (n + 2)), Integrable
          (fun D : Dataset (Observation k m) (n + 2) =>
            fittedLoss (T₀ n) L (deleteAt D i) (D i) -
              fittedLoss (T₁ n) L (deleteAt D i) (D i))
          (Measure.pi fun _ : Fin (n + 2) => μ)) →
        (hBias : ∀ (n : ℕ) (i : Fin (n + 2)),
          |(∫ D : Dataset (Observation k m) (n + 2),
              fittedLoss (T₀ n) L (deleteAt D i) (D i) -
                fittedLoss (T₁ n) L (deleteAt D i) (D i)
              ∂Measure.pi fun _ : Fin (n + 2) => μ) -
            (∫ p : Dataset (Observation k m) (n + 2) × Observation k m,
              fittedLoss (T₀ (n + 1)) L p.1 p.2 -
                fittedLoss (T₁ (n + 1)) L p.1 p.2
                ∂(Measure.pi fun _ : Fin (n + 2) => μ).prod μ)| ≤ δ₃ (n + 2)) →
        (hQueryInt : ∀ (n : ℕ) (z : Observation k m), Integrable
          (fun D : Dataset (Observation k m) (n + 1) =>
            fittedLoss (T₀ n) L D z - fittedLoss (T₁ n) L D z)
          (Measure.pi fun _ : Fin (n + 1) => μ)) →
        (hc_nonneg : ∀ n, 0 ≤ c (n + 1)) →
        (hc_bound : ∀ n, c (n + 1) ≤ (B : ℝ)) →
        (hQueryLip : ∀ n, LipschitzWith
          (NNReal.mk (c (n + 1)) (hc_nonneg n))
          (modelSelectionSignedExpectedMeanQuery μ T₀ T₁ L (hQueryInt n))) →
        (hδ₂_zero : ∀ N z, δ₂ (N + 1) z = 0) →
        (hδ₁_short_rate : ∀ n, ∀ᵐ z ∂μ,
          δ₁ (n + 1) z ≤ (A : ℝ) / Real.sqrt (n + 1 : ℝ)) →
        (hδ₁_full_rate : ∀ n, ∀ᵐ z ∂μ,
          δ₁ (n + 2) z ≤ (A : ℝ) / Real.sqrt (n + 2 : ℝ)) →
        (hδ₃_nonneg : ∀ n, 0 ≤ δ₃ (n + 2)) →
        (hδ₃_tendsto : Tendsto (fun n => δ₃ (n + 2)) atTop (nhds 0)) →
        ∀ ε : ℝ, 0 < ε → ∃ nε : ℕ, ∀ n ≥ nε,
          let P : Measure (Dataset (Observation k m) (n + 2)) :=
            Measure.pi fun _ : Fin (n + 2) => μ
          let R : Dataset (Observation k m) (n + 2) → ℝ := fun D =>
            Revision.looRiskL1 μ (T₀ (n + 1)) L (hf₀ n) D -
              Revision.looRiskL1 μ (T₁ (n + 1)) L (hf₁ n) D
          let E : Dataset (Observation k m) (n + 2) → ℝ := fun D =>
            looEstimate (T₀ n) L D - looEstimate (T₁ n) L D
          ((P.real {D | R D - E D > ε} ≤
              3 * (n + 2 : ℝ) * Real.exp (-(c₀ * ε ^ 2 * (n + 2 : ℝ))) ∧
            P.real {D | E D - R D > ε} ≤
              3 * (n + 2 : ℝ) * Real.exp (-(c₀ * ε ^ 2 * (n + 2 : ℝ)))) ∧
            P.real {D | |R D - E D| > ε} ≤
              6 * (n + 2 : ℝ) * Real.exp (-(c₀ * ε ^ 2 * (n + 2 : ℝ)))) ∧
          P.real {D | ε < |R D| ∧ E D * R D ≤ 0} ≤
            6 * (n + 2 : ℝ) * Real.exp (-(c₀ * ε ^ 2 * (n + 2 : ℝ))) := by
  exact @LOOConcentration.Manuscript.Internal.modelSelection_signed_actual_asymptotic_probability_uniform_scalar
    C A B

end LOOConcentration.Manuscript
