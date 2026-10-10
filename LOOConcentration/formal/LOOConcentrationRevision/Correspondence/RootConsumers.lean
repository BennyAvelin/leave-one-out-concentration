import LOOConcentrationRevision.Correspondence.SourceStanding
import LOOConcentrationRevision.Frozen.Results.MainConcentration
import LOOConcentrationRevision.Frozen.Results.LooMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LOOConcentration.Revision
open MeasureTheory Filter
open scoped Topology ENNReal

/-- Apply the actual frozen mainConcentration export from all literal manuscript
clauses. The same constructed standing witness determines the conditional risk. -/
theorem mainConcentration_of_manuscript_clauses {k m n : ℕ}
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1)) (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSource :
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
          c + d * ‖x‖)
    )
    (ε : ℝ) (hε : 3 * δ₃ (n + 2) < ε) :
    let h := (LOOConcentration.Correspondence.standingAssumption_iff_manuscript_clauses
      (n := n) μ T L δ₁ δ₂ δ₃ c d).mpr hSource
    let C := (observationLogSobolevConstant μ).toReal
    let M₂ := ∫ z, observationNormSq z ∂μ
    let H := fun D =>
      (looRiskL1 μ (T (n + 1)) L (h.stable.integrable_full n)) D -
        looEstimate (T n) L D
    let θ₁ := fun z => thetaRate C M₂ ENNReal.toReal_nonneg
      (integral_nonneg observationNormSq_nonneg) (n + 1) (by omega)
      (ε / 3) (by linarith [h.stable.delta₃_nonneg n])
      (δ₁ (n + 1) z) (δ₂ (n + 1) z)
      (h.stable.delta₁_nonneg n z) (h.stable.delta₂_nonneg n z)
    let θ₂ := thetaRate C M₂ ENNReal.toReal_nonneg
      (integral_nonneg observationNormSq_nonneg) (n + 2) (by omega)
      (ε / 3) (by linarith [h.stable.delta₃_nonneg n])
      (c / Real.sqrt (n + 2 : ℝ)) (d / (n + 2 : ℝ))
      (div_nonneg h.c_nonneg (Real.sqrt_nonneg _))
      (div_nonneg h.d_nonneg (by positivity))
    let θ₃ := thetaRate C M₂ ENNReal.toReal_nonneg
      (integral_nonneg observationNormSq_nonneg) (n + 2) (by omega)
      (ε / 3 - δ₃ (n + 2)) (by linarith)
      (∫ z, δ₁ (n + 2) z ∂μ) (∫ z, δ₂ (n + 2) z ∂μ)
      (integral_nonneg (h.stable.delta₁_nonneg (n + 1)))
      (integral_nonneg (h.stable.delta₂_nonneg (n + 1)))
    let Pplus := (Measure.pi fun _ : Fin (n + 2) => μ).real {D | H D > ε}
    let Pminus := (Measure.pi fun _ : Fin (n + 2) => μ).real {D | -H D > ε}
    (Pplus ≤ (n + 2 : ℝ) * (∫ z, θ₁ z ∂μ) + θ₂ + θ₃ ∧
     Pminus ≤ (n + 2 : ℝ) * (∫ z, θ₁ z ∂μ) + θ₂ + θ₃) ∧
    ∀ (a b : NNReal) (_hbound : ∀ᵐ z ∂μ,
      δ₁ (n + 1) z ≤ (a : ℝ) ∧ δ₂ (n + 1) z ≤ (b : ℝ)),
      let θuniform := thetaRate C M₂ ENNReal.toReal_nonneg
        (integral_nonneg observationNormSq_nonneg) (n + 1) (by omega)
        (ε / 3) (by linarith [h.stable.delta₃_nonneg n])
        a b a.property b.property
      Pplus ≤ θuniform + θ₂ + θ₃ ∧ Pminus ≤ θuniform + θ₂ + θ₃ := by
  exact mainConcentration μ T L δ₁ δ₂ δ₃ c d
    ((LOOConcentration.Correspondence.standingAssumption_iff_manuscript_clauses
      (n := n) μ T L δ₁ δ₂ δ₃ c d).mpr hSource) ε hε

/-- Apply the actual frozen looMoments export from all literal manuscript
clauses. The same constructed standing witness determines the conditional risk. -/
theorem looMoments_of_manuscript_clauses {k m n : ℕ}
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1)) (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSource :
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
          c + d * ‖x‖)
    )
    (p : ℝ) (_hp : 2 ≤ p)
    (_hδ₁ : MemLp (δ₁ (n + 1)) (ENNReal.ofReal p) μ)
    (_hδ₂ : MemLp (δ₂ (n + 1)) (ENNReal.ofReal p) μ) :
    let h := (LOOConcentration.Correspondence.standingAssumption_iff_manuscript_clauses
      (n := n) μ T L δ₁ δ₂ δ₃ c d).mpr hSource
    let ν := Measure.pi fun _ : Fin (n + 2) => μ
    let C := (observationLogSobolevConstant μ).toReal
    let M₂ := ∫ z, observationNormSq z ∂μ
    let Qdeleted := Real.sqrt ((n + 1 : ℝ) * M₂ + C * (p - 2))
    let Qfull := Real.sqrt ((n + 2 : ℝ) * M₂ + C * (p - 2))
    let B := Real.sqrt (C * (p - 1)) *
      ((eLpNorm (δ₁ (n + 1)) (ENNReal.ofReal p) μ).toReal +
       Qdeleted * (eLpNorm (δ₂ (n + 1)) (ENNReal.ofReal p) μ).toReal +
       c / Real.sqrt (n + 2 : ℝ) + d / (n + 2 : ℝ) * Qfull +
       (∫ z, δ₁ (n + 2) z ∂μ) + (∫ z, δ₂ (n + 2) z ∂μ) * Qfull)
    let H := fun D => (looRiskL1 μ (T (n + 1)) L (h.stable.integrable_full n)) D -
      looEstimate (T n) L D
    eLpNorm (fun D => H D - ∫ E, H E ∂ν) (ENNReal.ofReal p) ν ≤ ENNReal.ofReal B ∧
    eLpNorm H (ENNReal.ofReal p) ν ≤ ENNReal.ofReal (δ₃ (n + 2) + B) ∧
    (p = 2 → (∫ D, (H D - ∫ E, H E ∂ν) ^ 2 ∂ν) ≤ B ^ 2) := by
  exact looMoments μ T L δ₁ δ₂ δ₃ c d
    ((LOOConcentration.Correspondence.standingAssumption_iff_manuscript_clauses
      (n := n) μ T L δ₁ δ₂ δ₃ c d).mpr hSource) p _hp _hδ₁ _hδ₂

end LOOConcentration.Revision
