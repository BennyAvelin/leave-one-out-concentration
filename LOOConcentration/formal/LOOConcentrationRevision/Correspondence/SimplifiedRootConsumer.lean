import LOOConcentrationRevision.Correspondence.SourceStanding
import LOOConcentrationRevision.Frozen.Results.SimplifiedConcentration

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LOOConcentration.Revision
open MeasureTheory Filter
open scoped Topology ENNReal

/-- Consume the complete frozen simplified theorem, including its common
asymptotic witnesses, from the literal manuscript standing clauses. -/
theorem simplifiedConcentration_of_manuscript_clauses :
    (∀ (k m n : ℕ) (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
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
          c + d * ‖x‖)),
      let h := (LOOConcentration.Correspondence.standingAssumption_iff_manuscript_clauses
        (n := n) μ T L δ₁ δ₂ δ₃ c d).mpr hSource
      ∀
      (_hzero : ∀ z, δ₂ (n + 1) z = 0 ∧ δ₂ (n + 2) z = 0)
      (_hLip : ∀ z w,
        |meanFittedLoss μ (T n) L z (h.mean_integrable z) -
          meanFittedLoss μ (T n) L w (h.mean_integrable w)| ≤ c * observationNorm (z - w)),
      let C := (observationLogSobolevConstant μ).toReal
      let ν := Measure.pi fun _ : Fin (n + 2) => μ
      let H := fun D => (looRiskL1 μ (T (n + 1)) L (h.stable.integrable_full n)) D -
        looEstimate (T n) L D
      (∀ (ε : ℝ) (_hε : 3 * δ₃ (n + 2) < ε),
        let t := (ε - δ₃ (n + 2)) / 3
        let G := fun s : ℝ => if C * s ^ 2 = 0 then 0 else
          Real.exp (-(t ^ 2 / (2 * C * s ^ 2)))
        let rhs := (n + 2 : ℝ) * (∫ z, G (δ₁ (n + 1) z) ∂μ) +
          G (c / Real.sqrt (n + 2 : ℝ)) + G (∫ z, δ₁ (n + 2) z ∂μ)
        ν.real {D | H D > ε} ≤ rhs) ∧
      (∀ (a : NNReal) (_ha : ∀ᵐ z ∂μ, δ₁ (n + 1) z ≤ (a : ℝ))
        (t : ℝ) (_ht : 0 < t),
        let s := (a : ℝ) + c / Real.sqrt (n + 2 : ℝ) + ∫ z, δ₁ (n + 2) z ∂μ
        let G := if C * s ^ 2 = 0 then 0 else Real.exp (-(t ^ 2 / (2 * C * s ^ 2)))
        ν.real {D | |H D| > δ₃ (n + 2) + t} ≤ 2 * G ∧
        ν.real {D | H D > δ₃ (n + 2) + t} ≤ G ∧
        ν.real {D | -H D > δ₃ (n + 2) + t} ≤ G)) ∧
    (∀ (C A B : NNReal), ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ (k m : ℕ) (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
        (T : ∀ r : ℕ, Estimator k m (r + 1)) (L : Responses m → Responses m → ℝ)
        (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ c d : ℕ → ℝ)
        (_hC : (observationLogSobolevConstant μ).toReal = (C : ℝ))
        (hstandingSource : ∀ n,
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
      0 ≤ (c (n + 1)) ∧ 0 ≤ (d (n + 1)) ∧
      LocallyLipschitz (fun x : EuclideanSpace ℝ (ObservationCoordinate k m) =>
        Revision.meanFittedLoss μ (T n) L (Revision.observationOfEuclidean x)
          (hMean (Revision.observationOfEuclidean x))) ∧
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (ObservationCoordinate k m))),
        ‖gradient (fun y => Revision.meanFittedLoss μ (T n) L
          (Revision.observationOfEuclidean y) (hMean (Revision.observationOfEuclidean y))) x‖ ≤
          (c (n + 1)) + (d (n + 1)) * ‖x‖)),
        let hstanding := fun n =>
          (LOOConcentration.Correspondence.standingAssumption_iff_manuscript_clauses
            (n := n) μ T L δ₁ δ₂ δ₃ (c (n + 1)) (d (n + 1))).mpr (hstandingSource n)
        ∀
        (_hzero : ∀ n z, δ₂ (n + 1) z = 0 ∧ δ₂ (n + 2) z = 0)
        (_hLip : ∀ n z w,
          |meanFittedLoss μ (T n) L z ((hstanding n).mean_integrable z) -
            meanFittedLoss μ (T n) L w ((hstanding n).mean_integrable w)| ≤
            c (n + 1) * observationNorm (z - w))
        (_hc : ∀ n, c (n + 1) ≤ (B : ℝ))
        (_hδ₁ : ∀ n, ∀ᵐ z ∂μ,
          δ₁ (n + 1) z ≤ (A : ℝ) / Real.sqrt (n + 1 : ℝ) ∧
          δ₁ (n + 2) z ≤ (A : ℝ) / Real.sqrt (n + 2 : ℝ)),
        ∀ (ε : ℝ) (_hε : 0 < ε), ∃ nε : ℕ, ∀ n ≥ nε,
          let ν := Measure.pi fun _ : Fin (n + 2) => μ
          let H := fun D =>
            (looRiskL1 μ (T (n + 1)) L ((hstanding n).stable.integrable_full n)) D -
              looEstimate (T n) L D
          ν.real {D | H D > ε} ≤
            3 * (n + 2 : ℝ) * Real.exp (-(c₀ * ε ^ 2 * (n + 2 : ℝ)))) := by
  constructor
  · intro k m n μ _ T L δ₁ δ₂ δ₃ c d hSource
    dsimp only
    intro hzero hLip
    exact simplifiedConcentration.1 k m n μ T L δ₁ δ₂ δ₃ c d
      ((LOOConcentration.Correspondence.standingAssumption_iff_manuscript_clauses
        (n := n) μ T L δ₁ δ₂ δ₃ c d).mpr hSource) hzero hLip
  · intro C A B
    obtain ⟨c₀, hc₀, hTail⟩ := simplifiedConcentration.2 C A B
    refine ⟨c₀, hc₀, ?_⟩
    intro k m μ _ T L δ₁ δ₂ δ₃ c d hC hSource
    dsimp only
    intro hzero hLip hc hδ₁ ε hε
    exact hTail k m μ T L δ₁ δ₂ δ₃ c d hC
      (fun n => (LOOConcentration.Correspondence.standingAssumption_iff_manuscript_clauses
        (n := n) μ T L δ₁ δ₂ δ₃ (c (n + 1)) (d (n + 1))).mpr (hSource n))
      hzero hLip hc hδ₁ ε hε

end LOOConcentration.Revision
