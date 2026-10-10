import LOOConcentration.Analysis.DatasetMeasureTransport
import LOOConcentrationRevision.Geometry.CoordinateTransport
import LOOConcentrationRevision.Frozen.Definitions.MeanFittedLoss
import LOOConcentrationRevision.Frozen.Definitions.StandingAssumption
import LOOConcentrationRevision.Probability.ProductSecondMoment
import LOOConcentrationRevision.Results.StandingLossDecomposition
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal

namespace LOOConcentration.Revision

/-- The source Euclidean dataset law is exactly the pushforward of the original
ordered observation product law along the frozen flattening map. -/
theorem datasetLawOfObservation_eq_measureMap_datasetToEuclidean
    {k m r : ℕ} (μ : Measure (Observation k m)) :
    datasetLawOfObservation (r := r) μ =
      Measure.map (datasetToEuclidean : Dataset (Observation k m) r →
        EuclideanSpace ℝ (DatasetCoordinate k m r))
        (Measure.pi fun _ : Fin r => μ) := by
  rfl

/-- `eLpNorm` is preserved when a dataset function is pulled back by the
frozen inverse coordinates. This holds for every exponent, including `0` and
`∞`; hence in particular it covers all source exponents `p ≥ 2`. -/
theorem eLpNorm_datasetFunction_datasetLaw_eq
    {k m r : ℕ} (μ : Measure (Observation k m))
    (F : Dataset (Observation k m) r → ℝ) (q : ℝ≥0∞) :
    eLpNorm (fun x : EuclideanSpace ℝ (DatasetCoordinate k m r) =>
      F (datasetOfEuclidean x)) q (datasetLawOfObservation (r := r) μ) =
    eLpNorm F q (Measure.pi fun _ : Fin r => μ) := by
  have hme : MeasurableEmbedding
      (datasetToEuclidean : Dataset (Observation k m) r →
        EuclideanSpace ℝ (DatasetCoordinate k m r)) :=
    (datasetEuclideanMeasurableEquiv (k := k) (m := m) (n := r)).measurableEmbedding
  change eLpNorm (fun x : EuclideanSpace ℝ (DatasetCoordinate k m r) =>
      F (datasetOfEuclidean x)) q
      (Measure.map datasetToEuclidean (Measure.pi fun _ : Fin r => μ)) = _
  simpa only [Function.comp_def, datasetOfEuclidean_datasetToEuclidean] using
    (hme.eLpNorm_map_measure
      (μ := Measure.pi fun _ : Fin r => μ) (p := q)
      (g := fun x : EuclideanSpace ℝ (DatasetCoordinate k m r) =>
        F (datasetOfEuclidean x)))

/-- The source `MemLp` condition and its Euclidean representation are
interchangeable under the same frozen dataset equivalence. -/
theorem memLp_datasetFunction_datasetLaw_iff
    {k m r : ℕ} (μ : Measure (Observation k m))
    (F : Dataset (Observation k m) r → ℝ) (q : ℝ≥0∞) :
    MemLp (fun x : EuclideanSpace ℝ (DatasetCoordinate k m r) =>
      F (datasetOfEuclidean x)) q (datasetLawOfObservation (r := r) μ) ↔
    MemLp F q (Measure.pi fun _ : Fin r => μ) := by
  have hme : MeasurableEmbedding
      (datasetToEuclidean : Dataset (Observation k m) r →
        EuclideanSpace ℝ (DatasetCoordinate k m r)) :=
    (datasetEuclideanMeasurableEquiv (k := k) (m := m) (n := r)).measurableEmbedding
  change MemLp (fun x : EuclideanSpace ℝ (DatasetCoordinate k m r) =>
      F (datasetOfEuclidean x)) q
      (Measure.map datasetToEuclidean (Measure.pi fun _ : Fin r => μ)) ↔ _
  simpa only [Function.comp_def, datasetOfEuclidean_datasetToEuclidean] using
    (hme.memLp_map_measure_iff
      (μ := Measure.pi fun _ : Fin r => μ)
      (g := fun x : EuclideanSpace ℝ (DatasetCoordinate k m r) =>
        F (datasetOfEuclidean x)) (p := q))

/-- Integrability of an actual frozen-carrier function is equivalent to
integrability of its Euclidean expression. -/
theorem integrable_datasetFunction_datasetLaw_iff
    {k m r : ℕ} (μ : Measure (Observation k m))
    (F : Dataset (Observation k m) r → ℝ) :
    Integrable (fun x : EuclideanSpace ℝ (DatasetCoordinate k m r) =>
      F (datasetOfEuclidean x)) (datasetLawOfObservation (r := r) μ) ↔
    Integrable F (Measure.pi fun _ : Fin r => μ) := by
  have hme : MeasurableEmbedding
      (datasetToEuclidean : Dataset (Observation k m) r →
        EuclideanSpace ℝ (DatasetCoordinate k m r)) :=
    (datasetEuclideanMeasurableEquiv (k := k) (m := m) (n := r)).measurableEmbedding
  change Integrable (fun x : EuclideanSpace ℝ (DatasetCoordinate k m r) =>
      F (datasetOfEuclidean x))
      (Measure.map datasetToEuclidean (Measure.pi fun _ : Fin r => μ)) ↔ _
  simpa only [Function.comp_def, datasetOfEuclidean_datasetToEuclidean] using
    (hme.integrable_map_iff
      (μ := Measure.pi fun _ : Fin r => μ)
      (g := fun x : EuclideanSpace ℝ (DatasetCoordinate k m r) =>
        F (datasetOfEuclidean x)))

/-- Integrals of the Euclidean expression equal the same source function's
integral on `Measure.pi`; integrability is the only analytic premise. -/
theorem integral_datasetFunction_datasetLaw_eq
    {k m r : ℕ} (μ : Measure (Observation k m))
    (F : Dataset (Observation k m) r → ℝ)
    (hF : Integrable F (Measure.pi fun _ : Fin r => μ)) :
    (∫ x : EuclideanSpace ℝ (DatasetCoordinate k m r),
      F (datasetOfEuclidean x) ∂datasetLawOfObservation (r := r) μ) =
    ∫ D : Dataset (Observation k m) r, F D ∂Measure.pi fun _ : Fin r => μ := by
  let Fflat : EuclideanSpace ℝ (DatasetCoordinate k m r) → ℝ :=
    fun x => F (datasetOfEuclidean x)
  have hFE : Integrable Fflat (datasetLawOfObservation (r := r) μ) := by
    simpa only [Fflat] using
      (integrable_datasetFunction_datasetLaw_iff μ F).2 hF
  change Integrable Fflat
    (Measure.map datasetToEuclidean (Measure.pi fun _ : Fin r => μ)) at hFE
  change (∫ x : EuclideanSpace ℝ (DatasetCoordinate k m r),
      Fflat x ∂Measure.map datasetToEuclidean (Measure.pi fun _ : Fin r => μ)) = _
  calc
    _ = ∫ D : Dataset (Observation k m) r,
        Fflat (datasetToEuclidean D) ∂Measure.pi fun _ : Fin r => μ :=
      integral_map measurable_datasetToEuclidean.aemeasurable hFE.aestronglyMeasurable
    _ = ∫ D : Dataset (Observation k m) r, F D ∂Measure.pi fun _ : Fin r => μ := by
      apply integral_congr_ae
      filter_upwards with D
      simp only [Fflat, datasetOfEuclidean_datasetToEuclidean]

/-- Exact centering and `eLpNorm` commute with the source-to-Euclidean dataset
transport whenever the original source function is integrable. -/
theorem centered_eLpNorm_datasetFunction_datasetLaw_eq
    {k m r : ℕ} (μ : Measure (Observation k m))
    (F : Dataset (Observation k m) r → ℝ)
    (hF : Integrable F (Measure.pi fun _ : Fin r => μ)) (q : ℝ≥0∞) :
    eLpNorm (fun x : EuclideanSpace ℝ (DatasetCoordinate k m r) =>
      F (datasetOfEuclidean x) -
        ∫ y : EuclideanSpace ℝ (DatasetCoordinate k m r),
          F (datasetOfEuclidean y) ∂datasetLawOfObservation (r := r) μ)
      q (datasetLawOfObservation (r := r) μ) =
    eLpNorm (fun D : Dataset (Observation k m) r =>
      F D - ∫ E : Dataset (Observation k m) r,
        F E ∂Measure.pi fun _ : Fin r => μ)
      q (Measure.pi fun _ : Fin r => μ) := by
  have hcenter := integral_datasetFunction_datasetLaw_eq μ F hF
  rw [hcenter]
  exact eLpNorm_datasetFunction_datasetLaw_eq μ
    (fun D : Dataset (Observation k m) r =>
      F D - ∫ E : Dataset (Observation k m) r, F E ∂Measure.pi fun _ : Fin r => μ) q

/-- The deleted-fit actual source mean is exactly the Euclidean-law mean of the
same fitted-loss section, with no extra proof-step premise beyond `hSt`. -/
theorem deleted_fittedLoss_mean_transport
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)
    (z : Observation k m) :
    (∫ x : EuclideanSpace ℝ (DatasetCoordinate k m (n + 1)),
      fittedLoss (T n) L (datasetOfEuclidean x) z
        ∂datasetLawOfObservation (r := n + 1) μ) =
      meanFittedLoss μ (T n) L z (hSt.mean_integrable z) := by
  rw [meanFittedLoss]
  exact integral_datasetFunction_datasetLaw_eq μ
    (fun D : Dataset (Observation k m) (n + 1) => fittedLoss (T n) L D z)
    (hSt.mean_integrable z)

/-- The centered deleted fitted-loss `eLpNorm` under the original observation
product is exactly its Euclidean `datasetLawOfObservation` counterpart. -/
theorem deleted_fittedLoss_centered_eLpNorm_transport
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)
    (z : Observation k m) (q : ℝ≥0∞) :
    eLpNorm (fun x : EuclideanSpace ℝ (DatasetCoordinate k m (n + 1)) =>
      fittedLoss (T n) L (datasetOfEuclidean x) z -
        meanFittedLoss μ (T n) L z (hSt.mean_integrable z)) q
      (datasetLawOfObservation (r := n + 1) μ) =
    eLpNorm (fun D : Dataset (Observation k m) (n + 1) =>
      fittedLoss (T n) L D z -
        meanFittedLoss μ (T n) L z (hSt.mean_integrable z)) q
      (Measure.pi fun _ : Fin (n + 1) => μ) := by
  have hF : Integrable
      (fun D : Dataset (Observation k m) (n + 1) => fittedLoss (T n) L D z)
      (Measure.pi fun _ : Fin (n + 1) => μ) := hSt.mean_integrable z
  have htransport := centered_eLpNorm_datasetFunction_datasetLaw_eq μ
    (fun D : Dataset (Observation k m) (n + 1) => fittedLoss (T n) L D z) hF q
  rw [deleted_fittedLoss_mean_transport μ T L δ₁ δ₂ δ₃ c d hSt z]
    at htransport
  simpa only [meanFittedLoss] using htransport

/-- Integrability of all three actual source-error terms follows internally
from the accepted standing loss-integrability result. -/
theorem standingThreeErrors_integrable
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d) :
    Integrable (standingI1 μ T L δ₁ δ₂ δ₃ c d hSt)
      (Measure.pi fun _ : Fin (n + 2) => μ) ∧
    Integrable (standingI2 μ T L δ₁ δ₂ δ₃ c d hSt)
      (Measure.pi fun _ : Fin (n + 2) => μ) ∧
    Integrable (standingI3 μ T L δ₁ δ₂ δ₃ c d hSt)
      (Measure.pi fun _ : Fin (n + 2) => μ) := by
  have hparts := standingLoss_integrability μ T L δ₁ δ₂ δ₃ c d hSt
  constructor
  · change Integrable
      (standingV μ T L δ₁ δ₂ δ₃ c d hSt - looEstimate (T n) L)
      (Measure.pi fun _ : Fin (n + 2) => μ)
    exact hparts.2.1.sub hparts.2.2.1
  constructor
  · change Integrable
      (fun _ : Dataset (Observation k m) (n + 2) =>
        standingEV μ T L δ₁ δ₂ δ₃ c d hSt -
          standingV μ T L δ₁ δ₂ δ₃ c d hSt _)
      (Measure.pi fun _ : Fin (n + 2) => μ)
    exact (integrable_const _).sub hparts.2.1
  · change Integrable
      (fun D : Dataset (Observation k m) (n + 2) =>
        standingRisk μ T L δ₁ δ₂ δ₃ c d hSt D -
          standingER μ T L δ₁ δ₂ δ₃ c d hSt)
      (Measure.pi fun _ : Fin (n + 2) => μ)
    exact hparts.1.sub (integrable_const _)

/-- The actual full-sample risk error has the same centered Euclidean and
original-product `eLpNorm`. -/
theorem standingH_centered_eLpNorm_transport
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)
    (q : ℝ≥0∞) :
    eLpNorm (fun x : EuclideanSpace ℝ (DatasetCoordinate k m (n + 2)) =>
      standingH μ T L δ₁ δ₂ δ₃ c d hSt (datasetOfEuclidean x) -
        ∫ y : EuclideanSpace ℝ (DatasetCoordinate k m (n + 2)),
          standingH μ T L δ₁ δ₂ δ₃ c d hSt (datasetOfEuclidean y)
            ∂datasetLawOfObservation (r := n + 2) μ)
      q (datasetLawOfObservation (r := n + 2) μ) =
    eLpNorm (fun D : Dataset (Observation k m) (n + 2) =>
      standingH μ T L δ₁ δ₂ δ₃ c d hSt D -
        ∫ E : Dataset (Observation k m) (n + 2),
          standingH μ T L δ₁ δ₂ δ₃ c d hSt E
            ∂Measure.pi fun _ : Fin (n + 2) => μ)
      q (Measure.pi fun _ : Fin (n + 2) => μ) := by
  have hparts := standingLoss_integrability μ T L δ₁ δ₂ δ₃ c d hSt
  exact centered_eLpNorm_datasetFunction_datasetLaw_eq μ
    (standingH μ T L δ₁ δ₂ δ₃ c d hSt) hparts.2.2.2 q

/-- The three actual source-error terms, centered under their original
`Measure.pi` law, have exactly their Euclidean counterparts' `eLpNorm`. -/
theorem standingThreeErrors_centered_eLpNorm_transport
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)
    (q : ℝ≥0∞) :
    eLpNorm (fun x : EuclideanSpace ℝ (DatasetCoordinate k m (n + 2)) =>
      standingI1 μ T L δ₁ δ₂ δ₃ c d hSt (datasetOfEuclidean x) -
        ∫ y, standingI1 μ T L δ₁ δ₂ δ₃ c d hSt (datasetOfEuclidean y)
          ∂datasetLawOfObservation (r := n + 2) μ) q
        (datasetLawOfObservation (r := n + 2) μ) =
    eLpNorm (fun D : Dataset (Observation k m) (n + 2) =>
      standingI1 μ T L δ₁ δ₂ δ₃ c d hSt D -
        ∫ E, standingI1 μ T L δ₁ δ₂ δ₃ c d hSt E
          ∂Measure.pi fun _ : Fin (n + 2) => μ) q
        (Measure.pi fun _ : Fin (n + 2) => μ) ∧
    eLpNorm (fun x : EuclideanSpace ℝ (DatasetCoordinate k m (n + 2)) =>
      standingI2 μ T L δ₁ δ₂ δ₃ c d hSt (datasetOfEuclidean x) -
        ∫ y, standingI2 μ T L δ₁ δ₂ δ₃ c d hSt (datasetOfEuclidean y)
          ∂datasetLawOfObservation (r := n + 2) μ) q
        (datasetLawOfObservation (r := n + 2) μ) =
    eLpNorm (fun D : Dataset (Observation k m) (n + 2) =>
      standingI2 μ T L δ₁ δ₂ δ₃ c d hSt D -
        ∫ E, standingI2 μ T L δ₁ δ₂ δ₃ c d hSt E
          ∂Measure.pi fun _ : Fin (n + 2) => μ) q
        (Measure.pi fun _ : Fin (n + 2) => μ) ∧
    eLpNorm (fun x : EuclideanSpace ℝ (DatasetCoordinate k m (n + 2)) =>
      standingI3 μ T L δ₁ δ₂ δ₃ c d hSt (datasetOfEuclidean x) -
        ∫ y, standingI3 μ T L δ₁ δ₂ δ₃ c d hSt (datasetOfEuclidean y)
          ∂datasetLawOfObservation (r := n + 2) μ) q
        (datasetLawOfObservation (r := n + 2) μ) =
    eLpNorm (fun D : Dataset (Observation k m) (n + 2) =>
      standingI3 μ T L δ₁ δ₂ δ₃ c d hSt D -
        ∫ E, standingI3 μ T L δ₁ δ₂ δ₃ c d hSt E
          ∂Measure.pi fun _ : Fin (n + 2) => μ) q
        (Measure.pi fun _ : Fin (n + 2) => μ) := by
  have hi := standingThreeErrors_integrable μ T L δ₁ δ₂ δ₃ c d hSt
  exact ⟨centered_eLpNorm_datasetFunction_datasetLaw_eq μ _ hi.1 q,
    centered_eLpNorm_datasetFunction_datasetLaw_eq μ _ hi.2.1 q,
    centered_eLpNorm_datasetFunction_datasetLaw_eq μ _ hi.2.2 q⟩

#print axioms LOOConcentration.Revision.datasetLawOfObservation_eq_measureMap_datasetToEuclidean
#print axioms LOOConcentration.Revision.centered_eLpNorm_datasetFunction_datasetLaw_eq
#print axioms LOOConcentration.Revision.deleted_fittedLoss_centered_eLpNorm_transport
#print axioms LOOConcentration.Revision.standingThreeErrors_centered_eLpNorm_transport

end LOOConcentration.Revision
