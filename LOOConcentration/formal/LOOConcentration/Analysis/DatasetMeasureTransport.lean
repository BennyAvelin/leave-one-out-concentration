import LOOConcentration.Analysis.MollifierFatouBridge
import LOOConcentration.Concentration.SegmentIntegrability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Product-law transport to flattened dataset coordinates

The frozen ordered dataset and its flattened Euclidean coordinate space are
measurably equivalent. Pushing the ordered product law forward along this
equivalence preserves Bochner integrals, integrability, nonnegative
lintegrals, events, and the frozen norm normalization.
-/

set_option autoImplicit false

open Filter MeasureTheory
open scoped ENNReal Topology

namespace LOOConcentration

private theorem continuous_datasetToEuclidean {k m n : ℕ} :
    Continuous (datasetToEuclidean : Dataset (Observation k m) n →
      EuclideanSpace ℝ (DatasetCoordinate k m n)) := by
  change Continuous (fun D : Dataset (Observation k m) n =>
    WithLp.toLp (2 : ENNReal) (fun q : DatasetCoordinate k m n =>
      Sum.elim (D q.1).1 (D q.1).2 q.2))
  exact (PiLp.continuous_toLp (p := (2 : ENNReal))
      (β := fun _ : DatasetCoordinate k m n => ℝ)).comp (by
    apply continuous_pi
    intro q
    rcases q with ⟨i, c⟩
    cases c with
    | inl j => exact ((continuous_apply j).comp continuous_fst).comp (continuous_apply i)
    | inr j => exact ((continuous_apply j).comp continuous_snd).comp (continuous_apply i))

private theorem continuous_datasetFromEuclidean {k m n : ℕ} :
    Continuous (datasetFromEuclidean : EuclideanSpace ℝ (DatasetCoordinate k m n) →
      Dataset (Observation k m) n) := by
  apply continuous_pi
  intro i
  apply Continuous.prodMk
  · apply continuous_pi
    intro j
    exact PiLp.continuous_apply (p := (2 : ENNReal))
      (β := fun _ : DatasetCoordinate k m n => ℝ) (i, Sum.inl j)
  · apply continuous_pi
    intro j
    exact PiLp.continuous_apply (p := (2 : ENNReal))
      (β := fun _ : DatasetCoordinate k m n => ℝ) (i, Sum.inr j)

/-- The exact measurable equivalence between frozen datasets and their
flattened Euclidean coordinates. -/
def datasetEuclideanMeasurableEquiv {k m n : ℕ} :
    Dataset (Observation k m) n ≃ᵐ EuclideanSpace ℝ (DatasetCoordinate k m n) where
  toEquiv :=
    { toFun := datasetToEuclidean
      invFun := datasetFromEuclidean
      left_inv := datasetFromEuclidean_toEuclidean
      right_inv := datasetToEuclidean_fromEuclidean }
  measurable_toFun := continuous_datasetToEuclidean.measurable
  measurable_invFun := continuous_datasetFromEuclidean.measurable

theorem measurable_datasetToEuclidean {k m n : ℕ} :
    Measurable (datasetToEuclidean : Dataset (Observation k m) n →
      EuclideanSpace ℝ (DatasetCoordinate k m n)) :=
  continuous_datasetToEuclidean.measurable

theorem measurable_datasetFromEuclidean {k m n : ℕ} :
    Measurable (datasetFromEuclidean : EuclideanSpace ℝ (DatasetCoordinate k m n) →
      Dataset (Observation k m) n) :=
  continuous_datasetFromEuclidean.measurable

/-- The ordered i.i.d. product law on the frozen dataset carrier. -/
noncomputable def datasetProductLaw {k m n : ℕ} (μ : Measure (Observation k m)) :
    Measure (Dataset (Observation k m) n) :=
  Measure.pi fun _ : Fin n => μ

/-- The push-forward of the ordered product law to flattened Euclidean
coordinates. -/
noncomputable def flattenedDatasetProductLaw {k m n : ℕ} (μ : Measure (Observation k m)) :
    Measure (EuclideanSpace ℝ (DatasetCoordinate k m n)) :=
  Measure.map (datasetEuclideanMeasurableEquiv (k := k) (m := m) (n := n))
    (datasetProductLaw μ)

theorem flattenedDatasetProductLaw_eq_map_datasetToEuclidean {k m n : ℕ}
    (μ : Measure (Observation k m)) :
    flattenedDatasetProductLaw (k := k) (m := m) (n := n) μ =
      Measure.map (datasetToEuclidean : Dataset (Observation k m) n →
        EuclideanSpace ℝ (DatasetCoordinate k m n))
        (datasetProductLaw (k := k) (m := m) (n := n) μ) := by
  unfold flattenedDatasetProductLaw datasetEuclideanMeasurableEquiv
  rfl

theorem flattenedDatasetProductLaw_isProbabilityMeasure {k m n : ℕ}
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (flattenedDatasetProductLaw (k := k) (m := m) (n := n) μ) := by
  constructor
  rw [flattenedDatasetProductLaw_eq_map_datasetToEuclidean]
  rw [Measure.map_apply measurable_datasetToEuclidean MeasurableSet.univ]
  simp [datasetProductLaw]

/-- The Bochner integral of a function in flattened coordinates is its
integral after pulling back to the ordered dataset. -/
theorem integral_flattenedDatasetProductLaw_eq {k m n : ℕ}
    (μ : Measure (Observation k m))
    (F : EuclideanSpace ℝ (DatasetCoordinate k m n) → ℝ) :
    (∫ x, F x ∂flattenedDatasetProductLaw (k := k) (m := m) (n := n) μ) =
      ∫ D, F (datasetToEuclidean D)
        ∂datasetProductLaw (k := k) (m := m) (n := n) μ := by
  simpa [flattenedDatasetProductLaw, datasetProductLaw, datasetEuclideanMeasurableEquiv] using
    (integral_map_equiv (datasetEuclideanMeasurableEquiv (k := k) (m := m) (n := n)) F)

/-- Integrability is invariant under the dataset coordinate equivalence. -/
theorem integrable_flattenedDatasetProductLaw_iff {k m n : ℕ}
    (μ : Measure (Observation k m))
    (F : EuclideanSpace ℝ (DatasetCoordinate k m n) → ℝ) :
    Integrable F (flattenedDatasetProductLaw (k := k) (m := m) (n := n) μ) ↔
      Integrable (fun D : Dataset (Observation k m) n =>
        F (datasetToEuclidean D)) (datasetProductLaw (k := k) (m := m) (n := n) μ) := by
  simpa [flattenedDatasetProductLaw, datasetProductLaw, datasetEuclideanMeasurableEquiv,
    Function.comp_def] using
    (integrable_map_equiv
      (datasetEuclideanMeasurableEquiv (k := k) (m := m) (n := n)) F)

/-- The integral of a dataset function, expressed through the inverse
coordinate map, equals its integral under the ordered product law. -/
theorem integral_datasetFunction_euclidean_eq {k m n : ℕ}
    (μ : Measure (Observation k m))
    (F : Dataset (Observation k m) n → ℝ) :
    (∫ x, F (datasetFromEuclidean x)
      ∂flattenedDatasetProductLaw (k := k) (m := m) (n := n) μ) =
      ∫ D, F D ∂datasetProductLaw (k := k) (m := m) (n := n) μ := by
  simpa [Function.comp_def, datasetEuclideanMeasurableEquiv] using
    (integral_flattenedDatasetProductLaw_eq μ
      (fun x : EuclideanSpace ℝ (DatasetCoordinate k m n) =>
        F (datasetFromEuclidean x)))

/-- Integrability of a dataset function is equivalent on the ordered
product carrier and its flattened image. -/
theorem integrable_datasetFunction_euclidean_iff {k m n : ℕ}
    (μ : Measure (Observation k m))
    (F : Dataset (Observation k m) n → ℝ) :
    Integrable (fun x => F (datasetFromEuclidean x))
      (flattenedDatasetProductLaw (k := k) (m := m) (n := n) μ) ↔
      Integrable F (datasetProductLaw (k := k) (m := m) (n := n) μ) := by
  simpa [Function.comp_def, datasetEuclideanMeasurableEquiv] using
    (integrable_flattenedDatasetProductLaw_iff μ
      (fun x : EuclideanSpace ℝ (DatasetCoordinate k m n) =>
        F (datasetFromEuclidean x)))

/-- Nonnegative integrals, including exponential moments, transport exactly
under the coordinate map. -/
theorem lintegral_flattenedDatasetProductLaw_eq {k m n : ℕ}
    (μ : Measure (Observation k m))
    (G : EuclideanSpace ℝ (DatasetCoordinate k m n) → ℝ≥0∞) :
    (∫⁻ x, G x ∂flattenedDatasetProductLaw (k := k) (m := m) (n := n) μ) =
      ∫⁻ D, G (datasetToEuclidean D)
        ∂datasetProductLaw (k := k) (m := m) (n := n) μ := by
  simpa [flattenedDatasetProductLaw, datasetProductLaw, datasetEuclideanMeasurableEquiv] using
    (lintegral_map_equiv G
      (datasetEuclideanMeasurableEquiv (k := k) (m := m) (n := n)))

/-- A nonnegative dataset integrand, including a centered exponential,
has the same lintegral after coordinate transport. -/
theorem lintegral_datasetFunction_euclidean_eq {k m n : ℕ}
    (μ : Measure (Observation k m))
    (G : Dataset (Observation k m) n → ℝ≥0∞) :
    (∫⁻ x, G (datasetFromEuclidean x)
      ∂flattenedDatasetProductLaw (k := k) (m := m) (n := n) μ) =
      ∫⁻ D, G D ∂datasetProductLaw (k := k) (m := m) (n := n) μ := by
  simpa [Function.comp_def] using
    (lintegral_flattenedDatasetProductLaw_eq μ
      (fun x : EuclideanSpace ℝ (DatasetCoordinate k m n) =>
        G (datasetFromEuclidean x)))

/-- Probabilities of measurable coordinate events are computed by their
preimages on the ordered data carrier. -/
theorem flattenedDatasetProductLaw_event {k m n : ℕ}
    (μ : Measure (Observation k m))
    (s : Set (EuclideanSpace ℝ (DatasetCoordinate k m n)))
    (hs : MeasurableSet s) :
    flattenedDatasetProductLaw (k := k) (m := m) (n := n) μ s =
      datasetProductLaw (k := k) (m := m) (n := n) μ
        (datasetToEuclidean ⁻¹' s) := by
  rw [flattenedDatasetProductLaw_eq_map_datasetToEuclidean]
  exact Measure.map_apply measurable_datasetToEuclidean hs

/-- The squared frozen dataset norm is exactly the squared Euclidean norm
after flattening. -/
theorem euclideanDatasetNorm_sq {k m n : ℕ}
    (D : Dataset (Observation k m) n) :
    ‖datasetToEuclidean D‖ ^ 2 = datasetNormSq D := by
  rw [← datasetNorm_eq_euclidean]
  exact datasetNorm_sq D

/-- The squared Euclidean norm has the exact product second moment, with one
term per observation and no coordinate-dimension factor. -/
theorem integral_flattenedDatasetNorm_sq {k m n : ℕ}
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (hM2 : Integrable observationNormSq μ) :
    (∫ x : EuclideanSpace ℝ (DatasetCoordinate k m n), ‖x‖ ^ 2
      ∂flattenedDatasetProductLaw μ) =
      (n : ℝ) * ∫ z, observationNormSq z ∂μ := by
  calc
    (∫ x : EuclideanSpace ℝ (DatasetCoordinate k m n), ‖x‖ ^ 2
        ∂flattenedDatasetProductLaw μ) =
        ∫ D : Dataset (Observation k m) n, ‖datasetToEuclidean D‖ ^ 2
          ∂datasetProductLaw μ := by
      simpa [flattenedDatasetProductLaw, datasetProductLaw, datasetEuclideanMeasurableEquiv] using
        (integral_map_equiv
          (datasetEuclideanMeasurableEquiv (k := k) (m := m) (n := n))
          (fun x : EuclideanSpace ℝ (DatasetCoordinate k m n) => ‖x‖ ^ 2))
    _ = ∫ D : Dataset (Observation k m) n, datasetNormSq D
          ∂datasetProductLaw μ := by
      apply integral_congr_ae
      filter_upwards [] with D
      exact euclideanDatasetNorm_sq D
    _ = (n : ℝ) * ∫ z, observationNormSq z ∂μ := by
      exact integral_datasetNormSq μ hM2

/-- Finite one-observation second moment supplies integrability of the
squared Euclidean dataset norm under the pushed-forward product law. -/
theorem integrable_flattenedDatasetNorm_sq {k m n : ℕ}
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (hM2 : Integrable observationNormSq μ) :
    Integrable (fun x : EuclideanSpace ℝ (DatasetCoordinate k m n) => ‖x‖ ^ 2)
    (flattenedDatasetProductLaw (k := k) (m := m) (n := n) μ) := by
  change Integrable (fun x : EuclideanSpace ℝ (DatasetCoordinate k m n) => ‖x‖ ^ 2)
      (Measure.map (datasetEuclideanMeasurableEquiv (k := k) (m := m) (n := n))
      (datasetProductLaw (k := k) (m := m) (n := n) μ))
  apply (integrable_map_equiv
    (datasetEuclideanMeasurableEquiv (k := k) (m := m) (n := n))
    (fun x : EuclideanSpace ℝ (DatasetCoordinate k m n) => ‖x‖ ^ 2)).2
  have hmoment := integrable_datasetNormSq (k := k) (m := m) (n := n) μ hM2
  have hprod : Integrable datasetNormSq
      (datasetProductLaw (k := k) (m := m) (n := n) μ) := by
    simpa [datasetProductLaw] using hmoment
  convert hprod using 1
  funext D
  exact euclideanDatasetNorm_sq D

/-- The expectation of the Euclidean dataset norm is exactly the expectation
of the frozen norm on the ordered product carrier. -/
theorem integral_flattenedDatasetNorm_eq {k m n : ℕ}
    (μ : Measure (Observation k m))
    [IsProbabilityMeasure μ] :
    (∫ x : EuclideanSpace ℝ (DatasetCoordinate k m n), ‖x‖
      ∂flattenedDatasetProductLaw μ) =
      ∫ D : Dataset (Observation k m) n, datasetNorm D ∂datasetProductLaw μ := by
  calc
    (∫ x : EuclideanSpace ℝ (DatasetCoordinate k m n), ‖x‖
        ∂flattenedDatasetProductLaw μ) =
        ∫ D : Dataset (Observation k m) n, ‖datasetToEuclidean D‖
          ∂datasetProductLaw μ := by
      simpa [flattenedDatasetProductLaw, datasetProductLaw,
        datasetEuclideanMeasurableEquiv] using
        (integral_map_equiv
          (datasetEuclideanMeasurableEquiv (k := k) (m := m) (n := n))
          (fun x : EuclideanSpace ℝ (DatasetCoordinate k m n) => ‖x‖))
    _ = ∫ D : Dataset (Observation k m) n, datasetNorm D ∂datasetProductLaw μ := by
      apply integral_congr_ae
      filter_upwards [] with D
      exact (datasetNorm_eq_euclidean D).symm

/-- The local-slope and finite-second-moment inputs give the integrability
premise needed by wave 4 on the actual pushed-forward product law. The
remaining smooth centered-MGF envelope is kept explicit and is not derived
from a product log-Sobolev assumption here. -/
theorem centeredExp_locallyLipschitz_productLaw_bound {k m n : ℕ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (hM2 : Integrable observationNormSq μ)
    (F : LocallyLipschitzDataFunction k m n) {a b lam : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hSlope : ∀ D, datasetLocalSlope F D ≤ a + b * datasetNorm D)
    (B : ℕ → ℝ≥0∞) (Blim : ℝ≥0∞)
    (hSmooth : ∀ A : ℝ, 0 ≤ A → ∀ j : ℕ,
      ∫⁻ x, ENNReal.ofReal (Real.exp (lam *
        (datasetClipThenMollify F.1 A (datasetMollifierScale j) x -
          ∫ y, datasetClipThenMollify F.1 A (datasetMollifierScale j) y
            ∂flattenedDatasetProductLaw μ))) ∂flattenedDatasetProductLaw μ ≤ B j)
    (hB : Tendsto B atTop (𝓝 Blim)) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (lam *
      (F.1 (datasetFromEuclidean x) -
        ∫ y, F.1 (datasetFromEuclidean y) ∂flattenedDatasetProductLaw μ)))
      ∂flattenedDatasetProductLaw μ ≤ Blim := by
  let ν : Measure (DataCarrier k m n) :=
    datasetProductLaw (k := k + 1) (m := m + 1) (n := n + 1) μ
  let νE : Measure (EuclideanSpace ℝ
      (DatasetCoordinate (k + 1) (m + 1) (n + 1))) :=
    flattenedDatasetProductLaw (k := k + 1) (m := m + 1) (n := n + 1) μ
  have hνEprob : IsProbabilityMeasure νE := by
    dsimp [νE]
    exact flattenedDatasetProductLaw_isProbabilityMeasure (k := k + 1) (m := m + 1)
      (n := n + 1) μ
  have hseg : DatasetLinearGrowthSegmentBound F.1 a b := by
    intro D E
    exact datasetLocalSlope_segment_estimate F a b ha hb hSlope D E
  have hFprod : Integrable F.1 ν := by
    exact integrable_datasetFunction_of_localSlope_bound μ hM2 F a b ha hb hSlope
  have hFcoord : Integrable
      (fun x : EuclideanSpace ℝ
        (DatasetCoordinate (k + 1) (m + 1) (n + 1)) =>
          F.1 (datasetFromEuclidean x)) νE := by
    change Integrable
      (fun x : EuclideanSpace ℝ
        (DatasetCoordinate (k + 1) (m + 1) (n + 1)) =>
          F.1 (datasetFromEuclidean x))
      (Measure.map (datasetEuclideanMeasurableEquiv (k := k + 1) (m := m + 1)
        (n := n + 1)) ν)
    apply (integrable_map_equiv
      (datasetEuclideanMeasurableEquiv (k := k + 1) (m := m + 1) (n := n + 1))
      (fun x : EuclideanSpace ℝ
        (DatasetCoordinate (k + 1) (m + 1) (n + 1)) =>
          F.1 (datasetFromEuclidean x))).2
    convert hFprod using 1
    funext D
    simp [datasetEuclideanMeasurableEquiv]
  exact @centeredExp_datasetFunction_bound (k + 1) (m + 1) (n + 1) F.1 a b lam νE
    hνEprob B Blim hseg ha hb hFcoord hSmooth hB

end LOOConcentration
