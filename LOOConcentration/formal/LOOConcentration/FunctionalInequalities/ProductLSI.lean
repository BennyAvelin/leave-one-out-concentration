import LOOConcentration.Frozen.Norms.DatasetNormSq
import LOOConcentration.Probability.SampleMoments
import Mathlib.Tactic.FunProp

/-!
# First finite-product log-Sobolev facts

The manuscript states tensorization for smooth functions at source lines
308--309. This file records the exact squared-coordinate decomposition used
for a product gradient and section measurability/integrability facts for the
dataset squared norm. It does not assert tensorization of `HasLogSobolev` or
an estimate for nonsmooth partial local slopes.
-/

set_option autoImplicit false

namespace LOOConcentration

open MeasureTheory

/-- The squared Euclidean norm of a product tangent vector is the sum of the
squared norms of its coordinate blocks. In particular, this applies to a
smooth gradient once it is represented in dataset coordinates. -/
theorem datasetNormSq_coordinate_sum {k m n : ℕ}
    (V : Dataset (Observation k m) n) :
    datasetNormSq V = ∑ i : Fin n, observationNormSq (V i) := rfl

/-- Expand the dataset squared norm into the feature and response coordinate
sums, preserving the manuscript's unnormalized Euclidean convention. -/
theorem datasetNormSq_eq_feature_response_sum {k m n : ℕ}
    (D : Dataset (Observation k m) n) :
    datasetNormSq D =
      (∑ i : Fin n, ∑ j : Fin k, (D i).1 j ^ 2) +
      (∑ i : Fin n, ∑ j : Fin m, (D i).2 j ^ 2) := by
  simp [datasetNormSq, observationNormSq, Finset.sum_add_distrib]

/-- The squared dataset norm is continuous, hence measurable for the Borel
product space of observations. -/
theorem continuous_datasetNormSq {k m n : ℕ} :
    Continuous (datasetNormSq (k := k) (m := m) (n := n)) := by
  unfold datasetNormSq observationNormSq
  fun_prop

/-- Replacing one sample coordinate by a variable observation is a measurable
section. -/
theorem measurable_dataset_update_section {k m n : ℕ}
    (D : Dataset (Observation k m) n) (i : Fin n) :
    Measurable (fun z : Observation k m => Function.update D i z) := by
  classical
  apply measurable_pi_iff.2
  intro j
  by_cases hji : j = i
  · subst j
    simp only [Function.update_self]
    exact measurable_id
  · simp only [Function.update_of_ne hji]
    exact measurable_const

/-- Measurability of the squared dataset norm on each one-coordinate
section. -/
theorem measurable_datasetNormSq_section {k m n : ℕ}
    (D : Dataset (Observation k m) n) (i : Fin n) :
    Measurable (fun z : Observation k m =>
      datasetNormSq (Function.update D i z)) := by
  exact (continuous_datasetNormSq.measurable).comp
    (measurable_dataset_update_section D i)

/-- A one-coordinate section of the squared dataset norm is integrable under
the base law whenever one observation has finite second moment. -/
theorem integrable_datasetNormSq_section
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (hM2 : Integrable observationNormSq μ)
    (D : Dataset (Observation k m) n) (i : Fin n) :
    Integrable (fun z : Observation k m =>
      datasetNormSq (Function.update D i z)) μ := by
  change Integrable
    (fun z : Observation k m =>
      ∑ j : Fin n, observationNormSq (Function.update D i z j)) μ
  apply integrable_finsetSum Finset.univ
  intro j hj
  by_cases hji : j = i
  · subst j
    simpa only [Function.update_self] using hM2
  · simp only [Function.update_of_ne hji]
    exact integrable_const _

end LOOConcentration
