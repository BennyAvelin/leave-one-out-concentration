import LOOConcentration.Probability.SampleTestLaw
import LOOConcentration.Geometry.EuclideanNormFacts
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-!
# Second moment of an ordered independent sample

The manuscript uses the unnormalized Euclidean norm of all data coordinates.
The expected squared norm of an `n`-sample is `n` times the one-observation
second moment.
-/

set_option autoImplicit false

namespace LOOConcentration

open MeasureTheory

theorem integrable_datasetNormSq
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (hM2 : Integrable observationNormSq μ) :
    Integrable (datasetNormSq (k := k) (m := m) (n := n))
      (Measure.pi fun _ : Fin n => μ) := by
  change Integrable
    (fun D : Dataset (Observation k m) n => ∑ i : Fin n, observationNormSq (D i))
    (Measure.pi fun _ : Fin n => μ)
  apply integrable_finsetSum Finset.univ
  intro i _
  exact (sample_coordinate_measurePreserving μ i).integrable_comp_of_integrable hM2

theorem integral_datasetNormSq
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (hM2 : Integrable observationNormSq μ) :
    (∫ D : Dataset (Observation k m) n, datasetNormSq D
      ∂Measure.pi fun _ : Fin n => μ) =
      (n : ℝ) * ∫ z, observationNormSq z ∂μ := by
  have hcoord (i : Fin n) :
      (∫ D : Dataset (Observation k m) n, observationNormSq (D i)
        ∂Measure.pi fun _ : Fin n => μ) =
      ∫ z, observationNormSq z ∂μ := by
    have hmp := sample_coordinate_measurePreserving μ i
    have hfm : AEStronglyMeasurable observationNormSq
        ((Measure.pi fun _ : Fin n => μ).map
          (fun D : Dataset (Observation k m) n => D i)) := by
      rw [hmp.map_eq]
      exact hM2.aestronglyMeasurable
    simpa only [hmp.map_eq, Function.comp_def] using
      (integral_map hmp.measurable.aemeasurable hfm).symm
  change (∫ D : Dataset (Observation k m) n,
    ∑ i : Fin n, observationNormSq (D i)
      ∂Measure.pi fun _ : Fin n => μ) = _
  have hsum := integral_finsetSum (s := Finset.univ)
    (f := fun i (D : Dataset (Observation k m) n) => observationNormSq (D i))
    (fun i _ => (sample_coordinate_measurePreserving μ i).integrable_comp_of_integrable hM2)
  rw [hsum]
  simp_rw [hcoord]
  simp

theorem integrable_datasetNorm
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (hM2 : Integrable observationNormSq μ) :
    Integrable (datasetNorm (k := k) (m := m) (n := n))
      (Measure.pi fun _ : Fin n => μ) := by
  have hsq := integrable_datasetNormSq (n := n) μ hM2
  have hm : Measurable (datasetNorm (k := k) (m := m) (n := n)) := by
    unfold datasetNorm datasetNormSq observationNormSq
    fun_prop
  apply Integrable.mono' (hsq.add (integrable_const (1 : ℝ))) hm.aestronglyMeasurable
  filter_upwards with D
  change ‖datasetNorm D‖ ≤ datasetNormSq D + 1
  have h0 : 0 ≤ datasetNorm D := Real.sqrt_nonneg _
  have hsqD := datasetNorm_sq D
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  nlinarith [sq_nonneg (datasetNorm D - 1)]

theorem integrable_test_rate_mul_datasetNorm
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (δ : Observation k m → ℝ)
    (hM2 : Integrable observationNormSq μ)
    (hδ : Integrable δ μ) :
    Integrable
      (fun p : Dataset (Observation k m) n × Observation k m =>
        δ p.2 * datasetNorm p.1)
      ((Measure.pi fun _ : Fin n => μ).prod μ) := by
  simpa only [mul_comm] using (integrable_datasetNorm (n := n) μ hM2).mul_prod hδ

end LOOConcentration
