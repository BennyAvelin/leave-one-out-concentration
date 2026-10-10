import LOOConcentration.Concentration.EntropyVariational
import LOOConcentration.Geometry.EuclideanNormFacts
import LOOConcentration.Probability.SampleMoments
import Mathlib.Tactic

/-!
# Integrability of a tilted nonnegative moment

An exponential tilt by a bounded observable has a bounded density. Therefore
it preserves integrability of every nonnegative integrable statistic. Applied
to the frozen squared dataset norm, the ordinary product moment comes from the
one-observation second moment.
-/

set_option autoImplicit false

open MeasureTheory

namespace LOOConcentration

noncomputable section

/-- A bounded exponential tilt preserves integrability of a nonnegative
integrable statistic. -/
theorem integrable_tiltDensity_mul_of_nonneg_integrable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {F Q : Ω → ℝ} {B t : ℝ}
    (hFmeas : Measurable F) (hB : 0 ≤ B)
    (hF : ∀ ω, |F ω| ≤ B)
    (hQmeas : Measurable Q) (hQnonneg : ∀ ω, 0 ≤ Q ω)
    (hQ : Integrable Q μ) :
    Integrable (fun ω => tiltDensity μ F t ω * Q ω) μ := by
  have hZ : 0 < tiltPartition μ F t :=
    tiltPartition_pos hFmeas (B := B) hB hF
  let K : ℝ := Real.exp (|t| * B) / tiltPartition μ F t
  have hK : 0 ≤ K := by
    dsimp [K]
    exact div_nonneg (Real.exp_nonneg _) hZ.le
  have hDensityMeas : Measurable (tiltDensity μ F t) := by
    change Measurable
      (fun ω => Real.exp (t * F ω) / tiltPartition μ F t)
    exact (Real.measurable_exp.comp (measurable_const.mul hFmeas)).div_const _
  have hDensityNonneg : ∀ ω, 0 ≤ tiltDensity μ F t ω := by
    intro ω
    exact div_nonneg (Real.exp_nonneg _) hZ.le
  have hDensityLe : ∀ ω, tiltDensity μ F t ω ≤ K := by
    intro ω
    change Real.exp (t * F ω) / tiltPartition μ F t ≤ _
    dsimp [K]
    apply (div_le_div_iff_of_pos_right hZ).2
    apply Real.exp_le_exp.mpr
    calc
      t * F ω ≤ |t * F ω| := le_abs_self _
      _ = |t| * |F ω| := abs_mul _ _
      _ ≤ |t| * B := mul_le_mul_of_nonneg_left (hF ω) (abs_nonneg _)
  have hprodMeas : Measurable (fun ω => tiltDensity μ F t ω * Q ω) :=
    hDensityMeas.mul hQmeas
  refine Integrable.mono' (hQ.const_mul K) hprodMeas.aestronglyMeasurable ?_
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (hDensityNonneg ω) (hQnonneg ω))]
  exact mul_le_mul_of_nonneg_right (hDensityLe ω) (hQnonneg ω)

/-- The frozen squared dataset norm is integrable under the ordered product
law whenever one observation has finite second moment. -/
theorem integrable_datasetNormSq_tiltDensity_mul
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (hM2 : Integrable observationNormSq μ)
    (F : Dataset (Observation k m) n → ℝ) (hFmeas : Measurable F)
    {B t : ℝ} (hB : 0 ≤ B) (hF : ∀ D, |F D| ≤ B) :
    Integrable
      (fun D => tiltDensity (Measure.pi fun _ : Fin n => μ) F t D *
        datasetNormSq D)
      (Measure.pi fun _ : Fin n => μ) := by
  have hNormSq :
      Integrable (datasetNormSq (k := k) (m := m) (n := n))
        (Measure.pi fun _ : Fin n => μ) :=
    integrable_datasetNormSq μ hM2
  have hNormSqMeas :
      Measurable (datasetNormSq (k := k) (m := m) (n := n)) := by
    unfold datasetNormSq observationNormSq
    fun_prop
  exact integrable_tiltDensity_mul_of_nonneg_integrable
    (μ := Measure.pi fun _ : Fin n => μ) (F := F) (Q := datasetNormSq)
    hFmeas hB hF hNormSqMeas datasetNormSq_nonneg hNormSq

/-- Cutoff-indexed form matching the tilted norm moment family used by the
positive-growth log-MGF theorem. The estimate itself holds for every real
tilt parameter, independently of the cutoff. -/
theorem integrable_datasetNormSq_tiltDensity_mul_family
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (hM2 : Integrable observationNormSq μ)
    (F : Dataset (Observation k m) n → ℝ) (hFmeas : Measurable F)
    {B Λ : ℝ} (hB : 0 ≤ B) (hF : ∀ D, |F D| ≤ B) :
    ∀ t, 0 < |t| → |t| ≤ Λ →
      Integrable
        (fun D => tiltDensity (Measure.pi fun _ : Fin n => μ) F t D *
          datasetNormSq D)
        (Measure.pi fun _ : Fin n => μ) := by
  intro t _ _
  exact integrable_datasetNormSq_tiltDensity_mul μ hM2 F hFmeas hB hF

end
end LOOConcentration
