import LOOConcentration.Concentration.EntropyAbsorption
import LOOConcentration.Concentration.EntropyToMGF
import LOOConcentration.Concentration.EntropyVariational
import LOOConcentration.Concentration.SmoothTestEnergy
import LOOConcentration.Concentration.TiltedEntropyEnergy
import LOOConcentration.Concentration.TiltedNormMoment
import LOOConcentration.Analysis.DatasetMeasureTransport
import LOOConcentration.Geometry.EuclideanNormFacts
import Mathlib.Tactic

/-!
# Smooth bounded quadratic-growth log-MGF

This module assembles the reviewed tilted-entropy, tilted-norm, absorption,
and centered log-partition producers for an actual smooth dataset pullback.
The same-constant product-LSI output and the ordinary squared-norm MGF output
remain explicit predecessors.

Source: [arXiv:2211.02478](https://arxiv.org/abs/2211.02478) (historical audit version),
-/

set_option autoImplicit false

open MeasureTheory

namespace LOOConcentration

noncomputable section

private theorem smoothDataset_tiltEntropy_bounds
    {k m n : ℕ} (μ : Measure (Observation (k + 1) (m + 1)))
    [IsProbabilityMeasure μ] (hM2 : Integrable observationNormSq μ)
    (f : EuclideanSpace ℝ
      (DatasetCoordinate (k + 1) (m + 1) (n + 1)) → ℝ)
    (hf : ContDiff ℝ 1 f) (lam B a b C : ℝ)
    (hB : 0 ≤ B)
    (hBound : ∀ D : DataCarrier k m n,
      |(smoothDatasetPullback f hf).1 D| ≤ B)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hSlope : ∀ D : DataCarrier k m n,
      datasetLocalSlope (smoothDatasetPullback f hf) D ≤
        a + b * datasetNorm D)
    (hC : 0 < C)
    (hProductLSI :
      Integrable
        (fun D : DataCarrier k m n =>
          (expTiltedTestFunction (smoothDatasetPullback f hf) lam B hB hBound).1 D ^ 2)
        (Measure.pi fun _ : Fin (n + 1) => μ) →
      Integrable
        (fun D : DataCarrier k m n =>
          (expTiltedTestFunction (smoothDatasetPullback f hf) lam B hB hBound).1 D ^ 2 *
            Real.log ((expTiltedTestFunction
              (smoothDatasetPullback f hf) lam B hB hBound).1 D ^ 2))
        (Measure.pi fun _ : Fin (n + 1) => μ) →
      Integrable
        (fun D : DataCarrier k m n =>
          datasetLocalSlope
            (expTiltedTestFunction (smoothDatasetPullback f hf) lam B hB hBound) D ^ 2)
        (Measure.pi fun _ : Fin (n + 1) => μ) →
      looconcentrationEntropy (Measure.pi fun _ : Fin (n + 1) => μ)
          (fun D : DataCarrier k m n =>
            (expTiltedTestFunction (smoothDatasetPullback f hf) lam B hB hBound).1 D ^ 2) ≤
        2 * C * (∫ D : DataCarrier k m n,
          datasetLocalSlope
            (expTiltedTestFunction (smoothDatasetPullback f hf) lam B hB hBound) D ^ 2
            ∂Measure.pi (fun _ : Fin (n + 1) => μ))) :
    tiltEntropy (Measure.pi fun _ : Fin (n + 1) => μ)
        (smoothDatasetPullback f hf).1 lam ≤
      (C * lam ^ 2 / 2) * (∫ D : DataCarrier k m n,
        tiltDensity (Measure.pi fun _ : Fin (n + 1) => μ)
          (smoothDatasetPullback f hf).1 lam D * (a + b * datasetNorm D) ^ 2
          ∂Measure.pi (fun _ : Fin (n + 1) => μ)) ∧
    tiltEntropy (Measure.pi fun _ : Fin (n + 1) => μ)
        (smoothDatasetPullback f hf).1 lam ≤
      C * lam ^ 2 * (a ^ 2 + b ^ 2 *
        (∫ D : DataCarrier k m n,
          tiltDensity (Measure.pi fun _ : Fin (n + 1) => μ)
            (smoothDatasetPullback f hf).1 lam D * datasetNormSq D
            ∂Measure.pi (fun _ : Fin (n + 1) => μ))) := by
  have hBoundEuclidean : ∀ D : DataCarrier k m n,
      |f (datasetToEuclidean D)| ≤ B := by
    intro D
    simpa [smoothDatasetPullback] using hBound D
  have hEnergy := integrable_smoothExpTiltedTestFunction_energy
    μ hM2 f hf lam B a b hB hBoundEuclidean ha hb hSlope
  have hEnergyMeas := hEnergy.aestronglyMeasurable
  exact tiltEntropy_le_of_datasetProductLogSobolev
    μ hM2 (smoothDatasetPullback f hf) lam B a b C
    hB hBound ha hb hSlope hEnergyMeas hC hProductLSI

/-- The smooth bounded pullback with linear-growth frozen slope has the
source positive-growth centered log-MGF bound. The ordinary norm exponential
integrability and log-MGF families are the explicit outputs expected from the
still-open `lemma:norm` producer. Product LSI is stated for the actual admitted
smooth exponential tests; `SmoothTestEnergy` discharges their squared-slope
energy inside the proof. -/
theorem smoothDataset_logPartitionLog_centered_positive_b
    {k m n : ℕ} (μ : Measure (Observation (k + 1) (m + 1)))
    [IsProbabilityMeasure μ] (hM2 : Integrable observationNormSq μ)
    (f : EuclideanSpace ℝ
      (DatasetCoordinate (k + 1) (m + 1) (n + 1)) → ℝ)
    (hf : ContDiff ℝ 1 f) {B C a b : ℝ}
    (hB : 0 ≤ B)
    (hBound : ∀ D : DataCarrier k m n,
      |(smoothDatasetPullback f hf).1 D| ≤ B)
    (hC : 0 < C) (ha : 0 ≤ a) (hb : 0 < b)
    (hSlope : ∀ D : DataCarrier k m n,
      datasetLocalSlope (smoothDatasetPullback f hf) D ≤
        a + b * datasetNorm D)
    (hProductLSI : ∀ lam,
      Integrable
        (fun D : DataCarrier k m n =>
          (expTiltedTestFunction (smoothDatasetPullback f hf) lam B hB hBound).1 D ^ 2)
        (Measure.pi fun _ : Fin (n + 1) => μ) →
      Integrable
        (fun D : DataCarrier k m n =>
          (expTiltedTestFunction (smoothDatasetPullback f hf) lam B hB hBound).1 D ^ 2 *
            Real.log ((expTiltedTestFunction
              (smoothDatasetPullback f hf) lam B hB hBound).1 D ^ 2))
        (Measure.pi fun _ : Fin (n + 1) => μ) →
      Integrable
        (fun D : DataCarrier k m n =>
          datasetLocalSlope
            (expTiltedTestFunction (smoothDatasetPullback f hf) lam B hB hBound) D ^ 2)
        (Measure.pi fun _ : Fin (n + 1) => μ) →
      looconcentrationEntropy (Measure.pi fun _ : Fin (n + 1) => μ)
          (fun D : DataCarrier k m n =>
            (expTiltedTestFunction (smoothDatasetPullback f hf) lam B hB hBound).1 D ^ 2) ≤
        2 * C * (∫ D : DataCarrier k m n,
          datasetLocalSlope
            (expTiltedTestFunction (smoothDatasetPullback f hf) lam B hB hBound) D ^ 2
            ∂Measure.pi (fun _ : Fin (n + 1) => μ)))
    (hNormExp : ∀ u, 0 < |u| → |u| ≤ 1 / (4 * C * b) →
      Integrable
        (fun D : DataCarrier k m n =>
          Real.exp ((2 * C * u ^ 2 * b ^ 2) * datasetNormSq D))
        (Measure.pi fun _ : Fin (n + 1) => μ))
    (hNormMGF : ∀ u, 0 < |u| → |u| ≤ 1 / (4 * C * b) →
      Real.log (∫ D : DataCarrier k m n,
        Real.exp ((2 * C * u ^ 2 * b ^ 2) * datasetNormSq D)
          ∂Measure.pi (fun _ : Fin (n + 1) => μ)) ≤
        ((2 * C * u ^ 2 * b ^ 2) * (n + 1) *
          (∫ z : Observation (k + 1) (m + 1), observationNormSq z ∂μ)) /
          (1 - 2 * C * (2 * C * u ^ 2 * b ^ 2)))
    {t : ℝ} (ht : |t| ≤ 1 / (4 * C * b)) :
    logPartitionLog (Measure.pi fun _ : Fin (n + 1) => μ)
        (smoothDatasetPullback f hf).1 t -
      t * (∫ D : DataCarrier k m n,
        (smoothDatasetPullback f hf).1 D ∂Measure.pi (fun _ : Fin (n + 1) => μ)) ≤
      2 * C * (a ^ 2 + 2 * b ^ 2 * (n + 1) *
        (∫ z : Observation (k + 1) (m + 1), observationNormSq z ∂μ)) * t ^ 2 := by
  let ν : Measure (DataCarrier k m n) := Measure.pi fun _ : Fin (n + 1) => μ
  let F := smoothDatasetPullback f hf
  have hFmeas : Measurable F.1 := by
    change Measurable (fun D : DataCarrier k m n => f (datasetToEuclidean D))
    exact hf.continuous.measurable.comp measurable_datasetToEuclidean
  have hBoundF : ∀ D, |F.1 D| ≤ B := by
    intro D
    exact hBound D
  have hM2nonneg : 0 ≤ ∫ z : Observation (k + 1) (m + 1),
      observationNormSq z ∂μ :=
    integral_nonneg_of_ae (ae_of_all _ fun z => observationNormSq_nonneg z)
  have hTiltMoment : ∀ u, 0 < |u| → |u| ≤ 1 / (4 * C * b) →
      Integrable
        (fun D : DataCarrier k m n =>
          tiltDensity ν F.1 u D * datasetNormSq D) ν := by
    intro u _ _
    exact integrable_datasetNormSq_tiltDensity_mul
      μ hM2 F.1 hFmeas hB hBoundF
  have hEntropy : ∀ u, 0 < |u| → |u| ≤ 1 / (4 * C * b) →
      tiltEntropy ν F.1 u ≤ C * u ^ 2 *
        (a ^ 2 + b ^ 2 *
          (∫ D : DataCarrier k m n,
            tiltDensity ν F.1 u D * datasetNormSq D ∂ν)) := by
    intro u hu huCut
    have hProductEntropy := smoothDataset_tiltEntropy_bounds
      μ hM2 f hf u B a b C hB hBound ha (le_of_lt hb) hSlope hC
      (hProductLSI u)
    exact hProductEntropy.2
  have hNormMGF' : ∀ u, 0 < |u| → |u| ≤ 1 / (4 * C * b) →
      Real.log (∫ D : DataCarrier k m n,
        Real.exp ((2 * C * u ^ 2 * b ^ 2) * datasetNormSq D) ∂ν) ≤
        ((2 * C * u ^ 2 * b ^ 2) * ((n + 1 : ℕ) : ℝ) *
          (∫ z : Observation (k + 1) (m + 1), observationNormSq z ∂μ)) /
          (1 - 2 * C * (2 * C * u ^ 2 * b ^ 2)) := by
    intro u hu huCut
    simpa only [Nat.cast_add, Nat.cast_one, ν] using hNormMGF u hu huCut
  simpa [ν, F, Nat.cast_add] using datasetNormSq_logPartitionLog_centered_positive_b
    (μ := ν) (F := F.1) hFmeas (B := B) (C := C) (b := b) (a := a)
    (M2 := ∫ z : Observation (k + 1) (m + 1), observationNormSq z ∂μ)
    (r := n + 1) hB hBoundF hC hb ha hM2nonneg hNormExp hTiltMoment
    hEntropy hNormMGF' ht

/-- The bounded-gradient branch uses the exact first tilted slope-energy
estimate. When `b=0`, its pointwise factor is exactly `a²`; the second, looser
quadratic expansion is not used. -/
theorem smoothDataset_logPartitionLog_centered_bounded_gradient
    {k m n : ℕ} (μ : Measure (Observation (k + 1) (m + 1)))
    [IsProbabilityMeasure μ] (hM2 : Integrable observationNormSq μ)
    (f : EuclideanSpace ℝ
      (DatasetCoordinate (k + 1) (m + 1) (n + 1)) → ℝ)
    (hf : ContDiff ℝ 1 f) {B C a : ℝ}
    (hB : 0 ≤ B)
    (hBound : ∀ D : DataCarrier k m n,
      |(smoothDatasetPullback f hf).1 D| ≤ B)
    (hC : 0 < C) (ha : 0 ≤ a)
    (hSlope : ∀ D : DataCarrier k m n,
      datasetLocalSlope (smoothDatasetPullback f hf) D ≤ a)
    (hProductLSI : ∀ lam,
      Integrable
        (fun D : DataCarrier k m n =>
          (expTiltedTestFunction (smoothDatasetPullback f hf) lam B hB hBound).1 D ^ 2)
        (Measure.pi fun _ : Fin (n + 1) => μ) →
      Integrable
        (fun D : DataCarrier k m n =>
          (expTiltedTestFunction (smoothDatasetPullback f hf) lam B hB hBound).1 D ^ 2 *
            Real.log ((expTiltedTestFunction
              (smoothDatasetPullback f hf) lam B hB hBound).1 D ^ 2))
        (Measure.pi fun _ : Fin (n + 1) => μ) →
      Integrable
        (fun D : DataCarrier k m n =>
          datasetLocalSlope
            (expTiltedTestFunction (smoothDatasetPullback f hf) lam B hB hBound) D ^ 2)
        (Measure.pi fun _ : Fin (n + 1) => μ) →
      looconcentrationEntropy (Measure.pi fun _ : Fin (n + 1) => μ)
          (fun D : DataCarrier k m n =>
            (expTiltedTestFunction (smoothDatasetPullback f hf) lam B hB hBound).1 D ^ 2) ≤
        2 * C * (∫ D : DataCarrier k m n,
          datasetLocalSlope
            (expTiltedTestFunction (smoothDatasetPullback f hf) lam B hB hBound) D ^ 2
            ∂Measure.pi (fun _ : Fin (n + 1) => μ)))
    (t : ℝ) :
    logPartitionLog (Measure.pi fun _ : Fin (n + 1) => μ)
        (smoothDatasetPullback f hf).1 t -
      t * (∫ D : DataCarrier k m n,
        (smoothDatasetPullback f hf).1 D ∂Measure.pi (fun _ : Fin (n + 1) => μ)) ≤
      (C * a ^ 2 / 2) * t ^ 2 := by
  let ν : Measure (DataCarrier k m n) := Measure.pi fun _ : Fin (n + 1) => μ
  let F := smoothDatasetPullback f hf
  have hFmeas : Measurable F.1 := by
    change Measurable (fun D : DataCarrier k m n => f (datasetToEuclidean D))
    exact hf.continuous.measurable.comp measurable_datasetToEuclidean
  have hBoundF : ∀ D, |F.1 D| ≤ B := fun D => hBound D
  have hProductEntropy : ∀ u, 0 < |u| →
      tiltEntropy ν F.1 u ≤ (C * a ^ 2 / 2) * u ^ 2 := by
    intro u hu
    have hTiltEntropy := smoothDataset_tiltEntropy_bounds
      μ hM2 f hf u B a 0 C hB hBound ha (by norm_num)
      (by
        intro D
        simpa using hSlope D)
      hC (hProductLSI u)
    have hDensityOne := tiltDensity_integral_eq_one
      (μ := ν) (F := F.1) hFmeas (B := B) (t := u) hB hBoundF
    have hTiltSquare :
        (∫ D : DataCarrier k m n,
          tiltDensity ν F.1 u D * (a + 0 * datasetNorm D) ^ 2 ∂ν) = a ^ 2 := by
      calc
        _ = ∫ D : DataCarrier k m n, a ^ 2 * tiltDensity ν F.1 u D ∂ν := by
          apply integral_congr_ae
          filter_upwards with D
          ring
        _ = a ^ 2 * ∫ D : DataCarrier k m n, tiltDensity ν F.1 u D ∂ν :=
          integral_const_mul _ _
        _ = a ^ 2 := by rw [hDensityOne]; ring
    calc
      tiltEntropy ν F.1 u ≤ (C * u ^ 2 / 2) *
          (∫ D : DataCarrier k m n,
            tiltDensity ν F.1 u D * (a + 0 * datasetNorm D) ^ 2 ∂ν) := hTiltEntropy.1
      _ = (C * a ^ 2 / 2) * u ^ 2 := by rw [hTiltSquare]; ring
  exact datasetNormSq_logPartitionLog_centered_bounded_gradient
    (μ := ν) (F := F.1) hFmeas (B := B) (C := C) (a := a)
    hB hBoundF hProductEntropy t

end

end LOOConcentration
