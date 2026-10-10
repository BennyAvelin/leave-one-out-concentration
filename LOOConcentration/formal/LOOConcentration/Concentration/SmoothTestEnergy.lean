import LOOConcentration.Concentration.ExponentialTestEnergy
import LOOConcentration.Concentration.TiltedEntropyEnergy
import LOOConcentration.Concentration.NormTruncationTest
import LOOConcentration.Geometry.SmoothLocalSlope
import LOOConcentration.Moments.PowerEnergyIntegrability
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Measurability and finite energy of actual smooth tests

Each test below is identified with a smooth pullback on the frozen Euclidean
dataset coordinates. The reviewed smooth-local-slope identity then supplies
measurability of its squared slope, allowing the previously conditional
energy-admission lemmas to be applied without an AE-measurability premise.
-/

set_option autoImplicit false

open MeasureTheory
open scoped Topology

namespace LOOConcentration

private abbrev SmoothDatasetEuclidean (k m n : ℕ) :=
  EuclideanSpace ℝ (DatasetCoordinate (k + 1) (m + 1) (n + 1))

private theorem contDiff_expScale {k m n : ℕ}
    (f : SmoothDatasetEuclidean k m n → ℝ) (hf : ContDiff ℝ 1 f) (c : ℝ) :
    ContDiff ℝ 1 (fun x => Real.exp (c * f x)) := by
  have hexp : ContDiff ℝ 1 Real.exp :=
    Real.contDiff_exp.of_le (by exact le_top)
  exact hexp.comp (contDiff_const.mul hf)

private theorem measurable_datasetLocalSlope_smoothPullback {k m n : ℕ}
    (f : SmoothDatasetEuclidean k m n → ℝ) (hf : ContDiff ℝ 1 f) :
    Measurable (fun D : DataCarrier k m n =>
      datasetLocalSlope (smoothDatasetPullback f hf) D) := by
  have hSq := continuous_datasetLocalSlope_sq_smoothPullback f hf
  have hEq : (fun D : DataCarrier k m n =>
      datasetLocalSlope (smoothDatasetPullback f hf) D) =
      fun D => Real.sqrt
        (datasetLocalSlope (smoothDatasetPullback f hf) D ^ 2) := by
    funext D
    rw [Real.sqrt_sq_eq_abs,
      abs_of_nonneg (datasetLocalSlope_nonneg (smoothDatasetPullback f hf) D)]
  rw [hEq]
  exact (Real.continuous_sqrt.comp hSq).measurable

private theorem contDiff_regularizedPowerProfile {k m n : ℕ}
    (f : SmoothDatasetEuclidean k m n → ℝ) (hf : ContDiff ℝ 1 f)
    (q ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ 1 (fun x => (f x ^ 2 + ε) ^ (q / 4)) := by
  have hbase : ContDiff ℝ 1 (fun x => f x ^ 2 + ε) :=
    (hf.pow 2).add contDiff_const
  exact hbase.rpow_const_of_ne (fun x => ne_of_gt (by positivity))

/-- The bounded exponential test of a smooth pullback is itself an actual
smooth pullback. This identity holds for every real `lam`, including zero. -/
theorem expTiltedTestFunction_smoothPullback_eq {k m n : ℕ}
    (f : SmoothDatasetEuclidean k m n → ℝ) (hf : ContDiff ℝ 1 f)
    (lam B : ℝ) (hB : 0 ≤ B)
    (hBound : ∀ D : DataCarrier k m n,
      |f (datasetToEuclidean D)| ≤ B) :
    expTiltedTestFunction (smoothDatasetPullback f hf) lam B hB
        (by simpa [smoothDatasetPullback] using hBound) =
      smoothDatasetPullback (fun x => Real.exp (lam / 2 * f x))
        (contDiff_expScale f hf (lam / 2)) := by
  apply Subtype.ext
  funext D
  simp [expTiltedTestFunction, smoothDatasetPullback]

/-- The squared local slope of the actual bounded smooth exponential test is
integrable under the actual product law, with no measurability premise. The
finite second moment and the source linear-growth slope bound provide its
energy majorant; the slope measurability follows from the smooth pullback. -/
theorem integrable_smoothExpTiltedTestFunction_energy {k m n : ℕ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (hM2 : Integrable observationNormSq μ)
    (f : SmoothDatasetEuclidean k m n → ℝ) (hf : ContDiff ℝ 1 f)
    (lam B a b : ℝ) (hB : 0 ≤ B)
    (hBound : ∀ D : DataCarrier k m n,
      |f (datasetToEuclidean D)| ≤ B)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hSlope : ∀ D : DataCarrier k m n,
      datasetLocalSlope (smoothDatasetPullback f hf) D ≤
        a + b * datasetNorm D) :
    Integrable
      (fun D : DataCarrier k m n =>
        datasetLocalSlope
          (expTiltedTestFunction (smoothDatasetPullback f hf) lam B hB
            (by simpa [smoothDatasetPullback] using hBound)) D ^ 2)
      (Measure.pi fun _ : Fin (n + 1) => μ) := by
  let g := smoothDatasetPullback f hf
  have hgBound : ∀ D, |g.1 D| ≤ B := by
    intro D
    simpa [g, smoothDatasetPullback] using hBound D
  have hIdentity := expTiltedTestFunction_smoothPullback_eq
    f hf lam B hB hBound
  have hMeas : Measurable (fun D : DataCarrier k m n =>
      datasetLocalSlope (expTiltedTestFunction g lam B hB hgBound) D ^ 2) := by
    rw [hIdentity]
    exact measurable_datasetLocalSlope_sq_smoothPullback
      (fun x => Real.exp (lam / 2 * f x)) (contDiff_expScale f hf (lam / 2))
  have hAE : AEStronglyMeasurable
      (fun D : DataCarrier k m n =>
        datasetLocalSlope (expTiltedTestFunction g lam B hB hgBound) D ^ 2)
      (Measure.pi fun _ : Fin (n + 1) => μ) := hMeas.aestronglyMeasurable
  simpa [g] using
    (integrable_expTiltedTestFunction_energy_of_aestronglyMeasurable_exact
      μ hM2 g lam B a b hB hgBound ha hb hSlope hAE)

private noncomputable def smoothNormTruncationProfile {k m n : ℕ}
    (A : ℝ) (x : SmoothDatasetEuclidean k m n) : ℝ :=
  A * (1 - Real.exp (-‖x‖ ^ 2 / A))

private theorem contDiff_smoothNormTruncationProfile {k m n : ℕ} (A : ℝ) :
    ContDiff ℝ 1 (smoothNormTruncationProfile (k := k) (m := m) (n := n) A) := by
  have hnormSq : ContDiff ℝ 1
      (fun x : SmoothDatasetEuclidean k m n => ‖x‖ ^ 2) :=
    (contDiff_norm_sq ℝ).of_le (by exact le_top)
  have hexp : ContDiff ℝ 1 (fun x : SmoothDatasetEuclidean k m n =>
      Real.exp (-‖x‖ ^ 2 / A)) := by
    have hrealExp : ContDiff ℝ 1 Real.exp :=
      Real.contDiff_exp.of_le (by exact le_top)
    exact hrealExp.comp (hnormSq.neg.div_const A)
  unfold smoothNormTruncationProfile
  exact contDiff_const.mul (contDiff_const.sub hexp)

private noncomputable def smoothNormTruncationExpProfile {k m n : ℕ}
    (A s : ℝ) (x : SmoothDatasetEuclidean k m n) : ℝ :=
  Real.exp (s / 2 * smoothNormTruncationProfile A x)

private theorem contDiff_smoothNormTruncationExpProfile {k m n : ℕ}
    (A s : ℝ) :
    ContDiff ℝ 1 (smoothNormTruncationExpProfile (k := k) (m := m) (n := n) A s) := by
  have hrealExp : ContDiff ℝ 1 Real.exp :=
    Real.contDiff_exp.of_le (by exact le_top)
  exact hrealExp.comp
    (contDiff_const.mul (contDiff_smoothNormTruncationProfile (k := k) (m := m) (n := n) A))

/-- The actual `Q_A` exponential test is a smooth pullback through the frozen
Euclidean dataset coordinates. -/
theorem normTruncationExpTest_smoothPullback_eq {k m n : ℕ} {A : ℝ}
    (hA : 0 < A) (s : ℝ) (hs : 0 ≤ s) :
    normTruncationExpTest (k := k) (m := m) (n := n) hA s hs =
      smoothDatasetPullback
        (smoothNormTruncationExpProfile (k := k) (m := m) (n := n) A s)
        (contDiff_smoothNormTruncationExpProfile (k := k) (m := m) (n := n) A s) := by
  apply Subtype.ext
  funext D
  change Real.exp ((s / 2) * normTruncation A hA D) =
    Real.exp ((s / 2) *
      smoothNormTruncationProfile (k := k) (m := m) (n := n) A
        (datasetToEuclidean D))
  congr 2
  unfold normTruncation smoothNormTruncationProfile
  rw [← datasetNorm_sq D, datasetNorm_eq_euclidean]

/-- The actual bounded norm truncation exponential has integrable squared
local slope under the product law. Its measurability is discharged by the
reviewed smooth-pullback local-slope identity. -/
theorem integrable_smoothNormTruncationExpTest_slope_sq {k m n : ℕ} {A : ℝ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (hA : 0 < A) (s : ℝ) (hs : 0 ≤ s) :
    Integrable
      (fun D : Dataset (Observation (k + 1) (m + 1)) (n + 1) =>
        datasetLocalSlope
          (normTruncationExpTest (k := k) (m := m) (n := n) hA s hs) D ^ 2)
      (Measure.pi fun _ : Fin (n + 1) => μ) := by
  have hIdentity := normTruncationExpTest_smoothPullback_eq
    (k := k) (m := m) (n := n) hA s hs
  have hMeas : Measurable (fun D : DataCarrier k m n =>
      datasetLocalSlope
        (normTruncationExpTest (k := k) (m := m) (n := n) hA s hs) D ^ 2) := by
    rw [hIdentity]
    exact measurable_datasetLocalSlope_sq_smoothPullback
      (smoothNormTruncationExpProfile (k := k) (m := m) (n := n) A s)
      (contDiff_smoothNormTruncationExpProfile (k := k) (m := m) (n := n) A s)
  exact integrable_normTruncationExpTest_slope_sq_of_aestronglyMeasurable
    μ hA s hs hMeas.aestronglyMeasurable

private noncomputable def smoothRegularizedPowerProfile {k m n : ℕ}
    (f : SmoothDatasetEuclidean k m n → ℝ) (q ε : ℝ)
    (x : SmoothDatasetEuclidean k m n) : ℝ :=
  (f x ^ 2 + ε) ^ (q / 4)

/-- The regularized power of a bounded smooth pullback is again an actual
smooth pullback when the regularization is positive. -/
theorem regularizedPowerTestFunction_smoothPullback_eq {k m n : ℕ}
    (f : SmoothDatasetEuclidean k m n → ℝ) (hf : ContDiff ℝ 1 f)
    (q ε B : ℝ) (hB : 0 ≤ B)
    (hBound : ∀ D : DataCarrier k m n,
      |f (datasetToEuclidean D)| ≤ B) (hε : 0 < ε) :
    regularizedPowerTestFunction (smoothDatasetPullback f hf) q ε B hB
        (by simpa [smoothDatasetPullback] using hBound) hε =
      smoothDatasetPullback (smoothRegularizedPowerProfile f q ε)
        (contDiff_regularizedPowerProfile f hf q ε hε) := by
  apply Subtype.ext
  funext D
  simp [smoothDatasetPullback, regularizedPowerTestFunction_apply,
    smoothRegularizedPowerProfile]

/-- For a bounded smooth source with actual finite `p`-energy, the regularized
power test has integrable squared local slope under the actual product law.
The wave-6 smooth identity supplies both source-slope measurability and the
transformed-slope AE measurability required by the reviewed wave-7 energy
domination theorem. -/
theorem integrable_smoothRegularizedPowerTest_slope_sq {k m n : ℕ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (f : SmoothDatasetEuclidean k m n → ℝ) (hf : ContDiff ℝ 1 f)
    (p q ε B : ℝ) (hB : 0 ≤ B)
    (hBound : ∀ D : DataCarrier k m n,
      |f (datasetToEuclidean D)| ≤ B)
    (hp : 2 ≤ p) (hq : 2 ≤ q) (hε : 0 < ε)
    (hLp : Integrable
      (fun D : DataCarrier k m n =>
        datasetLocalSlope (smoothDatasetPullback f hf) D ^ p)
      (Measure.pi fun _ : Fin (n + 1) => μ)) :
    Integrable
      (fun D : DataCarrier k m n =>
        datasetLocalSlope
          (regularizedPowerTestFunction (smoothDatasetPullback f hf) q ε B hB
            (by simpa [smoothDatasetPullback] using hBound) hε) D ^ 2)
      (Measure.pi fun _ : Fin (n + 1) => μ) := by
  let g := smoothDatasetPullback f hf
  have hgBound : ∀ D, |g.1 D| ≤ B := by
    intro D
    simpa [g, smoothDatasetPullback] using hBound D
  have hSourceMeas := measurable_datasetLocalSlope_smoothPullback f hf
  have hIdentity := regularizedPowerTestFunction_smoothPullback_eq
    f hf q ε B hB hBound hε
  have hPowerMeas : Measurable (fun D : DataCarrier k m n =>
      datasetLocalSlope
        (regularizedPowerTestFunction g q ε B hB hgBound hε) D ^ 2) := by
    rw [hIdentity]
    exact measurable_datasetLocalSlope_sq_smoothPullback
      (smoothRegularizedPowerProfile f q ε)
      (contDiff_regularizedPowerProfile f hf q ε hε)
  exact integrable_regularizedPowerTest_slope_sq_of_aestronglyMeasurable
    (g := g) (ν := Measure.pi fun _ : Fin (n + 1) => μ) p q ε B hB hgBound hε hp hq
    hSourceMeas hLp hPowerMeas.aestronglyMeasurable

#print axioms expTiltedTestFunction_smoothPullback_eq
#print axioms integrable_smoothExpTiltedTestFunction_energy
#print axioms normTruncationExpTest_smoothPullback_eq
#print axioms integrable_smoothNormTruncationExpTest_slope_sq
#print axioms regularizedPowerTestFunction_smoothPullback_eq
#print axioms integrable_smoothRegularizedPowerTest_slope_sq

end LOOConcentration
