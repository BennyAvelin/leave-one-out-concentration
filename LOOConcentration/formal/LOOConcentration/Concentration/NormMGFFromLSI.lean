import LOOConcentration.Concentration.NormMGFLimit
import LOOConcentration.FunctionalInequalities.SmoothProductLSI
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# Admission and MGF application for actual norm-cap tests

The actual norm-cap exponential is identified with a smooth pullback, bounded
between one and its finite cap, and admitted with its actual squared-slope
energy. The reviewed same-constant smooth product LSI is applied directly to
discharge the cap entropy inequality from the original one-space assumption.

Source: [arXiv:2211.02478](https://arxiv.org/abs/2211.02478) (historical audit version),
-/

set_option autoImplicit false

open MeasureTheory
open scoped Topology

namespace LOOConcentration

noncomputable section

/-- Smooth exponential profile of the positive-scale norm cap. -/
noncomputable def normCapExpProfile {k m n : ℕ}
    (A : ℝ) (_hA : 0 < A) (s : ℝ)
    (x : EuclideanSpace ℝ (DatasetCoordinate (k + 1) (m + 1) (n + 1))) : ℝ :=
  Real.exp (s / 2 * (A * (1 - Real.exp (-‖x‖ ^ 2 / A))))

theorem contDiff_normCapExpProfile {k m n : ℕ} (A : ℝ) (hA : 0 < A) (s : ℝ) :
    ContDiff ℝ 1 (normCapExpProfile (k := k) (m := m) (n := n) A hA s) := by
  have hnormSq : ContDiff ℝ 1
      (fun x : EuclideanSpace ℝ
        (DatasetCoordinate (k + 1) (m + 1) (n + 1)) => ‖x‖ ^ 2) :=
    (contDiff_norm_sq ℝ).of_le (by exact le_top)
  have hexpInner : ContDiff ℝ 1 (fun x : EuclideanSpace ℝ
      (DatasetCoordinate (k + 1) (m + 1) (n + 1)) =>
        Real.exp (-‖x‖ ^ 2 / A)) := by
    have hexp : ContDiff ℝ 1 Real.exp :=
      Real.contDiff_exp.of_le (by exact le_top)
    exact hexp.comp (hnormSq.neg.div_const A)
  have hcap : ContDiff ℝ 1 (fun x : EuclideanSpace ℝ
      (DatasetCoordinate (k + 1) (m + 1) (n + 1)) =>
        A * (1 - Real.exp (-‖x‖ ^ 2 / A))) :=
    contDiff_const.mul (contDiff_const.sub hexpInner)
  unfold normCapExpProfile
  have hexp : ContDiff ℝ 1 Real.exp :=
    Real.contDiff_exp.of_le (by exact le_top)
  exact hexp.comp (contDiff_const.mul hcap)

/-- The actual locally-Lipschitz cap test is exactly this smooth Euclidean
pullback, with the frozen unnormalized dataset norm. -/
theorem normTruncationExpTest_eq_normCapExpProfile
    {k m n : ℕ} {A : ℝ} (hA : 0 < A) (s : ℝ) (hs : 0 ≤ s) :
    normTruncationExpTest (k := k) (m := m) (n := n) hA s hs =
    smoothDatasetPullback
        (normCapExpProfile (k := k) (m := m) (n := n) A hA s)
        (contDiff_normCapExpProfile (k := k) (m := m) (n := n) A hA s) := by
  apply Subtype.ext
  funext D
  change Real.exp ((s / 2) * normTruncation A hA D) =
    Real.exp (s / 2 * (A * (1 -
      Real.exp (-‖datasetToEuclidean D‖ ^ 2 / A))))
  congr 2
  unfold normTruncation
  rw [← datasetNorm_sq D, datasetNorm_eq_euclidean]

/-- The actual cap test is measurable on the Borel dataset carrier. -/
theorem measurable_normTruncationExpTest
    {k m n : ℕ} {A : ℝ} (hA : 0 < A) (s : ℝ) (hs : 0 ≤ s) :
    Measurable
      (fun D : Dataset (Observation (k + 1) (m + 1)) (n + 1) =>
        (normTruncationExpTest (k := k) (m := m) (n := n) hA s hs).1 D) := by
  have hval :
      (fun D : Dataset (Observation (k + 1) (m + 1)) (n + 1) =>
        (normTruncationExpTest (k := k) (m := m) (n := n) hA s hs).1 D) =
      fun D => Real.exp (s / 2 * normTruncation A hA D) := by
    funext D
    simp [normTruncationExpTest, normTruncation_locallyLipschitz]
  rw [hval]
  exact Real.measurable_exp.comp
    (measurable_const.mul
      ((normTruncation_contDiff (k := k) (m := m) (n := n) A hA).continuous.measurable))

/-- Pointwise positive lower and finite upper bounds for the actual norm-cap
exponential test on the whole dataset carrier. -/
theorem normTruncationExpTest_bounds
    {k m n : ℕ} {A : ℝ} (hA : 0 < A) (s : ℝ) (hs : 0 ≤ s)
    (D : Dataset (Observation (k + 1) (m + 1)) (n + 1)) :
    1 ≤ (normTruncationExpTest (k := k) (m := m) (n := n) hA s hs).1 D ∧
      (normTruncationExpTest (k := k) (m := m) (n := n) hA s hs).1 D ≤
        Real.exp (s * A / 2) := by
  change 1 ≤ Real.exp (s / 2 * normTruncation A hA D) ∧
      Real.exp (s / 2 * normTruncation A hA D) ≤ Real.exp (s * A / 2)
  have hQnonneg := normTruncation_nonneg hA D
  have hQle := normTruncation_le hA D
  have hsHalf : 0 ≤ s / 2 := by positivity
  constructor
  · exact Real.one_le_exp (mul_nonneg hsHalf hQnonneg)
  · apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hQle hsHalf]

/-- Apply the reviewed same-constant smooth product LSI, built from the
original one-space `HasLogSobolev`, to the actual norm-cap test. Its positive
range and finite squared-slope energy are established internally. -/
theorem normTruncation_entropy_of_hasLogSobolev
    {k m n : ℕ} (μ : Measure (Observation (k + 1) (m + 1)))
    [IsProbabilityMeasure μ] {A C s : ℝ} (hA : 0 < A)
    (hLSI : HasLogSobolev μ C)
    (hs : 0 ≤ s) :
    looconcentrationEntropy (Measure.pi fun _ : Fin (n + 1) => μ)
      (fun D : Dataset (Observation (k + 1) (m + 1)) (n + 1) =>
        Real.exp (s * normTruncation A hA D)) ≤
      2 * C * ∫ D : Dataset (Observation (k + 1) (m + 1)) (n + 1),
        datasetLocalSlope
          (normTruncationExpTest (k := k) (m := m) (n := n) hA s hs) D ^ 2
          ∂Measure.pi (fun _ : Fin (n + 1) => μ) := by
  let U := normTruncationExpTest (k := k) (m := m) (n := n) hA s hs
  let f := normCapExpProfile (k := k) (m := m) (n := n) A hA s
  let hf := contDiff_normCapExpProfile (k := k) (m := m) (n := n) A hA s
  have hUeq : U = smoothDatasetPullback f hf := by
    simpa [U, f, hf] using
      normTruncationExpTest_eq_normCapExpProfile
        (k := k) (m := m) (n := n) hA s hs
  have hBounds : ∀ D : DataCarrier k m n,
      1 ≤ (smoothDatasetPullback f hf).1 D ∧
        (smoothDatasetPullback f hf).1 D ≤ Real.exp (s * A / 2) := by
    intro D
    have h := normTruncationExpTest_bounds (k := k) (m := m) (n := n)
      hA s hs D
    simpa [U, hUeq] using h
  have hEnergyU := integrable_smoothNormTruncationExpTest_slope_sq
    (k := k) (m := m) (n := n) μ hA s hs
  have hEnergy : Integrable
      (fun D : DataCarrier k m n =>
        datasetLocalSlope (smoothDatasetPullback f hf) D ^ 2)
      (Measure.pi fun _ : Fin (n + 1) => μ) := by
    simpa [U, hUeq] using hEnergyU
  have hEntropySmooth := smooth_product_lsi_bounded_positive (μ := μ) hLSI f hf
    1 (Real.exp (s * A / 2)) (by norm_num) hBounds hEnergy
  have hEntropyU : looconcentrationEntropy (Measure.pi fun _ : Fin (n + 1) => μ)
      (fun D : DataCarrier k m n => U.1 D ^ 2) ≤
      2 * C * ∫ D : DataCarrier k m n,
        datasetLocalSlope U D ^ 2 ∂Measure.pi (fun _ : Fin (n + 1) => μ) := by
    simpa [U, hUeq] using hEntropySmooth
  have hSquare : ∀ D : Dataset (Observation (k + 1) (m + 1)) (n + 1),
      U.1 D ^ 2 = Real.exp (s * normTruncation A hA D) := by
    intro D
    have hval : U.1 D = Real.exp (s / 2 * normTruncation A hA D) := by
      simp [U, normTruncationExpTest, normTruncation_locallyLipschitz]
    rw [hval, pow_two, ← Real.exp_add]
    congr 1
    ring
  have hEntropyCap := hEntropyU
  simp_rw [hSquare] at hEntropyCap
  simpa [U] using hEntropyCap

/-- The reviewed norm-MGF limit from the original one-space `HasLogSobolev`
assumption and the actual finite second moment. The same-constant smooth
product LSI and cap entropy are discharged internally. -/
theorem datasetNormSq_exp_logMGF_le_of_hasLogSobolev
    {k m n : ℕ} (μ : Measure (Observation (k + 1) (m + 1)))
    [IsProbabilityMeasure μ] {C s : ℝ}
    (hLSI : HasLogSobolev μ C) (hs : 0 ≤ s) (hsCut : s < 1 / (2 * C))
    (hM2 : Integrable observationNormSq μ)
    :
    Integrable
        (fun D : Dataset (Observation (k + 1) (m + 1)) (n + 1) =>
          Real.exp (s * datasetNormSq D))
        (Measure.pi fun _ : Fin (n + 1) => μ) ∧
      Real.log (∫ D : Dataset (Observation (k + 1) (m + 1)) (n + 1),
        Real.exp (s * datasetNormSq D) ∂Measure.pi (fun _ : Fin (n + 1) => μ)) ≤
        s * ((n + 1 : ℝ) * ∫ z, observationNormSq z ∂μ) /
          (1 - 2 * C * s) := by
  have hCapEntropy := fun (A : ℝ) (hA : 0 < A) (t : ℝ) (ht : 0 ≤ t)
      (_hEnergy : Integrable
        (fun D : Dataset (Observation (k + 1) (m + 1)) (n + 1) =>
          datasetLocalSlope
            (normTruncationExpTest (k := k) (m := m) (n := n) hA t ht) D ^ 2)
        (Measure.pi fun _ : Fin (n + 1) => μ)) =>
      normTruncation_entropy_of_hasLogSobolev
        (k := k) (m := m) (n := n) μ hA hLSI ht
  have hProductEntropy : HasProductNormTruncationEntropy
      (k := k) (m := m) (n := n) μ C := by
    intro A hA t ht hEnergy
    exact hCapEntropy A hA t ht hEnergy
  exact datasetNormSq_exp_logMGF_le_of_product_entropy
    (k := k) (m := m) (n := n) μ hLSI.1 hs hsCut hM2 hProductEntropy

/-- Centered version of the actual norm-MGF limit from the original one-space
`HasLogSobolev` assumption. The `s=0` and zero-moment cases are included
without division by either quantity. -/
theorem centered_datasetNormSq_logMGF_le_of_hasLogSobolev
    {k m n : ℕ} (μ : Measure (Observation (k + 1) (m + 1)))
    [IsProbabilityMeasure μ] {C s : ℝ}
    (hLSI : HasLogSobolev μ C) (hs : 0 ≤ s) (hsCut : s < 1 / (2 * C))
    (hM2 : Integrable observationNormSq μ)
    :
    Integrable
        (fun D : Dataset (Observation (k + 1) (m + 1)) (n + 1) =>
          Real.exp (s * (datasetNormSq D -
            (n + 1 : ℝ) * ∫ z, observationNormSq z ∂μ)))
        (Measure.pi fun _ : Fin (n + 1) => μ) ∧
      Real.log (∫ D : Dataset (Observation (k + 1) (m + 1)) (n + 1),
        Real.exp (s * (datasetNormSq D -
          (n + 1 : ℝ) * ∫ z, observationNormSq z ∂μ))
          ∂Measure.pi (fun _ : Fin (n + 1) => μ)) ≤
        2 * C * s ^ 2 * ((n + 1 : ℝ) * ∫ z, observationNormSq z ∂μ) /
          (1 - 2 * C * s) := by
  have hCapEntropy := fun (A : ℝ) (hA : 0 < A) (t : ℝ) (ht : 0 ≤ t)
      (_hEnergy : Integrable
        (fun D : Dataset (Observation (k + 1) (m + 1)) (n + 1) =>
          datasetLocalSlope
            (normTruncationExpTest (k := k) (m := m) (n := n) hA t ht) D ^ 2)
        (Measure.pi fun _ : Fin (n + 1) => μ)) =>
      normTruncation_entropy_of_hasLogSobolev
        (k := k) (m := m) (n := n) μ hA hLSI ht
  have hProductEntropy : HasProductNormTruncationEntropy
      (k := k) (m := m) (n := n) μ C := by
    intro A hA t ht hEnergy
    exact hCapEntropy A hA t ht hEnergy
  exact centered_datasetNormSq_logMGF_le_of_product_entropy
    (k := k) (m := m) (n := n) μ hLSI.1 hs hsCut hM2 hProductEntropy

end

end LOOConcentration

#print axioms LOOConcentration.normTruncationExpTest_eq_normCapExpProfile
#print axioms LOOConcentration.contDiff_normCapExpProfile
#print axioms LOOConcentration.measurable_normTruncationExpTest
#print axioms LOOConcentration.normTruncationExpTest_bounds
#print axioms LOOConcentration.normTruncation_entropy_of_hasLogSobolev
#print axioms LOOConcentration.datasetNormSq_exp_logMGF_le_of_hasLogSobolev
#print axioms LOOConcentration.centered_datasetNormSq_logMGF_le_of_hasLogSobolev
