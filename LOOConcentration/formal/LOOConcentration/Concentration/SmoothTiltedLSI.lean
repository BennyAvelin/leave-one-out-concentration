import LOOConcentration.Concentration.SmoothTestEnergy
import LOOConcentration.Frozen.FunctionalInequalities.HasLogSobolev
import LOOConcentration.FunctionalInequalities.SmoothProductLSI
import Mathlib.Tactic

/-!
# Smooth exponential admission for product log-Sobolev

For a bounded C¹ dataset pullback, the actual exponential test is identified
with a C¹ Euclidean pullback. Its global positive bounds give both entropy
integrability requirements, and `SmoothTestEnergy` supplies its actual
squared-slope energy. The final bridge applies the audited same-constant
bounded-positive smooth product-LSI theorem from the frozen one-observation
`HasLogSobolev` premise, via the reviewed
`LOOConcentration.FunctionalInequalities.SmoothProductLSI` provider.
-/

set_option autoImplicit false

open MeasureTheory
open scoped Topology

namespace LOOConcentration

/-- The actual exponential test has the requested global positive bounds, for
all real parameters including zero. -/
theorem expTiltedTestFunction_value_bounds
    {k m n : ℕ} (F : LocallyLipschitzDataFunction k m n)
    (lam B : ℝ) (hB : 0 ≤ B) (hBound : ∀ D, |F.1 D| ≤ B)
    (D : DataCarrier k m n) :
    Real.exp (-(|lam| * B / 2)) ≤
        (expTiltedTestFunction F lam B hB hBound).1 D ∧
      (expTiltedTestFunction F lam B hB hBound).1 D ≤
        Real.exp (|lam| * B / 2) := by
  have hHalf : |lam / 2| = |lam| / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hArg : |(lam / 2) * F.1 D| ≤ |lam| * B / 2 := by
    calc
      |(lam / 2) * F.1 D| = |lam / 2| * |F.1 D| := abs_mul _ _
      _ ≤ |lam / 2| * B :=
        mul_le_mul_of_nonneg_left (hBound D) (abs_nonneg _)
      _ = |lam| * B / 2 := by rw [hHalf]; ring
  have hValue :
      (expTiltedTestFunction F lam B hB hBound).1 D =
        Real.exp ((lam / 2) * F.1 D) := by
    rfl
  rw [hValue]
  constructor
  · exact Real.exp_le_exp.mpr (neg_le_of_abs_le hArg)
  · exact Real.exp_le_exp.mpr (le_of_abs_le hArg)

/-- Squaring the actual exponential test cancels the half in its definition.
This pointwise identity is useful for its entropy kernel. -/
theorem expTiltedTestFunction_sq_eq
    {k m n : ℕ} (F : LocallyLipschitzDataFunction k m n)
    (lam B : ℝ) (hB : 0 ≤ B) (hBound : ∀ D, |F.1 D| ≤ B)
    (D : DataCarrier k m n) :
    (expTiltedTestFunction F lam B hB hBound).1 D ^ 2 =
      Real.exp (lam * F.1 D) := by
  change (Real.exp ((lam / 2) * F.1 D)) ^ 2 = Real.exp (lam * F.1 D)
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

private theorem expTiltedTest_entropyKernel_eq
    {k m n : ℕ} (F : LocallyLipschitzDataFunction k m n)
    (lam B : ℝ) (hB : 0 ≤ B) (hBound : ∀ D, |F.1 D| ≤ B) :
    (fun D : DataCarrier k m n =>
      (expTiltedTestFunction F lam B hB hBound).1 D ^ 2 *
        Real.log ((expTiltedTestFunction F lam B hB hBound).1 D ^ 2)) =
      fun D => Real.exp (lam * F.1 D) * (lam * F.1 D) := by
  funext D
  rw [expTiltedTestFunction_sq_eq, Real.log_exp]

private theorem measurable_smoothExpTiltedTest_sq
    {k m n : ℕ}
    (f : EuclideanSpace ℝ (DatasetCoordinate (k + 1) (m + 1) (n + 1)) → ℝ)
    (hf : ContDiff ℝ 1 f) (lam B : ℝ) (hB : 0 ≤ B)
    (hBound : ∀ D : DataCarrier k m n,
      |(smoothDatasetPullback f hf).1 D| ≤ B) :
    Measurable (fun D : DataCarrier k m n =>
      (expTiltedTestFunction (smoothDatasetPullback f hf) lam B hB hBound).1 D ^ 2) := by
  have hBoundEuclidean : ∀ D : DataCarrier k m n,
      |f (datasetToEuclidean D)| ≤ B := by
    intro D
    simpa [smoothDatasetPullback] using hBound D
  have hIdentity := expTiltedTestFunction_smoothPullback_eq
    f hf lam B hB hBoundEuclidean
  rw [hIdentity]
  change Measurable (fun D : DataCarrier k m n =>
    (Real.exp (lam / 2 * f (datasetToEuclidean D))) ^ 2)
  exact (((Real.continuous_exp.comp (continuous_const.mul hf.continuous)).pow 2).measurable).comp
    measurable_datasetToEuclidean

/-- The actual squared exponential test is integrable under the finite product
law. -/
theorem integrable_smoothExpTiltedTest_sq
    {k m n : ℕ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (f : EuclideanSpace ℝ (DatasetCoordinate (k + 1) (m + 1) (n + 1)) → ℝ)
    (hf : ContDiff ℝ 1 f) (lam B : ℝ) (hB : 0 ≤ B)
    (hBound : ∀ D : DataCarrier k m n,
      |(smoothDatasetPullback f hf).1 D| ≤ B) :
    Integrable
      (fun D : DataCarrier k m n =>
        (expTiltedTestFunction (smoothDatasetPullback f hf) lam B hB hBound).1 D ^ 2)
      (Measure.pi fun _ : Fin (n + 1) => μ) := by
  let ν : Measure (DataCarrier k m n) := Measure.pi fun _ : Fin (n + 1) => μ
  let T := expTiltedTestFunction (smoothDatasetPullback f hf) lam B hB hBound
  have hMeas := measurable_smoothExpTiltedTest_sq f hf lam B hB hBound
  have hPoint (D : DataCarrier k m n) :
      ‖T.1 D ^ 2‖ ≤ Real.exp (|lam| * B) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hUpper := (expTiltedTestFunction_value_bounds
      (smoothDatasetPullback f hf) lam B hB hBound D).2
    have hSquare := (sq_le_sq₀ (le_of_lt (Real.exp_pos _))
      (le_of_lt (Real.exp_pos _))).2 hUpper
    have hExpSquare :
        Real.exp (|lam| * B / 2) ^ 2 = Real.exp (|lam| * B) := by
      calc
        _ = Real.exp (|lam| * B / 2) * Real.exp (|lam| * B / 2) := by ring
        _ = Real.exp (|lam| * B / 2 + |lam| * B / 2) := by
          rw [← Real.exp_add]
        _ = Real.exp (|lam| * B) := by
          congr 1
          ring
    rw [hExpSquare] at hSquare
    change (expTiltedTestFunction
      (smoothDatasetPullback f hf) lam B hB hBound).1 D ^ 2 ≤ _
    exact hSquare
  exact Integrable.of_bound hMeas.aestronglyMeasurable
    (Real.exp (|lam| * B)) (Filter.Eventually.of_forall hPoint)

/-- The actual entropy integrand `test² log(test²)` is integrable. Its exact
formula is `exp(lam * F) * (lam * F)`, with a global absolute bound. -/
theorem integrable_smoothExpTiltedTest_entropyKernel
    {k m n : ℕ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (f : EuclideanSpace ℝ (DatasetCoordinate (k + 1) (m + 1) (n + 1)) → ℝ)
    (hf : ContDiff ℝ 1 f) (lam B : ℝ) (hB : 0 ≤ B)
    (hBound : ∀ D : DataCarrier k m n,
      |(smoothDatasetPullback f hf).1 D| ≤ B) :
    Integrable
      (fun D : DataCarrier k m n =>
        (expTiltedTestFunction (smoothDatasetPullback f hf) lam B hB hBound).1 D ^ 2 *
          Real.log ((expTiltedTestFunction
            (smoothDatasetPullback f hf) lam B hB hBound).1 D ^ 2))
      (Measure.pi fun _ : Fin (n + 1) => μ) := by
    let F := smoothDatasetPullback f hf
    let T := expTiltedTestFunction F lam B hB hBound
    have hMeasF : Measurable F.1 := by
      change Measurable (fun D : DataCarrier k m n => f (datasetToEuclidean D))
      exact hf.continuous.measurable.comp measurable_datasetToEuclidean
    have hArgMeas : Measurable (fun D : DataCarrier k m n => lam * F.1 D) :=
      measurable_const.mul hMeasF
    have hKernelMeas : Measurable (fun D : DataCarrier k m n =>
        Real.exp (lam * F.1 D) * (lam * F.1 D)) :=
      (Real.continuous_exp.measurable.comp hArgMeas).mul hArgMeas
    have hKernelEq := expTiltedTest_entropyKernel_eq F lam B hB hBound
    have hBoundKernel (D : DataCarrier k m n) :
        ‖T.1 D ^ 2 * Real.log (T.1 D ^ 2)‖ ≤
          Real.exp (|lam| * B) * (|lam| * B) := by
      change ‖(expTiltedTestFunction F lam B hB hBound).1 D ^ 2 *
        Real.log ((expTiltedTestFunction F lam B hB hBound).1 D ^ 2)‖ ≤ _
      have hKernelAt := congrFun hKernelEq D
      rw [Real.norm_eq_abs, hKernelAt]
      rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
      have hArg : |lam * F.1 D| ≤ |lam| * B := by
        calc
          |lam * F.1 D| = |lam| * |F.1 D| := abs_mul _ _
          _ ≤ |lam| * B := mul_le_mul_of_nonneg_left (hBound D) (abs_nonneg _)
      exact mul_le_mul (Real.exp_le_exp.mpr (le_of_abs_le hArg)) hArg
        (abs_nonneg _) (Real.exp_nonneg _)
    refine Integrable.of_bound ?_ (Real.exp (|lam| * B) * (|lam| * B)) ?_
    · have hMeasKernel : Measurable (fun D : DataCarrier k m n =>
          T.1 D ^ 2 * Real.log (T.1 D ^ 2)) := by
        rw [hKernelEq]
        exact hKernelMeas
      exact hMeasKernel.aestronglyMeasurable
    · exact Filter.Eventually.of_forall hBoundKernel

/-- The actual squared local slope of the exponential test is integrable under
the product law by the reviewed smooth-energy admission. -/
theorem integrable_smoothExpTiltedTest_slope_sq
    {k m n : ℕ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (hM2 : Integrable observationNormSq μ)
    (f : EuclideanSpace ℝ (DatasetCoordinate (k + 1) (m + 1) (n + 1)) → ℝ)
    (hf : ContDiff ℝ 1 f) (lam B a b : ℝ) (hB : 0 ≤ B)
    (hBound : ∀ D : DataCarrier k m n,
      |(smoothDatasetPullback f hf).1 D| ≤ B)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hSlope : ∀ D : DataCarrier k m n,
      datasetLocalSlope (smoothDatasetPullback f hf) D ≤ a + b * datasetNorm D) :
    Integrable
      (fun D : DataCarrier k m n =>
        datasetLocalSlope
          (expTiltedTestFunction (smoothDatasetPullback f hf) lam B hB hBound) D ^ 2)
      (Measure.pi fun _ : Fin (n + 1) => μ) := by
  have hBoundEuclidean : ∀ D : DataCarrier k m n,
      |f (datasetToEuclidean D)| ≤ B := by
    intro D
    simpa [smoothDatasetPullback] using hBound D
  exact integrable_smoothExpTiltedTestFunction_energy
    μ hM2 f hf lam B a b hB hBoundEuclidean ha hb hSlope

/-- Exact `SmoothQuadraticMGF` per-test binder. For each bounded smooth
exponential test, its actual range and squared-slope energy put it in the
audited same-constant smooth product-LSI class. -/
theorem smoothExpTiltedTest_hProductLSI
    {k m n : ℕ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    {C B a b : ℝ} (hLSI : HasLogSobolev μ C)
    (hB : 0 ≤ B)
    (hM2 : Integrable observationNormSq μ)
    (f : EuclideanSpace ℝ (DatasetCoordinate (k + 1) (m + 1) (n + 1)) → ℝ)
    (hf : ContDiff ℝ 1 f) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hBound : ∀ D : DataCarrier k m n,
      |(smoothDatasetPullback f hf).1 D| ≤ B)
    (hSlope : ∀ D : DataCarrier k m n,
      datasetLocalSlope (smoothDatasetPullback f hf) D ≤ a + b * datasetNorm D) :
    ∀ lam : ℝ,
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
            ∂Measure.pi (fun _ : Fin (n + 1) => μ)) := by
  intro lam _ _ _
  let ν : Measure (DataCarrier k m n) := Measure.pi fun _ : Fin (n + 1) => μ
  let F := smoothDatasetPullback f hf
  let T := expTiltedTestFunction F lam B hB hBound
  let g : EuclideanSpace ℝ (DatasetCoordinate (k + 1) (m + 1) (n + 1)) → ℝ :=
    fun x => Real.exp (lam / 2 * f x)
  have hg : ContDiff ℝ 1 g := by
    dsimp [g]
    have hexp : ContDiff ℝ 1 Real.exp :=
      Real.contDiff_exp.of_le (by exact le_top)
    exact hexp.comp (contDiff_const.mul hf)
  have hBoundEuclidean : ∀ D : DataCarrier k m n,
      |f (datasetToEuclidean D)| ≤ B := by
    intro D
    simpa [smoothDatasetPullback] using hBound D
  have hTestIdentity := expTiltedTestFunction_smoothPullback_eq
    f hf lam B hB hBoundEuclidean
  have hTestEq : T = smoothDatasetPullback g hg := by
    dsimp [T, F, g]
    exact hTestIdentity
  let M : ℝ := |lam| * B / 2
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  have hLower : 0 < Real.exp (-M) := Real.exp_pos _
  have hBounds : ∀ D : DataCarrier k m n,
      Real.exp (-M) ≤ (smoothDatasetPullback g hg).1 D ∧
        (smoothDatasetPullback g hg).1 D ≤ Real.exp M := by
    intro D
    have h := expTiltedTestFunction_value_bounds F lam B hB hBound D
    simpa [T, hTestEq, M] using h
  have hEnergyPullback :
      Integrable
        (fun D : DataCarrier k m n =>
          datasetLocalSlope (smoothDatasetPullback g hg) D ^ 2) ν := by
    have hEnergyActual := integrable_smoothExpTiltedTest_slope_sq
      μ hM2 f hf lam B a b hB hBound ha hb hSlope
    have hEnergyT :
        Integrable (fun D : DataCarrier k m n => datasetLocalSlope T D ^ 2) ν := by
      simpa [T, F, ν] using hEnergyActual
    simpa only [hTestEq] using hEnergyT
  have hProduct := smooth_product_lsi_bounded_positive hLSI g hg
    (Real.exp (-M)) (Real.exp M) hLower hBounds hEnergyPullback
  have hProductT := hProduct
  rw [← hTestEq] at hProductT
  simpa [T, F, ν] using hProductT

#print axioms expTiltedTestFunction_value_bounds
#print axioms expTiltedTestFunction_sq_eq
#print axioms integrable_smoothExpTiltedTest_sq
#print axioms integrable_smoothExpTiltedTest_entropyKernel
#print axioms integrable_smoothExpTiltedTest_slope_sq
#print axioms smoothExpTiltedTest_hProductLSI

end LOOConcentration
