import LOOConcentration.Analysis.DatasetMeasureTransport
import LOOConcentration.Geometry.SmoothLocalSlope
import LOOConcentration.Concentration.NormMGFFromLSI
import LOOConcentration.Concentration.SmoothQuadraticMGF
import LOOConcentration.Concentration.SmoothTiltedLSI

/-!
# Actual clip/mollify approximants for the general quadratic MGF

This file starts the source approximation route from the actual frozen
locally-Lipschitz dataset function.  It uses the project's clipped convolution
at cap `A` and the concrete radii `1 / (j + 1)`.  The reviewed smooth
log-MGF producer is applied only after the actual smoothness, boundedness,
and frozen-slope admissions are proved.
-/

set_option autoImplicit false

open Filter MeasureTheory
open scoped Topology ContDiff

namespace LOOConcentration

noncomputable section

private theorem generalQuadratic_segment_bound {k m n : ℕ}
    (F : LocallyLipschitzDataFunction k m n) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hSlope : ∀ D, datasetLocalSlope F D ≤ a + b * datasetNorm D) :
    DatasetLinearGrowthSegmentBound F.1 a b := by
  intro D E
  exact datasetLocalSlope_segment_estimate F a b ha hb hSlope D E

/-- The concrete mollified function used at clipping cap `A` and index `j`.
Its radius is the reviewed `1 / (j + 1)` sequence. -/
def generalQuadraticMollifier {k m n : ℕ}
    (F : LocallyLipschitzDataFunction k m n) (A : ℝ) (j : ℕ) :
    EuclideanSpace ℝ (DatasetCoordinate (k + 1) (m + 1) (n + 1)) → ℝ :=
  datasetClipThenMollify F.1 A (datasetMollifierScale j)

/-- Each actual approximation is smooth, using the source segment estimate to
obtain continuity of the frozen function before applying the mollifier. -/
theorem generalQuadraticMollifier_contDiff {k m n : ℕ}
    (F : LocallyLipschitzDataFunction k m n) {a b A : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hSlope : ∀ D, datasetLocalSlope F D ≤ a + b * datasetNorm D)
    (j : ℕ) :
    ContDiff ℝ 1 (generalQuadraticMollifier F A j) := by
  let hseg := generalQuadratic_segment_bound F ha hb hSlope
  have hcontinuous := continuous_datasetFunction_of_segmentBound hseg ha hb
  have hmoll : ContDiff ℝ ∞
      (clipThenMollify (fun x => F.1 (datasetFromEuclidean x)) A
        (datasetMollifierScale j)) :=
    contDiff_clipThenMollify
      (f := fun x => F.1 (datasetFromEuclidean x)) (N := A)
      (η := datasetMollifierScale j) hcontinuous (datasetMollifierScale_pos j)
  have hmoll1 : ContDiff ℝ 1
      (clipThenMollify (fun x => F.1 (datasetFromEuclidean x)) A
        (datasetMollifierScale j)) := hmoll.of_le
          (m := (1 : ℕ∞ω)) (n := (∞ : ℕ∞ω))
          (by exact_mod_cast (show (1 : ℕ∞) ≤ (⊤ : ℕ∞) from le_top))
  simpa [generalQuadraticMollifier, datasetClipThenMollify] using
    hmoll1

/-- The mollified approximant is bounded by its actual clipping cap. -/
theorem generalQuadraticMollifier_mem_Icc {k m n : ℕ}
    (F : LocallyLipschitzDataFunction k m n) {a b A : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hSlope : ∀ D, datasetLocalSlope F D ≤ a + b * datasetNorm D)
    (hA : 0 ≤ A) (j : ℕ)
    (x : EuclideanSpace ℝ (DatasetCoordinate (k + 1) (m + 1) (n + 1))) :
    generalQuadraticMollifier F A j x ∈ Set.Icc (-A) A := by
  let hseg := generalQuadratic_segment_bound F ha hb hSlope
  simpa [generalQuadraticMollifier] using
    datasetClipThenMollify_range hseg ha hb hA
      (datasetMollifierScale_pos j) x

/-- The exact frozen slope admission for the actual approximant.  Its
constant term is `a + b η_j`, and the coefficient of the frozen norm remains
exactly `b`. -/
theorem generalQuadraticMollifier_localSlope_bound {k m n : ℕ}
    (F : LocallyLipschitzDataFunction k m n) {a b A : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hSlope : ∀ D, datasetLocalSlope F D ≤ a + b * datasetNorm D)
    (j : ℕ) (D : DataCarrier k m n) :
    datasetLocalSlope
        (smoothDatasetPullback (generalQuadraticMollifier F A j)
          (generalQuadraticMollifier_contDiff F ha hb hSlope j)) D ≤
      a + b * datasetMollifierScale j + b * datasetNorm D := by
  rw [datasetLocalSlope_smoothPullback_eq]
  exact datasetClipThenMollify_fderiv_bound
    (generalQuadratic_segment_bound F ha hb hSlope) ha hb
    (datasetMollifierScale_pos j) D

/-- For fixed cap, the concrete smooth sequence converges pointwise to the
clipped frozen function. -/
theorem generalQuadraticMollifier_tendsto_clip {k m n : ℕ}
    (F : LocallyLipschitzDataFunction k m n) {a b A : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hSlope : ∀ D, datasetLocalSlope F D ≤ a + b * datasetNorm D)
    (x : EuclideanSpace ℝ (DatasetCoordinate (k + 1) (m + 1) (n + 1))) :
    Tendsto (fun j : ℕ => generalQuadraticMollifier F A j x)
      atTop (𝓝 (clipValue A (F.1 (datasetFromEuclidean x)))) := by
  simpa [generalQuadraticMollifier, datasetMollifierScale, Function.comp_def] using
    (datasetClipThenMollify_tendsto (N := A)
      (generalQuadratic_segment_bound F ha hb hSlope) ha hb
      (datasetFromEuclidean x)).comp datasetMollifierScale_tendsto

/-- At every fixed cap, the actual mollifier means converge under any
probability measure on the flattened carrier. -/
theorem generalQuadraticMollifier_integral_tendsto_clip {k m n : ℕ}
    (F : LocallyLipschitzDataFunction k m n) {a b A : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hSlope : ∀ D, datasetLocalSlope F D ≤ a + b * datasetNorm D)
    (hA : 0 ≤ A)
    (μ : Measure (EuclideanSpace ℝ (DatasetCoordinate (k + 1) (m + 1) (n + 1))))
    [IsProbabilityMeasure μ] :
    Tendsto (fun j : ℕ =>
        ∫ x, generalQuadraticMollifier F A j x ∂μ)
      atTop (𝓝 (∫ x,
        clipValue A (F.1 (datasetFromEuclidean x)) ∂μ)) := by
  simpa [generalQuadraticMollifier, Function.comp_def] using
    (datasetClipThenMollify_integral_tendsto (μ := μ)
      (generalQuadratic_segment_bound F ha hb hSlope) ha hb hA).comp
      datasetMollifierScale_tendsto

/-- The original locally-Lipschitz function is integrable under the actual
product law, and hence under its flattened image.  The segment estimate and
finite observation second moment are discharged internally. -/
theorem integrable_generalQuadraticFunction_flattened {k m n : ℕ}
    (μ : Measure (Observation (k + 1) (m + 1))) [IsProbabilityMeasure μ]
    (hM2 : Integrable observationNormSq μ)
    (F : LocallyLipschitzDataFunction k m n) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hSlope : ∀ D, datasetLocalSlope F D ≤ a + b * datasetNorm D) :
    Integrable
      (fun x : EuclideanSpace ℝ
          (DatasetCoordinate (k + 1) (m + 1) (n + 1)) =>
        F.1 (datasetFromEuclidean x))
      (flattenedDatasetProductLaw (k := k + 1) (m := m + 1) (n := n + 1) μ) := by
  apply (integrable_datasetFunction_euclidean_iff
    (k := k + 1) (m := m + 1) (n := n + 1) μ F.1).2
  exact integrable_datasetFunction_of_localSlope_bound μ hM2 F a b ha hb hSlope

/-- Centered exponential lintegrals are exactly preserved by the frozen to
Euclidean product-law equivalence, with the actual means transported too. -/
theorem centeredExp_lintegral_flattened_eq {k m n : ℕ}
    (μ : Measure (Observation k m)) (f :
      EuclideanSpace ℝ (DatasetCoordinate k m n) → ℝ) (lam : ℝ) :
    (∫⁻ x, ENNReal.ofReal (Real.exp
      (lam * (f x - ∫ y, f y ∂flattenedDatasetProductLaw
        (k := k) (m := m) (n := n) μ)))
      ∂flattenedDatasetProductLaw (k := k) (m := m) (n := n) μ) =
    ∫⁻ D, ENNReal.ofReal (Real.exp
      (lam * (f (datasetToEuclidean D) -
        ∫ E, f (datasetToEuclidean E) ∂datasetProductLaw
          (k := k) (m := m) (n := n) μ)))
      ∂datasetProductLaw (k := k) (m := m) (n := n) μ := by
  have hmean := integral_flattenedDatasetProductLaw_eq (k := k) (m := m) (n := n) μ f
  calc
    _ = ∫⁻ D, ENNReal.ofReal (Real.exp
        (lam * (f (datasetToEuclidean D) -
          ∫ y, f y ∂flattenedDatasetProductLaw
            (k := k) (m := m) (n := n) μ)))
        ∂datasetProductLaw (k := k) (m := m) (n := n) μ := by
      exact lintegral_flattenedDatasetProductLaw_eq (k := k) (m := m) (n := n) μ
        (fun x => ENNReal.ofReal (Real.exp
          (lam * (f x - ∫ y, f y ∂flattenedDatasetProductLaw
            (k := k) (m := m) (n := n) μ))))
    _ = _ := by rw [hmean]

private theorem centeredExp_lintegral_le_of_logPartitionLog
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    {f : Ω → ℝ} {lam B R : ℝ}
    (hmeas : Measurable f) (_hB : 0 ≤ B)
    (hBound : ∀ x, |f x| ≤ B)
    (hlog : logPartitionLog ν f lam - lam * (∫ x, f x ∂ν) ≤ R) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (lam * (f x - ∫ y, f y ∂ν))) ∂ν ≤
      ENNReal.ofReal (Real.exp R) := by
  let m := ∫ x, f x ∂ν
  have hfInt : Integrable f ν := by
    apply Integrable.mono' (integrable_const B) hmeas.aestronglyMeasurable
    filter_upwards [] with x
    simpa [Real.norm_eq_abs, abs_of_nonneg _hB] using hBound x
  have hexpInt : Integrable (fun x => Real.exp (lam * f x)) ν :=
    logPartition_integrable hmeas (B := B) (t := lam) hBound
  have hcenterEq : (fun x => Real.exp (lam * (f x - m))) =
      fun x => Real.exp (lam * f x) * Real.exp (-(lam * m)) := by
    funext x
    rw [show lam * (f x - m) = lam * f x + -(lam * m) by ring,
      Real.exp_add]
  have hcenterInt : Integrable (fun x => Real.exp (lam * (f x - m))) ν := by
    rw [hcenterEq]
    exact hexpInt.mul_const (Real.exp (-(lam * m)))
  have hZpos : 0 < ∫ x, Real.exp (lam * f x) ∂ν := by
    simpa [logPartition] using
      (logPartition_pos hmeas (B := B) (t := lam) hBound)
  have hcenterIntegral :
      (∫ x, Real.exp (lam * (f x - m)) ∂ν) =
        Real.exp (logPartitionLog ν f lam - lam * m) := by
    calc
      (∫ x, Real.exp (lam * (f x - m)) ∂ν) =
          (∫ x, Real.exp (lam * f x) ∂ν) * Real.exp (-(lam * m)) := by
        rw [hcenterEq, integral_mul_const]
      _ = Real.exp (logPartitionLog ν f lam - lam * m) := by
        change _ = Real.exp
          (Real.log (∫ x, Real.exp (lam * f x) ∂ν) - lam * m)
        rw [show Real.log (∫ x, Real.exp (lam * f x) ∂ν) - lam * m =
          Real.log (∫ x, Real.exp (lam * f x) ∂ν) + -(lam * m) by ring,
          Real.exp_add, Real.exp_log hZpos]
  have hrealBound :
      (∫ x, Real.exp (lam * (f x - m)) ∂ν) ≤ Real.exp R := by
    rw [hcenterIntegral]
    exact Real.exp_le_exp.mpr (by simpa [m] using hlog)
  calc
    (∫⁻ x, ENNReal.ofReal (Real.exp (lam * (f x - ∫ y, f y ∂ν))) ∂ν) =
        ENNReal.ofReal (∫ x, Real.exp (lam * (f x - m)) ∂ν) := by
      symm
      apply ofReal_integral_eq_lintegral_ofReal hcenterInt
      exact ae_of_all _ (fun x => (Real.exp_nonneg _))
    _ ≤ ENNReal.ofReal (Real.exp R) := ENNReal.ofReal_le_ofReal hrealBound

/-- The square-growth norm parameter used by the positive-`b` smooth producer
stays strictly inside the norm-MGF range on the source's closed cutoff. -/
private theorem positiveB_normParameter_lt_cutoff {C b u : ℝ}
    (hC : 0 < C) (hb : 0 < b)
    (hu : |u| ≤ 1 / (4 * C * b)) :
    2 * C * u ^ 2 * b ^ 2 < 1 / (2 * C) := by
  have hK : 0 < 1 / (4 * C * b) := by positivity
  have huSq : u ^ 2 ≤ (1 / (4 * C * b)) ^ 2 := by
    have hprod := mul_nonneg
      (sub_nonneg.mpr hu) (by positivity : 0 ≤ 1 / (4 * C * b) + |u|)
    nlinarith [sq_abs u, hprod]
  calc
    2 * C * u ^ 2 * b ^ 2 = (2 * C * b ^ 2) * u ^ 2 := by ring
    _ ≤ (2 * C * b ^ 2) * (1 / (4 * C * b)) ^ 2 :=
      mul_le_mul_of_nonneg_left huSq (by positivity)
    _ = 1 / (8 * C) := by field_simp; ring
    _ = (1 / 8) / C := by field_simp
    _ < (1 / 2) / C := div_lt_div_of_pos_right (by norm_num) hC
    _ = 1 / (2 * C) := by field_simp

/-- Actual mollifier exponential bound in the positive-growth case. The
reviewed smooth product LSI and original-LSI norm-MGF producer supply the
smooth quadratic calculus from the original one-observation assumption. -/
theorem generalQuadraticMollifier_centeredExp_lintegral_positive_b
    {k m n : ℕ} (μ : Measure (Observation (k + 1) (m + 1)))
    [IsProbabilityMeasure μ] (hM2 : Integrable observationNormSq μ)
    (F : LocallyLipschitzDataFunction k m n) {a b C A : ℝ}
    (ha : 0 ≤ a) (hb : 0 < b) (hLSI : HasLogSobolev μ C)
    (hSlope : ∀ D, datasetLocalSlope F D ≤ a + b * datasetNorm D)
    (hA : 0 ≤ A) (j : ℕ) {t : ℝ} (ht : |t| ≤ 1 / (4 * C * b)) :
    ∫⁻ x, ENNReal.ofReal (Real.exp
      (t * (generalQuadraticMollifier F A j x -
        ∫ y, generalQuadraticMollifier F A j y ∂flattenedDatasetProductLaw
          (k := k + 1) (m := m + 1) (n := n + 1) μ)))
      ∂flattenedDatasetProductLaw (k := k + 1) (m := m + 1) (n := n + 1) μ ≤
    ENNReal.ofReal (Real.exp
      (2 * C * ((a + b * datasetMollifierScale j) ^ 2 +
      2 * b ^ 2 * (n + 1) *
          (∫ z : Observation (k + 1) (m + 1), observationNormSq z ∂μ)) * t ^ 2)) := by
  have hC : 0 < C := hLSI.1
  let f := generalQuadraticMollifier F A j
  let hf := generalQuadraticMollifier_contDiff F (A := A) ha hb.le hSlope j
  let G := smoothDatasetPullback f hf
  let ν : Measure (DataCarrier k m n) := Measure.pi fun _ : Fin (n + 1) => μ
  let η := datasetMollifierScale j
  let aj := a + b * η
  have hAj : 0 ≤ aj := add_nonneg ha (mul_nonneg hb.le (datasetMollifierScale_pos j).le)
  have hBound : ∀ D : DataCarrier k m n, |G.1 D| ≤ A := by
    intro D
    have hrange := generalQuadraticMollifier_mem_Icc F ha hb.le hSlope hA j
      (datasetToEuclidean D)
    apply abs_le.mpr
    simpa [G, f, smoothDatasetPullback] using hrange
  have hSlopeG : ∀ D : DataCarrier k m n,
      datasetLocalSlope G D ≤ aj + b * datasetNorm D := by
    intro D
    simpa [G, f, hf, aj, η] using
      (generalQuadraticMollifier_localSlope_bound F ha hb.le hSlope j D)
  have hNormExp : ∀ u, 0 < |u| → |u| ≤ 1 / (4 * C * b) →
      Integrable
        (fun D : DataCarrier k m n =>
          Real.exp ((2 * C * u ^ 2 * b ^ 2) * datasetNormSq D)) ν := by
    intro u hu huCut
    let s := 2 * C * u ^ 2 * b ^ 2
    have hs : 0 ≤ s := by positivity
    have hsCut : s < 1 / (2 * C) := by
      simpa [s] using positiveB_normParameter_lt_cutoff hC hb huCut
    have hnorm := datasetNormSq_exp_logMGF_le_of_hasLogSobolev
      (k := k) (m := m) (n := n) μ hLSI hs hsCut hM2
    simpa [s, ν] using hnorm.1
  have hNormMGF : ∀ u, 0 < |u| → |u| ≤ 1 / (4 * C * b) →
      Real.log (∫ D : DataCarrier k m n,
        Real.exp ((2 * C * u ^ 2 * b ^ 2) * datasetNormSq D) ∂ν) ≤
        ((2 * C * u ^ 2 * b ^ 2) * (n + 1) *
          (∫ z : Observation (k + 1) (m + 1), observationNormSq z ∂μ)) /
          (1 - 2 * C * (2 * C * u ^ 2 * b ^ 2)) := by
    intro u hu huCut
    let s := 2 * C * u ^ 2 * b ^ 2
    have hs : 0 ≤ s := by positivity
    have hsCut : s < 1 / (2 * C) := by
      simpa [s] using positiveB_normParameter_lt_cutoff hC hb huCut
    have hnorm := datasetNormSq_exp_logMGF_le_of_hasLogSobolev
      (k := k) (m := m) (n := n) μ hLSI hs hsCut hM2
    simpa [s, ν, Nat.cast_add, Nat.cast_one, mul_assoc, mul_left_comm,
      mul_comm] using hnorm.2
  have hLog := smoothDataset_logPartitionLog_centered_positive_b
    (k := k) (m := m) (n := n) μ hM2 f hf
    (B := A) (C := C) (a := aj) (b := b)
    hA hBound hC hAj hb hSlopeG
    (smoothExpTiltedTest_hProductLSI (k := k) (m := m) (n := n)
      μ hLSI hA hM2 f hf hAj hb.le hBound hSlopeG)
    hNormExp hNormMGF ht
  have hDataLin := centeredExp_lintegral_le_of_logPartitionLog
    (ν := ν) (f := G.1) (lam := t) (B := A)
    (R := 2 * C * (aj ^ 2 + 2 * b ^ 2 * (n + 1) *
      (∫ z : Observation (k + 1) (m + 1), observationNormSq z ∂μ)) * t ^ 2)
    (by
      change Measurable (fun D : DataCarrier k m n =>
        f (datasetToEuclidean D))
      exact hf.continuous.measurable.comp measurable_datasetToEuclidean)
    hA hBound (by simpa [G, ν, aj, η] using hLog)
  have hTransport := centeredExp_lintegral_flattened_eq
    (k := k + 1) (m := m + 1) (n := n + 1) μ f t
  calc
    _ = ∫⁻ D, ENNReal.ofReal (Real.exp
        (t * (f (datasetToEuclidean D) -
          ∫ E, f (datasetToEuclidean E) ∂datasetProductLaw
            (k := k + 1) (m := m + 1) (n := n + 1) μ)))
        ∂datasetProductLaw (k := k + 1) (m := m + 1) (n := n + 1) μ := hTransport
    _ ≤ _ := by
      simpa [G, f, smoothDatasetPullback, ν, datasetProductLaw,
        aj, η, Nat.cast_add, Nat.cast_one] using hDataLin

/-- Actual mollifier exponential bound in the bounded-gradient case, from the
same one-observation LSI. This handles every real parameter, including zero. -/
theorem generalQuadraticMollifier_centeredExp_lintegral_bounded_gradient
    {k m n : ℕ} (μ : Measure (Observation (k + 1) (m + 1)))
    [IsProbabilityMeasure μ] (hM2 : Integrable observationNormSq μ)
    (F : LocallyLipschitzDataFunction k m n) {a C A : ℝ}
    (ha : 0 ≤ a) (hLSI : HasLogSobolev μ C)
    (hSlope : ∀ D, datasetLocalSlope F D ≤ a)
    (hA : 0 ≤ A) (j : ℕ) (t : ℝ) :
    ∫⁻ x, ENNReal.ofReal (Real.exp
      (t * (generalQuadraticMollifier F A j x -
        ∫ y, generalQuadraticMollifier F A j y ∂flattenedDatasetProductLaw
          (k := k + 1) (m := m + 1) (n := n + 1) μ)))
      ∂flattenedDatasetProductLaw (k := k + 1) (m := m + 1) (n := n + 1) μ ≤
    ENNReal.ofReal (Real.exp (C * a ^ 2 / 2 * t ^ 2)) := by
  have hC : 0 < C := hLSI.1
  have hSlope' : ∀ D, datasetLocalSlope F D ≤ a + 0 * datasetNorm D := by
    intro D
    simpa using hSlope D
  let f := generalQuadraticMollifier F A j
  let hf := generalQuadraticMollifier_contDiff F (A := A) ha
    (show 0 ≤ (0 : ℝ) by norm_num) hSlope' j
  let G := smoothDatasetPullback f hf
  let ν : Measure (DataCarrier k m n) := Measure.pi fun _ : Fin (n + 1) => μ
  have hBound : ∀ D : DataCarrier k m n, |G.1 D| ≤ A := by
    intro D
    have hrange := generalQuadraticMollifier_mem_Icc F ha (show 0 ≤ (0 : ℝ) by norm_num)
      hSlope' hA j (datasetToEuclidean D)
    apply abs_le.mpr
    simpa [G, f, smoothDatasetPullback] using hrange
  have hSlopeG : ∀ D : DataCarrier k m n, datasetLocalSlope G D ≤ a := by
    intro D
    simpa [G, f, hf] using
      (generalQuadraticMollifier_localSlope_bound F ha
        (show 0 ≤ (0 : ℝ) by norm_num) hSlope' j D)
  have hSlopeG' : ∀ D : DataCarrier k m n,
      datasetLocalSlope G D ≤ a + 0 * datasetNorm D := by
    intro D
    simpa [G] using hSlopeG D
  have hLog := smoothDataset_logPartitionLog_centered_bounded_gradient
    (k := k) (m := m) (n := n) μ hM2 f hf (B := A) (C := C) (a := a)
    hA hBound hC ha hSlopeG
    (smoothExpTiltedTest_hProductLSI (k := k) (m := m) (n := n)
      μ hLSI hA hM2 f hf ha (show 0 ≤ (0 : ℝ) by norm_num) hBound hSlopeG')
    t
  have hDataLin := centeredExp_lintegral_le_of_logPartitionLog
    (ν := ν) (f := G.1) (lam := t) (B := A)
    (R := C * a ^ 2 / 2 * t ^ 2)
    (by
      change Measurable (fun D : DataCarrier k m n =>
        f (datasetToEuclidean D))
      exact hf.continuous.measurable.comp measurable_datasetToEuclidean)
    hA hBound (by simpa [G, ν] using hLog)
  have hTransport := centeredExp_lintegral_flattened_eq
    (k := k + 1) (m := m + 1) (n := n + 1) μ f t
  calc
    _ = ∫⁻ D, ENNReal.ofReal (Real.exp
        (t * (f (datasetToEuclidean D) -
          ∫ E, f (datasetToEuclidean E) ∂datasetProductLaw
            (k := k + 1) (m := m + 1) (n := n + 1) μ)))
        ∂datasetProductLaw (k := k + 1) (m := m + 1) (n := n + 1) μ := hTransport
    _ ≤ _ := by
      simpa [G, f, smoothDatasetPullback, ν, datasetProductLaw] using hDataLin

/-- The positive-growth cap envelope is uniform in the cap. Its mollifier
index dependence is exactly the source coefficient `a + b η_j`; the limit
uses `η_j → 0`. -/
theorem generalQuadratic_centeredExp_lintegral_positive_b
    {k m n : ℕ} (μ : Measure (Observation (k + 1) (m + 1)))
    [IsProbabilityMeasure μ] (hM2 : Integrable observationNormSq μ)
    (F : LocallyLipschitzDataFunction k m n) {a b C : ℝ}
    (ha : 0 ≤ a) (hb : 0 < b) (hLSI : HasLogSobolev μ C)
    (hSlope : ∀ D, datasetLocalSlope F D ≤ a + b * datasetNorm D)
    {t : ℝ} (ht : |t| ≤ 1 / (4 * C * b)) :
    ∫⁻ D : DataCarrier k m n, ENNReal.ofReal (Real.exp
      (t * (F.1 D - ∫ E : DataCarrier k m n, F.1 E ∂datasetProductLaw
        (k := k + 1) (m := m + 1) (n := n + 1) μ)))
      ∂datasetProductLaw (k := k + 1) (m := m + 1) (n := n + 1) μ ≤
    ENNReal.ofReal (Real.exp
      (2 * C * (a ^ 2 + 2 * b ^ 2 * (n + 1) *
        (∫ z : Observation (k + 1) (m + 1), observationNormSq z ∂μ)) * t ^ 2)) := by
  have hC : 0 < C := hLSI.1
  let M : ℝ := ∫ z : Observation (k + 1) (m + 1), observationNormSq z ∂μ
  let K : ℝ := 2 * b ^ 2 * (n + 1) * M
  let B : ℕ → ENNReal := fun j => ENNReal.ofReal (Real.exp
    (2 * C * ((a + b * datasetMollifierScale j) ^ 2 + K) * t ^ 2))
  let Blim : ENNReal := ENNReal.ofReal (Real.exp (2 * C * (a ^ 2 + K) * t ^ 2))
  have hScale : Tendsto datasetMollifierScale atTop (𝓝 (0 : ℝ)) :=
    datasetMollifierScale_tendsto.mono_right nhdsWithin_le_nhds
  have hLinear : Tendsto
      (fun j : ℕ => a + b * datasetMollifierScale j) atTop (𝓝 a) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hScale)
  have hSquare : Tendsto
      (fun j : ℕ => (a + b * datasetMollifierScale j) ^ 2) atTop (𝓝 (a ^ 2)) := by
    simpa using hLinear.pow 2
  have hExponent : Tendsto
      (fun j : ℕ => 2 * C * ((a + b * datasetMollifierScale j) ^ 2 + K) * t ^ 2)
      atTop (𝓝 (2 * C * (a ^ 2 + K) * t ^ 2)) := by
    have hsum := hSquare.add
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => K) atTop (𝓝 K))
    have hconst : Tendsto (fun _ : ℕ => 2 * C) atTop (𝓝 (2 * C)) :=
      tendsto_const_nhds
    have hprod := hconst.mul hsum
    have hprod' := hprod.mul
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => t ^ 2) atTop (𝓝 (t ^ 2)))
    simpa [mul_assoc] using hprod'
  have hB : Tendsto B atTop (𝓝 Blim) := by
    have hcont : Continuous (fun r : ℝ => ENNReal.ofReal (Real.exp r)) :=
      ENNReal.continuous_ofReal.comp Real.continuous_exp
    exact (hcont.continuousAt.tendsto.comp hExponent)
  have hSmooth : ∀ A : ℝ, 0 ≤ A → ∀ j : ℕ,
      ∫⁻ x, ENNReal.ofReal (Real.exp (t *
        (datasetClipThenMollify F.1 A (datasetMollifierScale j) x -
          ∫ y, datasetClipThenMollify F.1 A (datasetMollifierScale j) y
            ∂flattenedDatasetProductLaw μ))) ∂flattenedDatasetProductLaw μ ≤ B j := by
    intro A hA j
    have h := generalQuadraticMollifier_centeredExp_lintegral_positive_b
      μ hM2 F ha hb hLSI hSlope hA j ht
    simpa [B, K, M, generalQuadraticMollifier,
      Nat.cast_add, Nat.cast_one] using h
  have hEuclidean := centeredExp_locallyLipschitz_productLaw_bound
    μ hM2 F ha hb.le hSlope B Blim hSmooth hB
  let f : EuclideanSpace ℝ (DatasetCoordinate (k + 1) (m + 1) (n + 1)) → ℝ :=
    fun x => F.1 (datasetFromEuclidean x)
  have hTransport := centeredExp_lintegral_flattened_eq
    (k := k + 1) (m := m + 1) (n := n + 1) μ f t
  calc
    _ = ∫⁻ x, ENNReal.ofReal (Real.exp
        (t * (f x - ∫ y, f y ∂flattenedDatasetProductLaw
          (k := k + 1) (m := m + 1) (n := n + 1) μ)))
        ∂flattenedDatasetProductLaw (k := k + 1) (m := m + 1) (n := n + 1) μ := by
      simpa [f, datasetFromEuclidean_toEuclidean] using hTransport.symm
    _ ≤ Blim := by
      simpa [f, Blim, K, M] using hEuclidean
    _ = _ := by rfl

/-- The bounded-gradient cap envelope is constant in both the cap and
mollifier index, so its limit transfers directly. -/
theorem generalQuadratic_centeredExp_lintegral_bounded_gradient
    {k m n : ℕ} (μ : Measure (Observation (k + 1) (m + 1)))
    [IsProbabilityMeasure μ] (hM2 : Integrable observationNormSq μ)
    (F : LocallyLipschitzDataFunction k m n) {a C : ℝ}
    (ha : 0 ≤ a) (hLSI : HasLogSobolev μ C)
    (hSlope : ∀ D, datasetLocalSlope F D ≤ a)
    (t : ℝ) :
    ∫⁻ D : DataCarrier k m n, ENNReal.ofReal (Real.exp
      (t * (F.1 D - ∫ E : DataCarrier k m n, F.1 E ∂datasetProductLaw
        (k := k + 1) (m := m + 1) (n := n + 1) μ)))
      ∂datasetProductLaw (k := k + 1) (m := m + 1) (n := n + 1) μ ≤
    ENNReal.ofReal (Real.exp (C * a ^ 2 / 2 * t ^ 2)) := by
  have hC : 0 < C := hLSI.1
  let R : ℝ := C * a ^ 2 / 2 * t ^ 2
  let B : ℕ → ENNReal := fun _ => ENNReal.ofReal (Real.exp R)
  have hB : Tendsto B atTop (𝓝 (ENNReal.ofReal (Real.exp R))) := by
    exact tendsto_const_nhds
  have hSmooth : ∀ A : ℝ, 0 ≤ A → ∀ j : ℕ,
      ∫⁻ x, ENNReal.ofReal (Real.exp (t *
        (datasetClipThenMollify F.1 A (datasetMollifierScale j) x -
          ∫ y, datasetClipThenMollify F.1 A (datasetMollifierScale j) y
            ∂flattenedDatasetProductLaw μ))) ∂flattenedDatasetProductLaw μ ≤ B j := by
    intro A hA j
    have h := generalQuadraticMollifier_centeredExp_lintegral_bounded_gradient
      μ hM2 F ha hLSI hSlope hA j t
    simpa [B, R, generalQuadraticMollifier] using h
  have hEuclidean := centeredExp_locallyLipschitz_productLaw_bound
    μ hM2 F ha (show 0 ≤ (0 : ℝ) by norm_num) (by
      intro D
      simpa using hSlope D) B (ENNReal.ofReal (Real.exp R)) hSmooth hB
  let f : EuclideanSpace ℝ (DatasetCoordinate (k + 1) (m + 1) (n + 1)) → ℝ :=
    fun x => F.1 (datasetFromEuclidean x)
  have hTransport := centeredExp_lintegral_flattened_eq
    (k := k + 1) (m := m + 1) (n := n + 1) μ f t
  calc
    _ = ∫⁻ x, ENNReal.ofReal (Real.exp
        (t * (f x - ∫ y, f y ∂flattenedDatasetProductLaw
          (k := k + 1) (m := m + 1) (n := n + 1) μ)))
        ∂flattenedDatasetProductLaw (k := k + 1) (m := m + 1) (n := n + 1) μ := by
      simpa [f, datasetFromEuclidean_toEuclidean] using hTransport.symm
    _ ≤ ENNReal.ofReal (Real.exp R) := by
      simpa [f, R] using hEuclidean
    _ = _ := by rfl

private theorem centeredExp_integrable_integral_log_of_lintegral_le
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    (g : Ω → ℝ) (hg : Measurable g) (R : ℝ)
    (hLin : ∫⁻ x, ENNReal.ofReal (Real.exp (g x)) ∂ν ≤
      ENNReal.ofReal (Real.exp R)) :
    Integrable (fun x => Real.exp (g x)) ν ∧
      (∫ x, Real.exp (g x) ∂ν ≤ Real.exp R) ∧
      Real.log (∫ x, Real.exp (g x) ∂ν) ≤ R := by
  have hExpMeas : Measurable (fun x => Real.exp (g x)) := Real.measurable_exp.comp hg
  have hFinite : ∫⁻ x, ENNReal.ofReal (Real.exp (g x)) ∂ν ≠ (⊤ : ENNReal) := by
    apply ne_of_lt
    calc
      ∫⁻ x, ENNReal.ofReal (Real.exp (g x)) ∂ν ≤
          ENNReal.ofReal (Real.exp R) := hLin
      _ < (⊤ : ENNReal) := ENNReal.ofReal_lt_top
  have hInt : Integrable (fun x => Real.exp (g x)) ν :=
    (lintegral_ofReal_ne_top_iff_integrable
      hExpMeas.aestronglyMeasurable
      (ae_of_all _ fun x => (Real.exp_nonneg (g x)))).mp hFinite
  have hRealBound : ∫ x, Real.exp (g x) ∂ν ≤ Real.exp R := by
    apply (ENNReal.ofReal_le_ofReal_iff (Real.exp_nonneg R)).mp
    rw [ofReal_integral_eq_lintegral_ofReal hInt
      (ae_of_all _ fun x => (Real.exp_nonneg (g x)))]
    exact hLin
  have hpos : 0 < ∫ x, Real.exp (g x) ∂ν := integral_exp_pos hInt
  exact ⟨hInt, hRealBound, (Real.log_le_iff_le_exp hpos).2 hRealBound⟩

/-- Positive-growth one-observation LSI gives the actual centered MGF,
integrability, integral bound, and log bound under the original product law. -/
theorem generalQuadratic_centeredExp_integral_log_positive_b
    {k m n : ℕ} (μ : Measure (Observation (k + 1) (m + 1)))
    [IsProbabilityMeasure μ] (hM2 : Integrable observationNormSq μ)
    (F : LocallyLipschitzDataFunction k m n) {a b C : ℝ}
    (ha : 0 ≤ a) (hb : 0 < b) (hLSI : HasLogSobolev μ C)
    (hSlope : ∀ D, datasetLocalSlope F D ≤ a + b * datasetNorm D)
    {t : ℝ} (ht : |t| ≤ 1 / (4 * C * b)) :
    Integrable (fun D : DataCarrier k m n => Real.exp
      (t * (F.1 D - ∫ E : DataCarrier k m n, F.1 E ∂datasetProductLaw
        (k := k + 1) (m := m + 1) (n := n + 1) μ)))
      (datasetProductLaw (k := k + 1) (m := m + 1) (n := n + 1) μ) ∧
    (∫ D : DataCarrier k m n, Real.exp
      (t * (F.1 D - ∫ E : DataCarrier k m n, F.1 E ∂datasetProductLaw
        (k := k + 1) (m := m + 1) (n := n + 1) μ))
      ∂datasetProductLaw (k := k + 1) (m := m + 1) (n := n + 1) μ ≤
      Real.exp (2 * C * (a ^ 2 + 2 * b ^ 2 * (n + 1) *
        (∫ z : Observation (k + 1) (m + 1), observationNormSq z ∂μ)) * t ^ 2)) ∧
    Real.log (∫ D : DataCarrier k m n, Real.exp
      (t * (F.1 D - ∫ E : DataCarrier k m n, F.1 E ∂datasetProductLaw
        (k := k + 1) (m := m + 1) (n := n + 1) μ))
      ∂datasetProductLaw (k := k + 1) (m := m + 1) (n := n + 1) μ) ≤
      2 * C * (a ^ 2 + 2 * b ^ 2 * (n + 1) *
        (∫ z : Observation (k + 1) (m + 1), observationNormSq z ∂μ)) * t ^ 2 := by
  let ν : Measure (DataCarrier k m n) :=
    datasetProductLaw (k := k + 1) (m := m + 1) (n := n + 1) μ
  let mean : ℝ := ∫ E : DataCarrier k m n, F.1 E ∂ν
  let g : DataCarrier k m n → ℝ := fun D => t * (F.1 D - mean)
  have hseg := generalQuadratic_segment_bound F ha hb.le hSlope
  have hcont := continuous_datasetFunction_of_segmentBound hseg ha hb.le
  have hFmeas : Measurable F.1 := by
    change Measurable ((fun x : EuclideanSpace ℝ
      (DatasetCoordinate (k + 1) (m + 1) (n + 1)) => F.1 (datasetFromEuclidean x)) ∘
        datasetToEuclidean)
    exact hcont.measurable.comp measurable_datasetToEuclidean
  have hg : Measurable g := by
    exact measurable_const.mul (hFmeas.sub_const mean)
  have hLin := generalQuadratic_centeredExp_lintegral_positive_b
    μ hM2 F ha hb hLSI hSlope ht
  have hFacts := centeredExp_integrable_integral_log_of_lintegral_le g hg
    (2 * C * (a ^ 2 + 2 * b ^ 2 * (n + 1) *
      (∫ z : Observation (k + 1) (m + 1), observationNormSq z ∂μ)) * t ^ 2)
    (by simpa [ν, g, mean, datasetProductLaw] using hLin)
  simpa [ν, g, mean, datasetProductLaw] using hFacts

/-- Bounded-gradient one-observation LSI gives the all-real-parameter centered
MGF, integrability, integral bound, and log bound under the product law. -/
theorem generalQuadratic_centeredExp_integral_log_bounded_gradient
    {k m n : ℕ} (μ : Measure (Observation (k + 1) (m + 1)))
    [IsProbabilityMeasure μ] (hM2 : Integrable observationNormSq μ)
    (F : LocallyLipschitzDataFunction k m n) {a C : ℝ}
    (ha : 0 ≤ a) (hLSI : HasLogSobolev μ C)
    (hSlope : ∀ D, datasetLocalSlope F D ≤ a) (t : ℝ) :
    Integrable (fun D : DataCarrier k m n => Real.exp
      (t * (F.1 D - ∫ E : DataCarrier k m n, F.1 E ∂datasetProductLaw
        (k := k + 1) (m := m + 1) (n := n + 1) μ)))
      (datasetProductLaw (k := k + 1) (m := m + 1) (n := n + 1) μ) ∧
    (∫ D : DataCarrier k m n, Real.exp
      (t * (F.1 D - ∫ E : DataCarrier k m n, F.1 E ∂datasetProductLaw
        (k := k + 1) (m := m + 1) (n := n + 1) μ))
      ∂datasetProductLaw (k := k + 1) (m := m + 1) (n := n + 1) μ ≤
      Real.exp (C * a ^ 2 / 2 * t ^ 2)) ∧
    Real.log (∫ D : DataCarrier k m n, Real.exp
      (t * (F.1 D - ∫ E : DataCarrier k m n, F.1 E ∂datasetProductLaw
        (k := k + 1) (m := m + 1) (n := n + 1) μ))
      ∂datasetProductLaw (k := k + 1) (m := m + 1) (n := n + 1) μ) ≤
      C * a ^ 2 / 2 * t ^ 2 := by
  let ν : Measure (DataCarrier k m n) :=
    datasetProductLaw (k := k + 1) (m := m + 1) (n := n + 1) μ
  let mean : ℝ := ∫ E : DataCarrier k m n, F.1 E ∂ν
  let g : DataCarrier k m n → ℝ := fun D => t * (F.1 D - mean)
  have hseg := generalQuadratic_segment_bound F ha (show 0 ≤ (0 : ℝ) by norm_num)
    (by intro D; simpa using hSlope D)
  have hcont := continuous_datasetFunction_of_segmentBound hseg ha
    (show 0 ≤ (0 : ℝ) by norm_num)
  have hFmeas : Measurable F.1 := by
    change Measurable ((fun x : EuclideanSpace ℝ
      (DatasetCoordinate (k + 1) (m + 1) (n + 1)) => F.1 (datasetFromEuclidean x)) ∘
        datasetToEuclidean)
    exact hcont.measurable.comp measurable_datasetToEuclidean
  have hg : Measurable g := by
    exact measurable_const.mul (hFmeas.sub_const mean)
  have hLin := generalQuadratic_centeredExp_lintegral_bounded_gradient
    μ hM2 F ha hLSI hSlope t
  have hFacts := centeredExp_integrable_integral_log_of_lintegral_le g hg
    (C * a ^ 2 / 2 * t ^ 2) (by simpa [ν, g, mean, datasetProductLaw] using hLin)
  simpa [ν, g, mean, datasetProductLaw] using hFacts

#print axioms generalQuadratic_centeredExp_integral_log_positive_b
#print axioms generalQuadratic_centeredExp_integral_log_bounded_gradient

end

end LOOConcentration
