import LOOConcentrationManuscript.Internal.RidgeFeatureFourthMoments
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal

open MeasureTheory ProbabilityTheory
noncomputable section

private theorem ridge_four_square_sum (a b c d : ℝ) :
    (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d),
    sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]

/-- The source envelope for the literal Ridge add-one slope update belongs to
`L²` under the actual training-sample and added-observation law. Its squared
integral is controlled by the source fourth feature moment. -/
theorem ridge_actual_add_one_envelope_memLp_two
    (μ : Measure (LOOConcentration.Observation 1 1)) [IsProbabilityMeasure μ]
    (hX4 : Integrable (fun z => (z.1 0) ^ 4) μ) (r : ℕ) :
    let N : ℝ := ((r + 1 : ℕ) : ℝ)
    let a := fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) =>
      (∑ i : Fin (r + 1), (D i).1 0) / N
    let v := fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) =>
      (∑ i : Fin (r + 1), ((D i).1 0 - a D) ^ 2) / N
    let Q := (Measure.pi fun _ : Fin (r + 1) => μ).prod μ
    let d := fun q : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) ×
        LOOConcentration.Observation 1 1 => (q.2).1 0 - a q.1
    let E := fun q => Real.sqrt (v q.1) + |d q| + v q.1 + (d q) ^ 2
    MemLp E 2 Q ∧
      (∫ q, (E q) ^ 2 ∂Q) ≤
        8 + 136 * (∫ z, (z.1 0) ^ 4 ∂μ) := by
  classical
  intro N a v Q d E
  have hMom := ridge_actual_add_one_feature_moments μ hX4 r
  have hV2 : Integrable (fun q : (LOOConcentration.Dataset
      (LOOConcentration.Observation 1 1) (r + 1)) × LOOConcentration.Observation 1 1 =>
      (v q.1) ^ 2) Q := by simpa only [v, a, N, Q] using hMom.1
  have hV2Bound : (∫ q, (v q.1) ^ 2 ∂Q) ≤ ∫ z, (z.1 0) ^ 4 ∂μ := by
    simpa only [v, a, N, Q] using hMom.2.1
  have hD4 : Integrable (fun q : (LOOConcentration.Dataset
      (LOOConcentration.Observation 1 1) (r + 1)) × LOOConcentration.Observation 1 1 =>
      (d q) ^ 4) Q := by simpa only [d, a, N, Q] using hMom.2.2.1
  have hD4Bound : (∫ q, (d q) ^ 4 ∂Q) ≤
      16 * (∫ z, (z.1 0) ^ 4 ∂μ) := by
    simpa only [d, a, N, Q] using hMom.2.2.2
  have hv0 (q : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) ×
      LOOConcentration.Observation 1 1) : 0 ≤ v q.1 := by
    dsimp [v, a, N]
    positivity
  have hEnvelopeSq : ∀ q : LOOConcentration.Dataset
      (LOOConcentration.Observation 1 1) (r + 1) × LOOConcentration.Observation 1 1,
      (E q) ^ 2 ≤ 8 + 8 * (v q.1) ^ 2 + 8 * (d q) ^ 4 := by
    intro q
    have hVle : v q.1 ≤ 1 + (v q.1) ^ 2 := by
      nlinarith [sq_nonneg (v q.1 - (1 / 2 : ℝ))]
    have hD2le : (d q) ^ 2 ≤ 1 + (d q) ^ 4 := by
      nlinarith [sq_nonneg ((d q) ^ 2 - (1 / 2 : ℝ))]
    have hSumSq := ridge_four_square_sum (Real.sqrt (v q.1)) (|d q|)
      (v q.1) ((d q) ^ 2)
    change (E q) ^ 2 ≤ _ at hSumSq
    have hRewrite : (Real.sqrt (v q.1)) ^ 2 = v q.1 := Real.sq_sqrt (hv0 q)
    have hAbs : |d q| ^ 2 = (d q) ^ 2 := sq_abs _
    rw [hRewrite, hAbs] at hSumSq
    nlinarith [hVle, hD2le]
  have hMajorant : Integrable
      (fun q : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) ×
        LOOConcentration.Observation 1 1 => 8 + 8 * (v q.1) ^ 2 + 8 * (d q) ^ 4) Q := by
    have hConst : Integrable (fun _ : LOOConcentration.Dataset
        (LOOConcentration.Observation 1 1) (r + 1) × LOOConcentration.Observation 1 1 =>
        (8 : ℝ)) Q := integrable_const 8
    have hEq : (fun q : LOOConcentration.Dataset (LOOConcentration.Observation 1 1)
        (r + 1) × LOOConcentration.Observation 1 1 =>
          8 + 8 * (v q.1) ^ 2 + 8 * (d q) ^ 4) =
        (fun _ => (8 : ℝ)) +
          ((fun q => 8 * (v q.1) ^ 2) + (fun q => 8 * (d q) ^ 4)) := by
      funext q
      simp only [Pi.add_apply]
      ring
    rw [hEq]
    exact hConst.add ((hV2.const_mul 8).add (hD4.const_mul 8))
  have hESq : Integrable (fun q => (E q) ^ 2) Q := by
    apply hMajorant.mono' (by fun_prop)
    filter_upwards with q
    calc
      ‖(E q) ^ 2‖ = (E q) ^ 2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (E q))]
      _ ≤ 8 + 8 * (v q.1) ^ 2 + 8 * (d q) ^ 4 := hEnvelopeSq q
  have hE : MemLp E 2 Q := (memLp_two_iff_integrable_sq (by fun_prop)).2 hESq
  refine ⟨hE, ?_⟩
  calc
    _ ≤ ∫ q : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) ×
        LOOConcentration.Observation 1 1,
        8 + 8 * (v q.1) ^ 2 + 8 * (d q) ^ 4 ∂Q :=
      integral_mono hESq hMajorant hEnvelopeSq
    _ = 8 + 8 * (∫ q, (v q.1) ^ 2 ∂Q) + 8 * (∫ q, (d q) ^ 4 ∂Q) := by
      have hSumInt : Integrable (fun q : LOOConcentration.Dataset
          (LOOConcentration.Observation 1 1) (r + 1) × LOOConcentration.Observation 1 1 =>
          8 * (v q.1) ^ 2 + 8 * (d q) ^ 4) Q := by
        change Integrable ((fun q => 8 * (v q.1) ^ 2) + (fun q => 8 * (d q) ^ 4)) Q
        exact (hV2.const_mul 8).add (hD4.const_mul 8)
      calc
        _ = ∫ q, (8 : ℝ) + (8 * (v q.1) ^ 2 + 8 * (d q) ^ 4) ∂Q := by
          congr 1
          funext q
          ring
        _ = (∫ q, (8 : ℝ) ∂Q) +
            (∫ q, 8 * (v q.1) ^ 2 + 8 * (d q) ^ 4 ∂Q) :=
          integral_add (integrable_const 8) hSumInt
        _ = 8 + 8 * (∫ q, (v q.1) ^ 2 ∂Q) + 8 * (∫ q, (d q) ^ 4 ∂Q) := by
          rw [integral_add (hV2.const_mul 8) (hD4.const_mul 8),
            integral_const_mul, integral_const_mul, integral_const]
          simp [Q]
          ring
    _ ≤ 8 + 136 * (∫ z, (z.1 0) ^ 4 ∂μ) := by nlinarith [hV2Bound, hD4Bound]

/-- The public predictor's query slope, read from the actual fitted function. -/
noncomputable def ridgeActualPublicSlope
    (b δ : {t : ℝ // 0 < t}) (r : ℕ)
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1)) : ℝ :=
  ((LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r D)
      (fun _ : Fin 1 => 1)) 0 -
    ((LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r D)
      (fun _ : Fin 1 => 0)) 0

/-- The empirical formula certified for the public predictor's query slope. -/
private noncomputable def ridgeSourceSlopeCoefficient
    (b δ : {t : ℝ // 0 < t}) (r : ℕ)
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1)) : ℝ :=
  let N : ℝ := ((r + 1 : ℕ) : ℝ)
  let X := LOOConcentrationManuscript.featureValues D
  let U := LOOConcentrationManuscript.clippedResponseValues D b.val
  let a : ℝ := (∑ i : Fin (r + 1), X i) / N
  let c : ℝ := (∑ i : Fin (r + 1), U i) / N
  let v : ℝ := (∑ i : Fin (r + 1), (X i - a) ^ 2) / N
  let s : ℝ := (∑ i : Fin (r + 1), (X i - a) * (U i - c)) / N
  s / (v + δ.val)

private theorem ridge_source_slope_coefficient_measurable
    (b δ : {t : ℝ // 0 < t}) (r : ℕ) :
    Measurable (ridgeSourceSlopeCoefficient b δ r) := by
  let N : ℝ := ((r + 1 : ℕ) : ℝ)
  let X : (Fin (r + 1) → LOOConcentration.Observation 1 1) → Fin (r + 1) → ℝ :=
    fun D i => (D i).1 0
  let U : (Fin (r + 1) → LOOConcentration.Observation 1 1) → Fin (r + 1) → ℝ :=
    fun D i => LOOConcentration.Manuscript.coordinateClip ⟨b.val, b.property.le⟩ ((D i).2 0)
  let a : (Fin (r + 1) → LOOConcentration.Observation 1 1) → ℝ :=
    fun D => (∑ i : Fin (r + 1), X D i) / N
  let c : (Fin (r + 1) → LOOConcentration.Observation 1 1) → ℝ :=
    fun D => (∑ i : Fin (r + 1), U D i) / N
  let v : (Fin (r + 1) → LOOConcentration.Observation 1 1) → ℝ :=
    fun D => (∑ i : Fin (r + 1), (X D i - a D) ^ 2) / N
  let s : (Fin (r + 1) → LOOConcentration.Observation 1 1) → ℝ :=
    fun D => (∑ i : Fin (r + 1), (X D i - a D) * (U D i - c D)) / N
  change Measurable (fun D => s D / (v D + δ.val))
  have ha : Measurable a := by
    dsimp [a, X]
    fun_prop
  have hc : Measurable c := by
    dsimp [c, U]
    fun_prop [LOOConcentration.Manuscript.coordinateClip]
  have hv : Measurable v := by
    dsimp [v, X]
    fun_prop
  have hs : Measurable s := by
    dsimp [s, X, U]
    fun_prop [LOOConcentration.Manuscript.coordinateClip]
  exact hs.div (hv.add measurable_const)

theorem ridge_actual_public_predictor_eval_formula (r : ℕ)
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1))
    (b δ : {t : ℝ // 0 < t}) (x : ℝ) :
    let N : ℝ := ((r + 1 : ℕ) : ℝ)
    let X := LOOConcentrationManuscript.featureValues D
    let U := LOOConcentrationManuscript.clippedResponseValues D b.val
    let a : ℝ := (∑ i : Fin (r + 1), X i) / N
    let c : ℝ := (∑ i : Fin (r + 1), U i) / N
    let v : ℝ := (∑ i : Fin (r + 1), (X i - a) ^ 2) / N
    let s : ℝ := (∑ i : Fin (r + 1), (X i - a) * (U i - c)) / N
    let ybar : ℝ := (∑ i : Fin (r + 1), (D i).2 0) / N
    let beta : ℝ := s / (v + δ.val)
    ((LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r D)
      (fun _ : Fin 1 => x)) 0 = ybar + beta * (x - a) := by
  classical
  simp [LOOConcentration.Manuscript.stabilizedLinearEstimator,
    LOOConcentrationManuscript.featureValues,
    LOOConcentrationManuscript.clippedResponseValues]
  field_simp

/-- The slope read from the public estimator is exactly its clipped empirical
covariance divided by the regularized feature variance. -/
theorem ridge_actual_public_slope_eq_source_formula
    (b δ : {t : ℝ // 0 < t}) (r : ℕ)
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1)) :
    ridgeActualPublicSlope b δ r D = ridgeSourceSlopeCoefficient b δ r D := by
  have hOne := ridge_actual_public_predictor_eval_formula r D b δ 1
  have hZero := ridge_actual_public_predictor_eval_formula r D b δ 0
  dsimp [ridgeActualPublicSlope]
  rw [hOne, hZero]
  dsimp [ridgeSourceSlopeCoefficient]
  ring

/-- The actual public Ridge query-slope increment has an L² bound of order
`1/(r+2)`. The source empirical slope formula is identified internally with
the difference of the public predictor at queries one and zero. -/
theorem ridge_actual_add_one_public_slope_difference_L2
    (μ : Measure (LOOConcentration.Observation 1 1)) [IsProbabilityMeasure μ]
    (hX4 : Integrable (fun z => (z.1 0) ^ 4) μ)
    (b δ : {t : ℝ // 0 < t}) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ,
      let N : ℝ := (r + 1 : ℝ)
      let Q := (Measure.pi fun _ : Fin (r + 1) => μ).prod μ
      let slopeDiff := fun q : LOOConcentration.Dataset
          (LOOConcentration.Observation 1 1) (r + 1) × LOOConcentration.Observation 1 1 =>
        ridgeActualPublicSlope b δ (r + 1) (Fin.snoc q.1 q.2) -
          ridgeActualPublicSlope b δ r q.1
      MemLp slopeDiff 2 Q ∧
        (∫ q, (slopeDiff q) ^ 2 ∂Q) ≤ C / (N + 1) ^ 2 := by
  obtain ⟨C₀, hC₀, hPoint⟩ := ridge_actual_add_one_slope_bound b δ
  refine ⟨C₀ ^ 2 * (8 + 136 * (∫ z, (z.1 0) ^ 4 ∂μ)), ?_, ?_⟩
  · have hNonneg : 0 ≤ ∫ z, (z.1 0) ^ 4 ∂μ := integral_nonneg (fun z => by positivity)
    positivity
  · intro r N Q slopeDiff
    let a := fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) =>
      (∑ i : Fin (r + 1), (D i).1 0) / N
    let v := fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) =>
      (∑ i : Fin (r + 1), ((D i).1 0 - a D) ^ 2) / N
    let d := fun q : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) ×
        LOOConcentration.Observation 1 1 => (q.2).1 0 - a q.1
    let E := fun q => Real.sqrt (v q.1) + |d q| + v q.1 + (d q)^2
    have hSlopeDiffFormula : slopeDiff = fun q =>
        ridgeSourceSlopeCoefficient b δ (r + 1) (Fin.snoc q.1 q.2) -
          ridgeSourceSlopeCoefficient b δ r q.1 := by
      funext q
      dsimp [slopeDiff]
      rw [ridge_actual_public_slope_eq_source_formula,
        ridge_actual_public_slope_eq_source_formula]
    have hEnv := ridge_actual_add_one_envelope_memLp_two μ hX4 r
    have hEnvMem : MemLp E 2 Q := by
      simpa only [E, d, v, a, N, Q, Nat.cast_add, Nat.cast_one] using hEnv.1
    have hEnvBound : (∫ q, (E q)^2 ∂Q) ≤
        8 + 136 * (∫ z, (z.1 0)^4 ∂μ) := by
      simpa only [E, d, v, a, N, Q, Nat.cast_add, Nat.cast_one] using hEnv.2
    have hPointwise (q : LOOConcentration.Dataset
        (LOOConcentration.Observation 1 1) (r + 1) × LOOConcentration.Observation 1 1) :
        |slopeDiff q| ≤ C₀ / (N + 1) * E q := by
      have h := hPoint r q.1 q.2
      simp only [LOOConcentration.Manuscript.coordinateClip] at h
      have hNew := ridge_actual_public_slope_eq_source_formula b δ (r + 1)
        (Fin.snoc q.1 q.2)
      have hOld := ridge_actual_public_slope_eq_source_formula b δ r q.1
      dsimp [slopeDiff]
      rw [hNew, hOld]
      simpa only [E, d, v, a, N, Q, ridgeSourceSlopeCoefficient,
        LOOConcentrationManuscript.featureValues,
        LOOConcentrationManuscript.clippedResponseValues, Nat.cast_add, Nat.cast_one] using h
    have hPointwiseSq (q : LOOConcentration.Dataset
        (LOOConcentration.Observation 1 1) (r + 1) × LOOConcentration.Observation 1 1) :
        (slopeDiff q)^2 ≤ (C₀^2 / (N + 1)^2) * (E q)^2 := by
      have hE : 0 ≤ E q := by dsimp [E]; positivity
      have hk : 0 ≤ C₀ / (N + 1) := by positivity
      have hSq := (sq_le_sq₀ (abs_nonneg (slopeDiff q)) (mul_nonneg hk hE)).2
        (hPointwise q)
      have hAbsSq : (slopeDiff q) ^ 2 ≤
          (C₀ / (N + 1) * E q) ^ 2 := by simpa only [sq_abs] using hSq
      calc
        _ ≤ (C₀ / (N + 1) * E q) ^ 2 := hAbsSq
        _ = (C₀ ^ 2 / (N + 1) ^ 2) * (E q) ^ 2 := by
          have hden : (N + 1) ≠ 0 := by positivity
          field_simp [hden]
    have hEnvSqInt : Integrable (fun q => (E q)^2) Q :=
      (memLp_two_iff_integrable_sq (by fun_prop)).1 hEnvMem
    have hMajorant : Integrable
        (fun q => (C₀^2 / (N + 1)^2) * (E q)^2) Q :=
      hEnvSqInt.const_mul (C₀^2 / (N + 1)^2)
    have hSlopeFormulaMeas : Measurable (fun q : LOOConcentration.Dataset
        (LOOConcentration.Observation 1 1) (r + 1) × LOOConcentration.Observation 1 1 =>
        ridgeSourceSlopeCoefficient b δ (r + 1) (Fin.snoc q.1 q.2) -
          ridgeSourceSlopeCoefficient b δ r q.1) := by
      have hNew := ridge_source_slope_coefficient_measurable b δ (r + 1)
      have hOld := ridge_source_slope_coefficient_measurable b δ r
      have hSnoc : Measurable (fun q : LOOConcentration.Dataset
          (LOOConcentration.Observation 1 1) (r + 1) × LOOConcentration.Observation 1 1 =>
          (Fin.snoc q.1 q.2 :
            LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 2))) := by
        apply measurable_pi_lambda
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa only [Fin.snoc_last] using measurable_snd
        · convert (measurable_pi_apply j).comp measurable_fst using 1
          funext q
          simp only [Fin.snoc_castSucc, Function.comp_apply]
      exact (hNew.comp hSnoc).sub (hOld.comp measurable_fst)
    have hSlopeSqInt : Integrable (fun q => (slopeDiff q)^2) Q := by
      apply hMajorant.mono' (by rw [hSlopeDiffFormula]; exact hSlopeFormulaMeas.pow_const 2 |>.aestronglyMeasurable)
      filter_upwards with q
      have hA0 : 0 ≤ (C₀ ^ 2 / (N + 1) ^ 2) * (E q) ^ 2 := by positivity
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (slopeDiff q)),
        abs_of_nonneg hA0] using hPointwiseSq q
    have hSlopeMem : MemLp slopeDiff 2 Q := by
      apply (memLp_two_iff_integrable_sq ?_).2 hSlopeSqInt
      rw [hSlopeDiffFormula]
      exact hSlopeFormulaMeas.aestronglyMeasurable
    refine ⟨hSlopeMem, ?_⟩
    calc
      _ ≤ ∫ q, (C₀^2 / (N + 1)^2) * (E q)^2 ∂Q :=
        integral_mono hSlopeSqInt hMajorant hPointwiseSq
      _ = (C₀^2 / (N + 1)^2) * (∫ q, (E q)^2 ∂Q) := by rw [integral_const_mul]
      _ ≤ (C₀^2 / (N + 1)^2) *
          (8 + 136 * (∫ z, (z.1 0)^4 ∂μ)) :=
        mul_le_mul_of_nonneg_left hEnvBound (by positivity)
      _ = (C₀^2 * (8 + 136 * (∫ z, (z.1 0)^4 ∂μ))) /
          (N + 1)^2 := by ring

end
end LOOConcentration.Manuscript.Internal
