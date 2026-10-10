import LOOConcentrationManuscript.Internal.RidgePredictorAbsoluteLossQueryConsumer
import LOOConcentrationManuscript.Frozen.Definitions.StabilizedLinearEstimator
import LOOConcentration.Frozen.Foundations.FittedLoss
import LOOConcentration.Geometry.NormTransport
import LOOConcentration.Geometry.SmoothObservationSlope
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Positivity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

/-!
Pointwise true-L1 and query regularity of the literal public stabilized ridge
estimator with its source absolute loss.
-/

namespace LOOConcentrationManuscript.Internal
open MeasureTheory ProbabilityTheory
noncomputable section

private abbrev ridgeAbsoluteLoss :
    LOOConcentration.Responses 1 → LOOConcentration.Responses 1 → ℝ :=
  fun u v => |u 0 - v 0|

private abbrev ridgeFeatureAbsMean (r : ℕ)
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1)) : ℝ :=
  (∑ i : Fin (r + 1), |(D i).1 0|) / (r + 1 : ℝ)

private abbrev ridgeResponseAbsMean (r : ℕ)
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1)) : ℝ :=
  (∑ i : Fin (r + 1), |(D i).2 0|) / (r + 1 : ℝ)

private theorem ridgeFeatureCoordinate_abs_integrable
    (μ : Measure (LOOConcentration.Observation 1 1)) [IsProbabilityMeasure μ]
    (hSecond : Integrable LOOConcentration.observationNormSq μ) :
    Integrable (fun z : LOOConcentration.Observation 1 1 => |z.1 0|) μ := by
  have hSq : Integrable (fun z : LOOConcentration.Observation 1 1 => (z.1 0) ^ 2) μ :=
    hSecond.mono' (by fun_prop) (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      simp only [LOOConcentration.observationNormSq, Fin.sum_univ_one]
      exact le_add_of_nonneg_right (sq_nonneg (z.2 0)))
  have hLp : MemLp (fun z : LOOConcentration.Observation 1 1 => z.1 0) 2 μ :=
    (memLp_two_iff_integrable_sq (by fun_prop)).2 hSq
  simpa only [Real.norm_eq_abs] using (hLp.integrable one_le_two).norm

private theorem ridgeResponseCoordinate_abs_integrable
    (μ : Measure (LOOConcentration.Observation 1 1)) [IsProbabilityMeasure μ]
    (hSecond : Integrable LOOConcentration.observationNormSq μ) :
    Integrable (fun z : LOOConcentration.Observation 1 1 => |z.2 0|) μ := by
  have hSq : Integrable (fun z : LOOConcentration.Observation 1 1 => (z.2 0) ^ 2) μ :=
    hSecond.mono' (by fun_prop) (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      simp only [LOOConcentration.observationNormSq, Fin.sum_univ_one]
      exact le_add_of_nonneg_left (sq_nonneg (z.1 0)))
  have hLp : MemLp (fun z : LOOConcentration.Observation 1 1 => z.2 0) 2 μ :=
    (memLp_two_iff_integrable_sq (by fun_prop)).2 hSq
  simpa only [Real.norm_eq_abs] using (hLp.integrable one_le_two).norm

private theorem ridgeFeatureAbsMean_integrable
    (μ : Measure (LOOConcentration.Observation 1 1)) [IsProbabilityMeasure μ]
    (hAbs : Integrable (fun z : LOOConcentration.Observation 1 1 => |z.1 0|) μ)
    (r : ℕ) :
    Integrable (ridgeFeatureAbsMean r)
      (Measure.pi fun _ : Fin (r + 1) => μ) := by
  let P := Measure.pi fun _ : Fin (r + 1) => μ
  have hc (i : Fin (r + 1)) :
      Integrable (fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) =>
        |(D i).1 0|) P := by
    exact (measurePreserving_eval (fun _ : Fin (r + 1) => μ) i).integrable_comp_of_integrable hAbs
  have hsum : Integrable
      (fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) =>
        ∑ i : Fin (r + 1), |(D i).1 0|) P :=
    integrable_finsetSum Finset.univ (fun i _ => hc i)
  simpa only [ridgeFeatureAbsMean] using hsum.div_const (r + 1 : ℝ)

private theorem ridgeResponseAbsMean_integrable
    (μ : Measure (LOOConcentration.Observation 1 1)) [IsProbabilityMeasure μ]
    (hAbs : Integrable (fun z : LOOConcentration.Observation 1 1 => |z.2 0|) μ)
    (r : ℕ) :
    Integrable (ridgeResponseAbsMean r)
      (Measure.pi fun _ : Fin (r + 1) => μ) := by
  let P := Measure.pi fun _ : Fin (r + 1) => μ
  have hc (i : Fin (r + 1)) :
      Integrable (fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) =>
        |(D i).2 0|) P := by
    exact (measurePreserving_eval (fun _ : Fin (r + 1) => μ) i).integrable_comp_of_integrable hAbs
  have hsum : Integrable
      (fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) =>
        ∑ i : Fin (r + 1), |(D i).2 0|) P :=
    integrable_finsetSum Finset.univ (fun i _ => hc i)
  simpa only [ridgeResponseAbsMean] using hsum.div_const (r + 1 : ℝ)

private theorem ridge_average_abs_le {N : ℕ} (hN : 0 < (N : ℝ))
    (f : Fin N → ℝ) :
    |(∑ i : Fin N, f i) / (N : ℝ)| ≤
      (∑ i : Fin N, |f i|) / (N : ℝ) := by
  have hsum := Finset.abs_sum_le_sum_abs (s := Finset.univ) f
  rw [abs_div, abs_of_pos hN]
  exact div_le_div_of_nonneg_right hsum hN.le

private theorem ridgeEstimator_eval_formula (r : ℕ)
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1))
    (b δ : {t : ℝ // 0 < t}) (x : ℝ) :
    let N : ℝ := ((r + 1 : ℕ) : ℝ)
    let X := LOOConcentrationManuscript.featureValues D
    let U := LOOConcentrationManuscript.clippedResponseValues D b.val
    let a : ℝ := (∑ i : Fin (r + 1), X i) / N
    let c : ℝ := (∑ i : Fin (r + 1), U i) / N
    let v : ℝ := (∑ i : Fin (r + 1), (X i - a) ^ 2) / N
    let s : ℝ := (∑ i : Fin (r + 1), (X i - a) * (U i - c)) / N
    let d : ℝ := (∑ i : Fin (r + 1), (D i).2 0) / N
    let beta : ℝ := s / (v + δ.val)
    ((LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r D)
      (fun _ : Fin 1 => x)) 0 = d + beta * (x - a) := by
  classical
  simp [LOOConcentration.Manuscript.stabilizedLinearEstimator,
    LOOConcentrationManuscript.featureValues,
    LOOConcentrationManuscript.clippedResponseValues]
  field_simp

private theorem ridgeEstimator_slope_bound (r : ℕ)
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1))
    (b δ : {t : ℝ // 0 < t}) :
    let N : ℝ := ((r + 1 : ℕ) : ℝ)
    let X := LOOConcentrationManuscript.featureValues D
    let U := LOOConcentrationManuscript.clippedResponseValues D b.val
    let a : ℝ := (∑ i : Fin (r + 1), X i) / N
    let c : ℝ := (∑ i : Fin (r + 1), U i) / N
    let v : ℝ := (∑ i : Fin (r + 1), (X i - a) ^ 2) / N
    let s : ℝ := (∑ i : Fin (r + 1), (X i - a) * (U i - c)) / N
    let beta : ℝ := s / (v + δ.val)
    |beta| ≤ b.val / (2 * Real.sqrt δ.val) := by
  have h := (LOOConcentrationManuscript.Internal.ridgePredictor_actual_query_derivative_and_slope_bound
    r D b.val δ.val b.property δ.property 0).2
  simpa [LOOConcentrationManuscript.featureValues,
    LOOConcentrationManuscript.clippedResponseValues] using h

private theorem ridgeEstimator_abs_eval_bound (r : ℕ)
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1))
    (b δ : {t : ℝ // 0 < t}) (x : ℝ) :
    |((LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r D)
      (fun _ : Fin 1 => x)) 0| ≤
      ridgeResponseAbsMean r D +
        (b.val / (2 * Real.sqrt δ.val)) * |x| +
        (b.val / (2 * Real.sqrt δ.val)) * ridgeFeatureAbsMean r D := by
  classical
  let N : ℝ := ((r + 1 : ℕ) : ℝ)
  let X := LOOConcentrationManuscript.featureValues D
  let U := LOOConcentrationManuscript.clippedResponseValues D b.val
  let a : ℝ := (∑ i : Fin (r + 1), X i) / N
  let c : ℝ := (∑ i : Fin (r + 1), U i) / N
  let v : ℝ := (∑ i : Fin (r + 1), (X i - a) ^ 2) / N
  let s : ℝ := (∑ i : Fin (r + 1), (X i - a) * (U i - c)) / N
  let d : ℝ := (∑ i : Fin (r + 1), (D i).2 0) / N
  let beta : ℝ := s / (v + δ.val)
  let S : ℝ := b.val / (2 * Real.sqrt δ.val)
  have hFormula := ridgeEstimator_eval_formula r D b δ x
  have hSlope := ridgeEstimator_slope_bound r D b δ
  have hS : 0 ≤ S := by
    dsimp [S]
    exact div_nonneg b.property.le (le_of_lt (mul_pos (by norm_num) (Real.sqrt_pos.2 δ.property)))
  have hA : |a| ≤ ridgeFeatureAbsMean r D := by
    simpa [a, X, N, ridgeFeatureAbsMean,
      LOOConcentrationManuscript.featureValues] using
      ridge_average_abs_le (by positivity : 0 < ((r + 1 : ℕ) : ℝ))
        (fun i : Fin (r + 1) => (D i).1 0)
  have hD : |d| ≤ ridgeResponseAbsMean r D := by
    simpa [d, N, ridgeResponseAbsMean] using
      ridge_average_abs_le (by positivity : 0 < ((r + 1 : ℕ) : ℝ))
        (fun i : Fin (r + 1) => (D i).2 0)
  rw [hFormula]
  change |d + beta * (x - a)| ≤ _
  calc
    |d + beta * (x - a)| ≤ |d| + |beta| * |x - a| := by
      calc
        _ ≤ |d| + |beta * (x - a)| := by
          simpa only [sub_neg_eq_add, abs_neg] using abs_sub d (-(beta * (x - a)))
        _ = _ := by rw [abs_mul]
    _ ≤ ridgeResponseAbsMean r D + S * |x - a| := by
      exact add_le_add hD
        (mul_le_mul_of_nonneg_right hSlope (abs_nonneg _))
    _ ≤ ridgeResponseAbsMean r D + S * (|x| + |a|) := by
      gcongr
      exact abs_sub _ _
    _ = ridgeResponseAbsMean r D + S * |x| + S * |a| := by ring
    _ ≤ ridgeResponseAbsMean r D + S * |x| + S * ridgeFeatureAbsMean r D := by
      gcongr

private theorem ridgeEstimator_query_lipschitz (r : ℕ)
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1))
    (b δ : {t : ℝ // 0 < t}) :
    ∀ x x' : ℝ,
      |((LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r D)
          (fun _ : Fin 1 => x)) 0 -
        ((LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r D)
          (fun _ : Fin 1 => x')) 0| ≤
        (b.val / (2 * Real.sqrt δ.val)) * |x - x'| := by
  intro x x'
  let N : ℝ := ((r + 1 : ℕ) : ℝ)
  let X := LOOConcentrationManuscript.featureValues D
  let U := LOOConcentrationManuscript.clippedResponseValues D b.val
  let a : ℝ := (∑ i : Fin (r + 1), X i) / N
  let c : ℝ := (∑ i : Fin (r + 1), U i) / N
  let v : ℝ := (∑ i : Fin (r + 1), (X i - a) ^ 2) / N
  let s : ℝ := (∑ i : Fin (r + 1), (X i - a) * (U i - c)) / N
  let d : ℝ := (∑ i : Fin (r + 1), (D i).2 0) / N
  let beta : ℝ := s / (v + δ.val)
  have hSlope := ridgeEstimator_slope_bound r D b δ
  change |beta| ≤ b.val / (2 * Real.sqrt δ.val) at hSlope
  rw [ridgeEstimator_eval_formula r D b δ x,
    ridgeEstimator_eval_formula r D b δ x']
  calc
    |(d + beta * (x - a)) - (d + beta * (x' - a))| =
        |beta| * |x - x'| := by
      rw [show (d + beta * (x - a)) - (d + beta * (x' - a)) =
        beta * (x - x') by ring, abs_mul]
    _ ≤ (b.val / (2 * Real.sqrt δ.val)) * |x - x'| :=
      mul_le_mul_of_nonneg_right hSlope (abs_nonneg _)

private theorem ridgeWeighted_euclidean_bound (S A B : ℝ)
    (hS : 0 ≤ S) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    S * A + B ≤ Real.sqrt (1 + S ^ 2) * Real.sqrt (A ^ 2 + B ^ 2) := by
  have hLeft : 0 ≤ S * A + B := add_nonneg (mul_nonneg hS hA) hB
  have hRight : 0 ≤ Real.sqrt (1 + S ^ 2) * Real.sqrt (A ^ 2 + B ^ 2) := by positivity
  apply (sq_le_sq₀ hLeft hRight).1
  rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 1 + S ^ 2),
    Real.sq_sqrt (by positivity : 0 ≤ A ^ 2 + B ^ 2)]
  nlinarith [sq_nonneg (A - S * B)]

private theorem ridgeActualLoss_pairwise_bound (r : ℕ)
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1))
    (b δ : {t : ℝ // 0 < t}) :
    let C : ℝ := Real.sqrt (1 + b.val ^ 2 / (4 * δ.val))
    ∀ z w : LOOConcentration.Observation 1 1,
      |LOOConcentration.fittedLoss
          (LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r)
          ridgeAbsoluteLoss D z -
        LOOConcentration.fittedLoss
          (LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r)
          ridgeAbsoluteLoss D w| ≤ C * LOOConcentration.observationNorm (z - w) := by
  intro C
  let S : ℝ := b.val / (2 * Real.sqrt δ.val)
  have hS : 0 ≤ S := by
    dsimp [S]
    exact div_nonneg b.property.le (le_of_lt (mul_pos (by norm_num) (Real.sqrt_pos.2 δ.property)))
  have hSsq : S ^ 2 = b.val ^ 2 / (4 * δ.val) := by
    dsimp [S]
    rw [div_pow, mul_pow, Real.sq_sqrt δ.property.le]
    ring
  have hC : C = Real.sqrt (1 + S ^ 2) := by rw [hSsq]
  intro z w
  have hQuery := ridgeEstimator_query_lipschitz r D b δ
  have hQuery' :
      |((LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r D)
          (fun _ : Fin 1 => z.1 0)) 0 -
        ((LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r D)
          (fun _ : Fin 1 => w.1 0)) 0| ≤ S * |z.1 0 - w.1 0| := by
    simpa only [S] using hQuery (z.1 0) (w.1 0)
  have hLoss :
      |LOOConcentration.fittedLoss
          (LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r)
          ridgeAbsoluteLoss D z -
        LOOConcentration.fittedLoss
          (LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r)
          ridgeAbsoluteLoss D w| ≤
        S * |z.1 0 - w.1 0| + |z.2 0 - w.2 0| := by
    change
      |abs (((LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r D)
          (fun _ : Fin 1 => z.1 0)) 0 - z.2 0) -
        abs (((LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r D)
          (fun _ : Fin 1 => w.1 0)) 0 - w.2 0)| ≤ _
    calc
      _ ≤ |((((LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r D)
          (fun _ : Fin 1 => z.1 0)) 0 - z.2 0) -
        (((LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r D)
          (fun _ : Fin 1 => w.1 0)) 0 - w.2 0))| :=
        abs_abs_sub_abs_le_abs_sub _ _
      _ = |((((LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r D)
          (fun _ : Fin 1 => z.1 0)) 0 -
        ((LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r D)
          (fun _ : Fin 1 => w.1 0)) 0) - (z.2 0 - w.2 0))| := by
        congr 1
        ring
      _ ≤ _ := by
        calc
          _ ≤ |(((LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r D)
              (fun _ : Fin 1 => z.1 0)) 0 -
            ((LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r D)
              (fun _ : Fin 1 => w.1 0)) 0)| + |z.2 0 - w.2 0| := abs_sub _ _
          _ ≤ S * |z.1 0 - w.1 0| + |z.2 0 - w.2 0| :=
            add_le_add hQuery' le_rfl
  have hNorm : LOOConcentration.observationNorm (z - w) =
      Real.sqrt ((z.1 0 - w.1 0) ^ 2 + (z.2 0 - w.2 0) ^ 2) := by
    simp [LOOConcentration.observationNorm, LOOConcentration.observationNormSq]
  rw [hNorm]
  calc
    _ ≤ S * |z.1 0 - w.1 0| + |z.2 0 - w.2 0| := hLoss
    _ ≤ Real.sqrt (1 + S ^ 2) *
        Real.sqrt (|z.1 0 - w.1 0| ^ 2 + |z.2 0 - w.2 0| ^ 2) :=
      ridgeWeighted_euclidean_bound S |z.1 0 - w.1 0| |z.2 0 - w.2 0|
        hS (abs_nonneg _) (abs_nonneg _)
    _ = C * Real.sqrt ((z.1 0 - w.1 0) ^ 2 + (z.2 0 - w.2 0) ^ 2) := by
      rw [hC]
      congr 1
      simp only [sq_abs]

private theorem ridgeActualLoss_zero_eq_response (r : ℕ)
    (b δ : {t : ℝ // 0 < t}) (z : LOOConcentration.Observation 1 1) :
    LOOConcentration.fittedLoss
      (LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r)
      ridgeAbsoluteLoss (0 : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1)) z =
      |z.2 0| := by
  simp [LOOConcentration.fittedLoss, ridgeAbsoluteLoss,
    LOOConcentration.Manuscript.stabilizedLinearEstimator]

private theorem ridgeActualLoss_measurable (r : ℕ)
    (b δ : {t : ℝ // 0 < t}) (z : LOOConcentration.Observation 1 1) :
    Measurable (fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) =>
      LOOConcentration.fittedLoss
        (LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r)
        ridgeAbsoluteLoss D z) := by
  dsimp [LOOConcentration.fittedLoss, ridgeAbsoluteLoss,
    LOOConcentration.Manuscript.stabilizedLinearEstimator]
  fun_prop

/-- True-L1 expected-loss regularity for the literal public stabilized ridge
estimator. The query constant is the source value and is fixed before `r`. -/
theorem stabilizedLinearEstimator_expected_absoluteLoss_query_fields
    (μ : Measure (LOOConcentration.Observation 1 1)) [IsProbabilityMeasure μ]
    (hSecond : Integrable LOOConcentration.observationNormSq μ)
    (b δ : {t : ℝ // 0 < t}) :
    ∀ r : ℕ,
      let P := Measure.pi (fun _ : Fin (r + 1) => μ)
      let T : LOOConcentration.Estimator 1 1 (r + 1) :=
        LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r
      let L := ridgeAbsoluteLoss
      (∀ z : LOOConcentration.Observation 1 1,
        Integrable (fun D => LOOConcentration.fittedLoss T L D z) P) ∧
      @Integrable ℝ PseudoMetricSpace.toUniformSpace.toTopologicalSpace
        NormedAddCommGroup.toENormedAddCommMonoid.toContinuousENorm
        (LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) ×
          LOOConcentration.Observation 1 1) _
        (fun p : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) ×
            LOOConcentration.Observation 1 1 =>
          LOOConcentration.fittedLoss T L p.1 p.2) (P.prod μ) ∧
      (∀ z : LOOConcentration.Observation 1 1,
        LOOConcentration.fittedLoss T L
          (0 : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1)) z =
            |z.2 0|) ∧
      Integrable
        (fun z : LOOConcentration.Observation 1 1 =>
          LOOConcentration.fittedLoss T L
            (0 : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1)) z) μ ∧
      ∀ z w : LOOConcentration.Observation 1 1,
        |(∫ D, LOOConcentration.fittedLoss T L D z ∂P) -
          (∫ D, LOOConcentration.fittedLoss T L D w ∂P)| ≤
          Real.sqrt (1 + b.val ^ 2 / (4 * δ.val)) *
            LOOConcentration.observationNorm (z - w) := by
  intro r P T L
  classical
  have hYAbs := ridgeResponseCoordinate_abs_integrable μ hSecond
  have hXAbs := ridgeFeatureCoordinate_abs_integrable μ hSecond
  have hMX : Integrable (ridgeFeatureAbsMean r)
      (Measure.pi fun _ : Fin (r + 1) => μ) :=
    ridgeFeatureAbsMean_integrable μ hXAbs r
  have hMY : Integrable (ridgeResponseAbsMean r)
      (Measure.pi fun _ : Fin (r + 1) => μ) :=
    ridgeResponseAbsMean_integrable μ hYAbs r
  let S : ℝ := b.val / (2 * Real.sqrt δ.val)
  have hS : 0 ≤ S := by
    dsimp [S]
    exact div_nonneg b.property.le
      (le_of_lt (mul_pos (by norm_num) (Real.sqrt_pos.2 δ.property)))
  have hPointwise (z : LOOConcentration.Observation 1 1) :
      Integrable (fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) =>
        LOOConcentration.fittedLoss T L D z) (Measure.pi fun _ : Fin (r + 1) => μ) := by
    let env : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) → ℝ :=
      fun D => ((ridgeResponseAbsMean r D + S * |z.1 0|) +
        S * ridgeFeatureAbsMean r D) + |z.2 0|
    have hSMX : Integrable (fun D => S * ridgeFeatureAbsMean r D)
        (Measure.pi fun _ : Fin (r + 1) => μ) := by
      simpa only [mul_comm] using hMX.const_mul S
    have hEnv := ((hMY.add (integrable_const (S * |z.1 0|))).add hSMX).add
      (integrable_const |z.2 0|)
    have hMeas := ridgeActualLoss_measurable r b δ z
    apply hEnv.mono' hMeas.aestronglyMeasurable
    filter_upwards [] with D
    change ‖LOOConcentration.fittedLoss T L D z‖ ≤ env D
    rw [Real.norm_eq_abs]
    change |ridgeAbsoluteLoss ((T D) z.1) z.2| ≤ env D
    simp only [ridgeAbsoluteLoss]
    simp only [abs_abs]
    have hz : z.1 = (fun _ : Fin 1 => z.1 0) := by
      funext i
      fin_cases i
      rfl
    calc
      _ ≤ |((T D) z.1) 0| + |z.2 0| := abs_sub _ _
      _ ≤ ridgeResponseAbsMean r D + S * |z.1 0| +
          S * ridgeFeatureAbsMean r D + |z.2 0| := by
        simpa only [S, T, ← hz] using
          add_le_add_left (ridgeEstimator_abs_eval_bound r D b δ (z.1 0)) |z.2 0|
  have hPointwiseAll : ∀ z : LOOConcentration.Observation 1 1,
      Integrable (fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) =>
        LOOConcentration.fittedLoss T L D z) (Measure.pi fun _ : Fin (r + 1) => μ) :=
    fun z => hPointwise z
  have hZero : ∀ z : LOOConcentration.Observation 1 1,
      LOOConcentration.fittedLoss T L
        (0 : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1)) z =
          |z.2 0| := by
    intro z
    exact ridgeActualLoss_zero_eq_response r b δ z
  have hZeroInt : Integrable
      (fun z : LOOConcentration.Observation 1 1 =>
        LOOConcentration.fittedLoss T L
          (0 : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1)) z) μ := by
    simpa only [hZero] using hYAbs
  let Q := (Measure.pi fun _ : Fin (r + 1) => μ).prod μ
  have hFst : MeasurePreserving Prod.fst Q
      (Measure.pi fun _ : Fin (r + 1) => μ) := measurePreserving_fst
  have hSnd : MeasurePreserving Prod.snd Q μ := measurePreserving_snd
  have hMXQ : Integrable
      (fun p : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) ×
        LOOConcentration.Observation 1 1 => ridgeFeatureAbsMean r p.1) Q :=
    hFst.integrable_comp_of_integrable hMX
  have hMYQ : Integrable
      (fun p : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) ×
        LOOConcentration.Observation 1 1 => ridgeResponseAbsMean r p.1) Q :=
    hFst.integrable_comp_of_integrable hMY
  have hXQ : Integrable
      (fun p : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) ×
        LOOConcentration.Observation 1 1 => |p.2.1 0|) Q := by
    exact hSnd.integrable_comp_of_integrable hXAbs
  have hYQ : Integrable
      (fun p : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) ×
        LOOConcentration.Observation 1 1 => |p.2.2 0|) Q := by
    exact hSnd.integrable_comp_of_integrable hYAbs
  have hSMXQ : Integrable
      (fun p : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) ×
        LOOConcentration.Observation 1 1 => S * ridgeFeatureAbsMean r p.1) Q := by
    simpa only [mul_comm] using hMXQ.const_mul S
  have hEnvQ : @Integrable ℝ PseudoMetricSpace.toUniformSpace.toTopologicalSpace
      NormedAddCommGroup.toENormedAddCommMonoid.toContinuousENorm
      (LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) ×
        LOOConcentration.Observation 1 1) _
      (fun p : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) ×
          LOOConcentration.Observation 1 1 =>
        ridgeResponseAbsMean r p.1 + S * |p.2.1 0| +
          S * ridgeFeatureAbsMean r p.1 + |p.2.2 0|) Q := by
    have hSXQ : Integrable (fun p => S * |p.2.1 0|) Q := by
      simpa only [mul_comm] using hXQ.const_mul S
    let fMY := fun p : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) ×
      LOOConcentration.Observation 1 1 => ridgeResponseAbsMean r p.1
    let fSX := fun p : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) ×
      LOOConcentration.Observation 1 1 => S * |p.2.1 0|
    let fSMX := fun p : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) ×
      LOOConcentration.Observation 1 1 => S * ridgeFeatureAbsMean r p.1
    let fY := fun p : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) ×
      LOOConcentration.Observation 1 1 => |p.2.2 0|
    have hEq :
        (fun p : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) ×
            LOOConcentration.Observation 1 1 =>
          ridgeResponseAbsMean r p.1 + S * |p.2.1 0| +
            S * ridgeFeatureAbsMean r p.1 + |p.2.2 0|) =
          fMY + (fSX + (fSMX + fY)) := by
      funext p
      simp only [Pi.add_apply]
      dsimp [fMY, fSX, fSMX, fY]
      ring
    rw [hEq]
    exact hMYQ.add (hSXQ.add (hSMXQ.add hYQ))
  have hJointMeas : Measurable
      (fun p : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) ×
          LOOConcentration.Observation 1 1 =>
        LOOConcentration.fittedLoss T L p.1 p.2) := by
    dsimp [LOOConcentration.fittedLoss, L, ridgeAbsoluteLoss,
      T, LOOConcentration.Manuscript.stabilizedLinearEstimator]
    fun_prop
  have hJoint : @Integrable ℝ PseudoMetricSpace.toUniformSpace.toTopologicalSpace
      NormedAddCommGroup.toENormedAddCommMonoid.toContinuousENorm
      (LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) ×
        LOOConcentration.Observation 1 1) _
      (fun p : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) ×
          LOOConcentration.Observation 1 1 =>
        LOOConcentration.fittedLoss T L p.1 p.2) Q := by
    apply hEnvQ.mono' hJointMeas.aestronglyMeasurable
    filter_upwards [] with p
    change ‖LOOConcentration.fittedLoss T L p.1 p.2‖ ≤ _
    rw [Real.norm_eq_abs]
    change |ridgeAbsoluteLoss ((T p.1) p.2.1) p.2.2| ≤ _
    simp only [ridgeAbsoluteLoss]
    simp only [abs_abs]
    have hz : p.2.1 = (fun _ : Fin 1 => p.2.1 0) := by
      funext i
      fin_cases i
      rfl
    calc
      _ ≤ |((T p.1) p.2.1) 0| + |p.2.2 0| := abs_sub _ _
      _ ≤ ridgeResponseAbsMean r p.1 + S * |p.2.1 0| +
          S * ridgeFeatureAbsMean r p.1 + |p.2.2 0| := by
        simpa only [S, T, ← hz] using
          add_le_add_left (ridgeEstimator_abs_eval_bound r p.1 b δ (p.2.1 0))
            |p.2.2 0|
  have hExpectedPair (z w : LOOConcentration.Observation 1 1) :
      |(∫ D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1),
          LOOConcentration.fittedLoss T L D z ∂(Measure.pi fun _ : Fin (r + 1) => μ)) -
        (∫ D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1),
          LOOConcentration.fittedLoss T L D w ∂(Measure.pi fun _ : Fin (r + 1) => μ))| ≤
        Real.sqrt (1 + b.val ^ 2 / (4 * δ.val)) *
          LOOConcentration.observationNorm (z - w) := by
    have hZ := hPointwise z
    have hW := hPointwise w
    let C : ℝ := Real.sqrt (1 + b.val ^ 2 / (4 * δ.val))
    have hBound (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1)) :=
      ridgeActualLoss_pairwise_bound r D b δ z w
    calc
      _ = |∫ D, LOOConcentration.fittedLoss T L D z -
          LOOConcentration.fittedLoss T L D w ∂(Measure.pi fun _ : Fin (r + 1) => μ)| := by
        rw [integral_sub hZ hW]
      _ ≤ ∫ D, |LOOConcentration.fittedLoss T L D z -
          LOOConcentration.fittedLoss T L D w| ∂(Measure.pi fun _ : Fin (r + 1) => μ) :=
        abs_integral_le_integral_abs
      _ ≤ ∫ _D, C * LOOConcentration.observationNorm (z - w)
          ∂(Measure.pi fun _ : Fin (r + 1) => μ) := by
        exact integral_mono ((hZ.sub hW).abs) (integrable_const _) hBound
      _ = C * LOOConcentration.observationNorm (z - w) := by
        rw [integral_const]
        simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  refine ⟨hPointwiseAll, ?_, hZero, hZeroInt, ?_⟩
  · simpa only [Q] using hJoint
  · intro z w
    exact hExpectedPair z w

end
end LOOConcentrationManuscript.Internal
