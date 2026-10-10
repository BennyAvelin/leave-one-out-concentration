import LOOConcentrationManuscript.Internal.RidgeAddOneSlopeMoments
import LOOConcentrationManuscript.Internal.RidgePredictorQueryFeature
import LOOConcentration.Frozen.Foundations.FittedLoss
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
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

private abbrev ridgeDeleteAbsoluteLoss :
    LOOConcentration.Responses 1 → LOOConcentration.Responses 1 → ℝ :=
  fun u v => |u 0 - v 0|

private theorem ridge_pi_average_integrable_and_integral
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (N : ℕ) (hN : 0 < N) (f : α → ℝ) (hf : Integrable f μ) :
    Integrable (fun D : Fin N → α => (∑ i : Fin N, f (D i)) / (N : ℝ))
        (Measure.pi fun _ : Fin N => μ) ∧
      (∫ D : Fin N → α, (∑ i : Fin N, f (D i)) / (N : ℝ)
          ∂Measure.pi (fun _ : Fin N => μ)) = ∫ z, f z ∂μ := by
  let P := Measure.pi fun _ : Fin N => μ
  have hCoord (i : Fin N) : Integrable (fun D : Fin N → α => f (D i)) P :=
    (measurePreserving_eval (fun _ : Fin N => μ) i).integrable_comp_of_integrable hf
  have hSum : Integrable (fun D : Fin N → α => ∑ i : Fin N, f (D i)) P :=
    integrable_finsetSum Finset.univ (fun i _ => hCoord i)
  have hCoordInt (i : Fin N) :
      (∫ D : Fin N → α, f (D i) ∂P) = ∫ z, f z ∂μ := by
    let hMP := measurePreserving_eval (fun _ : Fin N => μ) i
    have hMapMeas : AEStronglyMeasurable f (Measure.map (Function.eval i) P) := by
      rw [hMP.map_eq]
      exact hf.aestronglyMeasurable
    have hMap := integral_map hMP.measurable.aemeasurable hMapMeas
    rw [hMP.map_eq] at hMap
    exact hMap.symm
  refine ⟨?_, ?_⟩
  · simpa only [P] using hSum.div_const (N : ℝ)
  · calc
      _ = (N : ℝ)⁻¹ * (∫ D : Fin N → α, ∑ i : Fin N, f (D i) ∂P) := by
        rw [show (fun D : Fin N → α => (∑ i : Fin N, f (D i)) / (N : ℝ)) =
          fun D => (N : ℝ)⁻¹ * (∑ i : Fin N, f (D i)) by funext D; ring]
        rw [integral_const_mul]
      _ = (N : ℝ)⁻¹ * ∑ i : Fin N, ∫ D : Fin N → α, f (D i) ∂P := by
        rw [integral_finsetSum Finset.univ (fun i hi => hCoord i)]
      _ = (N : ℝ)⁻¹ * ((N : ℝ) * ∫ z, f z ∂μ) := by
        congr 1
        calc
          _ = ∑ _i : Fin N, ∫ z, f z ∂μ := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hCoordInt i
          _ = _ := by simp
      _ = ∫ z, f z ∂μ := by
        have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
        field_simp

private theorem ridge_prod_fst_integral
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (ν : Measure β) [IsProbabilityMeasure ν]
    (f : α → ℝ) (hf : Integrable f μ) :
    Integrable (fun p : α × β => f p.1) (μ.prod ν) ∧
      (∫ p : α × β, f p.1 ∂μ.prod ν) = ∫ x, f x ∂μ := by
  have hInt : Integrable (fun p : α × β => f p.1) (μ.prod ν) :=
    measurePreserving_fst.integrable_comp_of_integrable hf
  have hEq : (∫ p : α × β, f p.1 ∂μ.prod ν) =
      (∫ x, f x ∂μ) * (∫ y : β, (1 : ℝ) ∂ν) := by
    calc
      _ = ∫ p : α × β, f p.1 * (1 : ℝ) ∂μ.prod ν := by
        congr 1
        funext p
        ring
      _ = _ := integral_prod_mul f (fun _ : β => (1 : ℝ))
  refine ⟨hInt, ?_⟩
  rw [hEq]
  simp

private theorem ridge_prod_snd_integral
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (ν : Measure β) [IsProbabilityMeasure ν]
    (f : β → ℝ) (hf : Integrable f ν) :
    Integrable (fun p : α × β => f p.2) (μ.prod ν) ∧
      (∫ p : α × β, f p.2 ∂μ.prod ν) = ∫ y, f y ∂ν := by
  have hInt : Integrable (fun p : α × β => f p.2) (μ.prod ν) :=
    measurePreserving_snd.integrable_comp_of_integrable hf
  have hEq : (∫ p : α × β, f p.2 ∂μ.prod ν) =
      (∫ x : α, (1 : ℝ) ∂μ) * (∫ y, f y ∂ν) := by
    calc
      _ = ∫ p : α × β, (1 : ℝ) * f p.2 ∂μ.prod ν := by
        congr 1
        funext p
        ring
      _ = _ := integral_prod_mul (fun _ : α => (1 : ℝ)) f
  refine ⟨hInt, ?_⟩
  rw [hEq]
  simp

private theorem ridge_average_abs_le {N : ℕ} (hN : 0 < (N : ℝ))
    (f : Fin N → ℝ) :
    |(∑ i : Fin N, f i) / (N : ℝ)| ≤
      (∑ i : Fin N, |f i|) / (N : ℝ) := by
  have hsum := Finset.abs_sum_le_sum_abs (s := Finset.univ) f
  rw [abs_div, abs_of_pos hN]
  exact div_le_div_of_nonneg_right hsum hN.le

theorem ridge_actual_first_moment_feature_sq_source
    (μ : Measure (LOOConcentration.Observation 1 1)) [IsProbabilityMeasure μ]
    (hX4 : Integrable (fun z => (z.1 0) ^ 4) μ)
    (hY1 : Integrable (fun z => |z.2 0|) μ) :
    Integrable (fun z => |z.1 0|) μ ∧
      Integrable (fun z => (z.1 0) ^ 2) μ ∧
      Integrable (fun z => z.1 0) μ ∧
      Integrable (fun z => z.2 0) μ := by
  have hOne : Integrable (fun _ : LOOConcentration.Observation 1 1 => (1 : ℝ)) μ :=
    integrable_const 1
  have hMajor : Integrable (fun z => (1 : ℝ) + (z.1 0) ^ 4) μ := hOne.add hX4
  have hXabs : Integrable (fun z : LOOConcentration.Observation 1 1 => |z.1 0|) μ := by
    apply hMajor.mono' (by fun_prop)
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_abs]
    nlinarith [sq_nonneg (|z.1 0| - (1 / 2 : ℝ)),
      sq_nonneg ((z.1 0) ^ 2 - (1 / 2 : ℝ)), sq_abs (z.1 0)]
  have hXsq : Integrable (fun z : LOOConcentration.Observation 1 1 => (z.1 0) ^ 2) μ := by
    apply hMajor.mono' (by fun_prop)
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (z.1 0))]
    nlinarith [sq_nonneg ((z.1 0) ^ 2 - (1 / 2 : ℝ))]
  have hX : Integrable (fun z : LOOConcentration.Observation 1 1 => z.1 0) μ := by
    apply hXabs.mono' (by fun_prop)
    filter_upwards with z
    exact le_rfl
  have hY : Integrable (fun z : LOOConcentration.Observation 1 1 => z.2 0) μ := by
    apply hY1.mono' (by fun_prop)
    filter_upwards with z
    exact le_rfl
  exact ⟨hXabs, hXsq, hX, hY⟩

private theorem ridge_actual_predictor_abs_bound (r : ℕ)
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1))
    (b δ : {t : ℝ // 0 < t}) (x : ℝ) :
    |((LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r D)
      (fun _ : Fin 1 => x)) 0| ≤
      |(∑ i : Fin (r + 1), (D i).2 0) / (r + 1 : ℝ)| +
        (b.val / (2 * Real.sqrt δ.val)) * |x| +
        (b.val / (2 * Real.sqrt δ.val)) *
          |(∑ i : Fin (r + 1), (D i).1 0) / (r + 1 : ℝ)| := by
  let N : ℝ := ((r + 1 : ℕ) : ℝ)
  let X := LOOConcentrationManuscript.featureValues D
  let U := LOOConcentrationManuscript.clippedResponseValues D b.val
  let a : ℝ := (∑ i : Fin (r + 1), X i) / N
  let c : ℝ := (∑ i : Fin (r + 1), U i) / N
  let v : ℝ := (∑ i : Fin (r + 1), (X i - a) ^ 2) / N
  let s : ℝ := (∑ i : Fin (r + 1), (X i - a) * (U i - c)) / N
  let ybar : ℝ := (∑ i : Fin (r + 1), (D i).2 0) / N
  let beta : ℝ := s / (v + δ.val)
  let S : ℝ := b.val / (2 * Real.sqrt δ.val)
  have hFormula := ridge_actual_public_predictor_eval_formula r D b δ x
  have hSlope := LOOConcentrationManuscript.Internal.ridgePredictor_actual_query_derivative_and_slope_bound
    r D b.val δ.val b.property δ.property
  have hBeta : |beta| ≤ S := by
    simpa [X, U, a, c, v, s, beta, N, S,
      LOOConcentrationManuscript.featureValues,
      LOOConcentrationManuscript.clippedResponseValues,
      Nat.cast_add, Nat.cast_one] using (hSlope x).2
  have hS : 0 ≤ S := by
    dsimp [S]
    exact div_nonneg b.property.le
      (le_of_lt (mul_pos (by norm_num) (Real.sqrt_pos.2 δ.property)))
  rw [hFormula]
  change |ybar + beta * (x - a)| ≤ _
  calc
    _ ≤ |ybar| + |beta * (x - a)| := abs_add_le _ _
    _ = |ybar| + |beta| * |x - a| := by rw [abs_mul]
    _ ≤ |ybar| + |beta| * (|x| + |a|) := by
      gcongr
      exact abs_sub _ _
    _ ≤ |ybar| + S * |x| + S * |a| := by
      calc
        _ ≤ |ybar| + S * (|x| + |a|) := by
          gcongr
        _ = _ := by ring
    _ = _ := by
      dsimp [ybar, a, N, S]
      rw [Nat.cast_add, Nat.cast_one]
      field_simp
      simp only [X, LOOConcentrationManuscript.featureValues]

private theorem ridge_pi_average_abs_integrable_and_integral
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (N : ℕ) (hN : 0 < N) (f : α → ℝ)
    (hfa : Integrable (fun z => |f z|) μ) :
    Integrable (fun D : Fin N → α => (∑ i : Fin N, |f (D i)|) / (N : ℝ))
        (Measure.pi fun _ : Fin N => μ) ∧
      (∫ D : Fin N → α, (∑ i : Fin N, |f (D i)|) / (N : ℝ)
          ∂Measure.pi (fun _ : Fin N => μ)) = ∫ z, |f z| ∂μ := by
  have h := ridge_pi_average_integrable_and_integral μ N hN (fun z => |f z|) hfa
  simpa only [Real.norm_eq_abs] using h

private theorem ridge_pi_average_abs_mean_bound
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (N : ℕ) (hN : 0 < N) (f : α → ℝ)
    (hf : Integrable f μ) (hfa : Integrable (fun z => |f z|) μ) :
    (∫ D : Fin N → α, |(∑ i : Fin N, f (D i)) / (N : ℝ)|
        ∂Measure.pi (fun _ : Fin N => μ)) ≤ ∫ z, |f z| ∂μ := by
  have hMean := ridge_pi_average_integrable_and_integral μ N hN f hf
  have hMeanAbs : Integrable
      (fun D : Fin N → α => |(∑ i : Fin N, f (D i)) / (N : ℝ)|)
      (Measure.pi fun _ : Fin N => μ) := by
    simpa only [Real.norm_eq_abs] using hMean.1.norm
  have hAbsAvg := ridge_pi_average_abs_integrable_and_integral μ N hN f hfa
  have hPoint (D : Fin N → α) :
      |(∑ i : Fin N, f (D i)) / (N : ℝ)| ≤
        (∑ i : Fin N, |f (D i)|) / (N : ℝ) :=
    ridge_average_abs_le (by positivity) (fun i => f (D i))
  calc
    _ ≤ ∫ D : Fin N → α, (∑ i : Fin N, |f (D i)|) / (N : ℝ)
        ∂Measure.pi (fun _ : Fin N => μ) :=
      integral_mono hMeanAbs hAbsAvg.1 hPoint
    _ = ∫ z, |f z| ∂μ := hAbsAvg.2

private theorem ridge_mean_square_le_average_square {N : ℕ} (hN : 0 < N)
    (x : Fin N → ℝ) :
    ((∑ i : Fin N, x i) / (N : ℝ)) ^ 2 ≤
      (∑ i : Fin N, (x i) ^ 2) / (N : ℝ) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : Fin N => (1 : ℝ)) x
  have hsum : (∑ i : Fin N, x i) ^ 2 ≤
      (N : ℝ) * ∑ i : Fin N, (x i) ^ 2 := by
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin] using hcs
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  rw [div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hNr)).2
  calc
    _ ≤ (N : ℝ) * ∑ i : Fin N, (x i) ^ 2 := hsum
    _ = ((∑ i : Fin N, (x i) ^ 2) / (N : ℝ)) * ((N : ℝ) ^ 2) := by
      field_simp [hNr]

private theorem ridge_snoc_average_integrable_and_integral
    (μ : Measure (LOOConcentration.Observation 1 1)) [IsProbabilityMeasure μ]
    (N : ℕ) (hN : 0 < N) (f : LOOConcentration.Observation 1 1 → ℝ)
    (hf : Integrable f μ) :
    let P := Measure.pi (fun _ : Fin N => μ)
    let Q := P.prod μ
    Integrable (fun q : (Fin N → LOOConcentration.Observation 1 1) ×
        LOOConcentration.Observation 1 1 =>
      ((∑ i : Fin N, f (q.1 i)) + f q.2) / (N + 1 : ℝ)) Q ∧
    (∫ q : (Fin N → LOOConcentration.Observation 1 1) ×
        LOOConcentration.Observation 1 1,
      ((∑ i : Fin N, f (q.1 i)) + f q.2) / (N + 1 : ℝ) ∂Q) = ∫ z, f z ∂μ := by
  classical
  intro P Q
  let avg := fun D : Fin N → LOOConcentration.Observation 1 1 =>
    (∑ i : Fin N, f (D i)) / (N : ℝ)
  have hAvg := ridge_pi_average_integrable_and_integral μ N hN f hf
  have hAvgQ := ridge_prod_fst_integral P μ avg hAvg.1
  have hFQ := ridge_prod_snd_integral P μ f hf
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hN1pos : 0 < (N + 1 : ℝ) := by positivity
  have hEq : (fun q : (Fin N → LOOConcentration.Observation 1 1) ×
      LOOConcentration.Observation 1 1 =>
      ((∑ i : Fin N, f (q.1 i)) + f q.2) / (N + 1 : ℝ)) =
      (fun q => ((N : ℝ) / (N + 1 : ℝ)) * avg q.1 +
        ((N + 1 : ℝ)⁻¹) * f q.2) := by
    funext q
    dsimp [avg]
    have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
    have hN1ne : (N + 1 : ℝ) ≠ 0 := ne_of_gt hN1pos
    field_simp
  have hInt : Integrable
      (fun q : (Fin N → LOOConcentration.Observation 1 1) ×
        LOOConcentration.Observation 1 1 =>
        ((N : ℝ) / (N + 1 : ℝ)) * avg q.1 +
          ((N + 1 : ℝ)⁻¹) * f q.2) Q := by
    exact (hAvgQ.1.const_mul _).add (hFQ.1.const_mul _)
  refine ⟨?_, ?_⟩
  · rw [hEq]
    exact hInt
  · rw [hEq]
    rw [integral_add (hAvgQ.1.const_mul _) (hFQ.1.const_mul _),
      integral_const_mul, integral_const_mul, hAvgQ.2, hAvg.2, hFQ.2]
    have hmul : (N : ℝ) / (N + 1 : ℝ) + (N + 1 : ℝ)⁻¹ = 1 := by
      field_simp
    calc
      _ = ((N : ℝ) / (N + 1 : ℝ) + (N + 1 : ℝ)⁻¹) *
          (∫ z, f z ∂μ) := by ring
      _ = ∫ z, f z ∂μ := by rw [hmul]; ring

theorem ridge_actual_fit_loss_integrable_source_moments
    (μ : Measure (LOOConcentration.Observation 1 1)) [IsProbabilityMeasure μ]
    (hY1 : Integrable (fun z => |z.2 0|) μ)
    (hX1 : Integrable (fun z => |z.1 0|) μ)
    (b δ : {t : ℝ // 0 < t}) (r : ℕ) :
    Integrable
      (fun p : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) ×
          LOOConcentration.Observation 1 1 =>
        LOOConcentration.fittedLoss
          (LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r)
          ridgeDeleteAbsoluteLoss p.1 p.2)
      ((Measure.pi fun _ : Fin (r + 1) => μ).prod μ) := by
  classical
  let P := Measure.pi (fun _ : Fin (r + 1) => μ)
  let Q := P.prod μ
  let ybar := fun D : Fin (r + 1) → LOOConcentration.Observation 1 1 =>
    (∑ i : Fin (r + 1), (D i).2 0) / (r + 1 : ℝ)
  let abar := fun D : Fin (r + 1) → LOOConcentration.Observation 1 1 =>
    (∑ i : Fin (r + 1), (D i).1 0) / (r + 1 : ℝ)
  let S : ℝ := b.val / (2 * Real.sqrt δ.val)
  have hYbar := ridge_pi_average_integrable_and_integral μ (r+1) (by omega)
    (fun z => z.2 0) (by
      apply hY1.mono' (by fun_prop)
      filter_upwards with z
      exact le_rfl)
  have hAbar := ridge_pi_average_integrable_and_integral μ (r+1) (by omega)
    (fun z => z.1 0) (by
      apply hX1.mono' (by fun_prop)
      filter_upwards with z
      exact le_rfl)
  have hYbarAbs : Integrable (fun D => |ybar D|) P := by
    have hNr : 0 < ((r + 1 : ℕ) : ℝ) := by positivity
    simpa [P, ybar, Nat.cast_add, Nat.cast_one, abs_div,
      abs_of_pos hNr] using hYbar.1.norm
  have hAbarAbs : Integrable (fun D => |abar D|) P := by
    have hNr : 0 < ((r + 1 : ℕ) : ℝ) := by positivity
    simpa [P, abar, Nat.cast_add, Nat.cast_one, abs_div,
      abs_of_pos hNr] using hAbar.1.norm
  have hMYQ := ridge_prod_fst_integral P μ (fun D => |ybar D|) hYbarAbs
  have hMAQ := ridge_prod_fst_integral P μ (fun D => |abar D|) hAbarAbs
  have hXQ := ridge_prod_snd_integral P μ (fun z => |z.1 0|) hX1
  have hYQ := ridge_prod_snd_integral P μ (fun z => |z.2 0|) hY1
  have hS : 0 ≤ S := by
    dsimp [S]
    exact div_nonneg b.property.le
      (le_of_lt (mul_pos (by norm_num) (Real.sqrt_pos.2 δ.property)))
  have hEnvInt : Integrable
      (fun p : (Fin (r + 1) → LOOConcentration.Observation 1 1) ×
        LOOConcentration.Observation 1 1 =>
        |ybar p.1| + S * |p.2.1 0| + S * |abar p.1| + |p.2.2 0|) Q := by
    have hEq : (fun p : (Fin (r + 1) → LOOConcentration.Observation 1 1) ×
        LOOConcentration.Observation 1 1 =>
        |ybar p.1| + S * |p.2.1 0| + S * |abar p.1| + |p.2.2 0|) =
        (fun p => |ybar p.1|) +
          ((fun p => S * |p.2.1 0|) +
            ((fun p => S * |abar p.1|) + (fun p => |p.2.2 0|))) := by
      funext p
      simp only [Pi.add_apply]
      ring
    rw [hEq]
    exact hMYQ.1.add ((hXQ.1.const_mul S).add
      ((hMAQ.1.const_mul S).add hYQ.1))
  have hMeas : Measurable
      (fun p : (Fin (r + 1) → LOOConcentration.Observation 1 1) ×
        LOOConcentration.Observation 1 1 =>
        LOOConcentration.fittedLoss
          (LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r)
          ridgeDeleteAbsoluteLoss p.1 p.2) := by
    dsimp [LOOConcentration.fittedLoss, ridgeDeleteAbsoluteLoss,
      LOOConcentration.Manuscript.stabilizedLinearEstimator]
    fun_prop
  apply hEnvInt.mono' hMeas.aestronglyMeasurable
  filter_upwards with p
  rw [Real.norm_eq_abs]
  change |ridgeDeleteAbsoluteLoss
    ((LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r p.1) p.2.1)
    p.2.2| ≤ _
  simp only [ridgeDeleteAbsoluteLoss, abs_abs]
  have hcoord : p.2.1 = (fun _ : Fin 1 => p.2.1 0) := by
    funext i
    fin_cases i
    rfl
  calc
    _ ≤ |((LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r p.1)
        (fun _ : Fin 1 => p.2.1 0)) 0| + |p.2.2 0| := abs_sub _ _
    _ ≤ |ybar p.1| + S * |p.2.1 0| + S * |abar p.1| + |p.2.2 0| := by
      simpa only [S, ybar, abar] using
        add_le_add_left (ridge_actual_predictor_abs_bound r p.1 b δ (p.2.1 0))
          |p.2.2 0|

theorem ridge_actual_snoc_fit_loss_integrable_source_moments
    (μ : Measure (LOOConcentration.Observation 1 1)) [IsProbabilityMeasure μ]
    (hY1 : Integrable (fun z => |z.2 0|) μ)
    (hX1 : Integrable (fun z => |z.1 0|) μ)
    (b δ : {t : ℝ // 0 < t}) (r : ℕ) :
    Integrable
      (fun p : (LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) ×
          LOOConcentration.Observation 1 1) × LOOConcentration.Observation 1 1 =>
        LOOConcentration.fittedLoss
          (LOOConcentration.Manuscript.stabilizedLinearEstimator b δ (r + 1))
          ridgeDeleteAbsoluteLoss (Fin.snoc p.1.1 p.1.2) p.2)
      (((Measure.pi fun _ : Fin (r + 1) => μ).prod μ).prod μ) := by
  classical
  let P := Measure.pi (fun _ : Fin (r + 1) => μ)
  let Q := P.prod μ
  let R := Q.prod μ
  let yplus := fun q : (Fin (r + 1) → LOOConcentration.Observation 1 1) ×
      LOOConcentration.Observation 1 1 =>
    (∑ i : Fin (r + 1), (q.1 i).2 0 + q.2.2 0) / (((r + 1) + 1 : ℕ) : ℝ)
  let aplus := fun q : (Fin (r + 1) → LOOConcentration.Observation 1 1) ×
      LOOConcentration.Observation 1 1 =>
    (∑ i : Fin (r + 1), (q.1 i).1 0 + q.2.1 0) / (((r + 1) + 1 : ℕ) : ℝ)
  let S : ℝ := b.val / (2 * Real.sqrt δ.val)
  have hYplus := ridge_snoc_average_integrable_and_integral μ (r+1) (by omega)
    (fun z => z.2 0) (by
      apply hY1.mono' (by fun_prop)
      filter_upwards with z
      exact le_rfl)
  have hAplus := ridge_snoc_average_integrable_and_integral μ (r+1) (by omega)
    (fun z => z.1 0) (by
      apply hX1.mono' (by fun_prop)
      filter_upwards with z
      exact le_rfl)
  have hYplusAbs : Integrable (fun q => |yplus q|) Q := by
    have hNpos : 0 < (((r + 1) + 1 : ℕ) : ℝ) := by positivity
    simpa [P, Q, yplus, Nat.cast_add, Nat.cast_one, abs_div,
      abs_of_pos hNpos] using hYplus.1.norm
  have hAplusAbs : Integrable (fun q => |aplus q|) Q := by
    have hNpos : 0 < (((r + 1) + 1 : ℕ) : ℝ) := by positivity
    simpa [P, Q, aplus, Nat.cast_add, Nat.cast_one, abs_div,
      abs_of_pos hNpos] using hAplus.1.norm
  have hYplusR := ridge_prod_fst_integral Q μ (fun q => |yplus q|) hYplusAbs
  have hAplusR := ridge_prod_fst_integral Q μ (fun q => |aplus q|) hAplusAbs
  have hXR := ridge_prod_snd_integral Q μ (fun z => |z.1 0|) hX1
  have hYR := ridge_prod_snd_integral Q μ (fun z => |z.2 0|) hY1
  have hS : 0 ≤ S := by
    dsimp [S]
    exact div_nonneg b.property.le
      (le_of_lt (mul_pos (by norm_num) (Real.sqrt_pos.2 δ.property)))
  have hEnvInt : Integrable
      (fun p : ((Fin (r + 1) → LOOConcentration.Observation 1 1) ×
          LOOConcentration.Observation 1 1) × LOOConcentration.Observation 1 1 =>
        |yplus p.1| + S * |p.2.1 0| + S * |aplus p.1| + |p.2.2 0|) R := by
    have hEq : (fun p : ((Fin (r + 1) → LOOConcentration.Observation 1 1) ×
        LOOConcentration.Observation 1 1) × LOOConcentration.Observation 1 1 =>
        |yplus p.1| + S * |p.2.1 0| + S * |aplus p.1| + |p.2.2 0|) =
        (fun p => |yplus p.1|) +
          ((fun p => S * |p.2.1 0|) +
            ((fun p => S * |aplus p.1|) + (fun p => |p.2.2 0|))) := by
      funext p
      simp only [Pi.add_apply]
      ring
    rw [hEq]
    exact hYplusR.1.add ((hXR.1.const_mul S).add
      ((hAplusR.1.const_mul S).add hYR.1))
  have hMeas : Measurable
      (fun p : ((Fin (r + 1) → LOOConcentration.Observation 1 1) ×
          LOOConcentration.Observation 1 1) × LOOConcentration.Observation 1 1 =>
        LOOConcentration.fittedLoss
          (LOOConcentration.Manuscript.stabilizedLinearEstimator b δ (r + 1))
          ridgeDeleteAbsoluteLoss (Fin.snoc p.1.1 p.1.2) p.2) := by
    dsimp [LOOConcentration.fittedLoss, ridgeDeleteAbsoluteLoss,
      LOOConcentration.Manuscript.stabilizedLinearEstimator]
    fun_prop
  apply hEnvInt.mono' hMeas.aestronglyMeasurable
  filter_upwards with p
  rw [Real.norm_eq_abs]
  change |ridgeDeleteAbsoluteLoss
    ((LOOConcentration.Manuscript.stabilizedLinearEstimator b δ (r + 1)
      (Fin.snoc p.1.1 p.1.2)) p.2.1) p.2.2| ≤ _
  simp only [ridgeDeleteAbsoluteLoss, abs_abs]
  have hcoord : p.2.1 = (fun _ : Fin 1 => p.2.1 0) := by
    funext i
    fin_cases i
    rfl
  calc
    _ ≤ |((LOOConcentration.Manuscript.stabilizedLinearEstimator b δ (r + 1)
        (Fin.snoc p.1.1 p.1.2)) (fun _ : Fin 1 => p.2.1 0)) 0| + |p.2.2 0| := abs_sub _ _
    _ ≤ |yplus p.1| + S * |p.2.1 0| + S * |aplus p.1| + |p.2.2 0| := by
      have hB := ridge_actual_predictor_abs_bound (r + 1)
        (Fin.snoc p.1.1 p.1.2) b δ (p.2.1 0)
      simpa only [S, yplus, aplus, Nat.cast_add, Nat.cast_one,
        Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last] using
        add_le_add_left hB |p.2.2 0|
