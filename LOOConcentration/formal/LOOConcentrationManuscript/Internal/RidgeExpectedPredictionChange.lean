import LOOConcentrationManuscript.Internal.RidgeAddOneSlopeMoments
import LOOConcentrationManuscript.Internal.RidgeAddOneSlopeBoundConsumer
import LOOConcentrationManuscript.Internal.RidgeExpectedDeleteBiasConsumer
import LOOConcentrationManuscript.Internal.RidgeExpectedDeleteBias
import LOOConcentration.Probability.SampleTestLaw
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

private theorem ridge_difference_square_bound
    {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (f g : α → ℝ)
    (hf : Integrable (fun x => (f x) ^ 2) ν)
    (hg : Integrable (fun x => (g x) ^ 2) ν)
    (hfmeas : AEStronglyMeasurable f ν)
    (hgmeas : AEStronglyMeasurable g ν) :
    Integrable (fun x => (f x - g x) ^ 2) ν ∧
      (∫ x, (f x - g x) ^ 2 ∂ν) ≤
        2 * (∫ x, (f x) ^ 2 ∂ν) + 2 * (∫ x, (g x) ^ 2 ∂ν) := by
  have hMajor : Integrable (fun x => 2 * (f x) ^ 2 + 2 * (g x) ^ 2) ν := by
    change Integrable ((fun x => 2 * (f x) ^ 2) + (fun x => 2 * (g x) ^ 2)) ν
    exact (hf.const_mul 2).add (hg.const_mul 2)
  have hPoint (x : α) : (f x - g x) ^ 2 ≤ 2 * (f x) ^ 2 + 2 * (g x) ^ 2 := by
    nlinarith [sq_nonneg (f x + g x)]
  have hDiff : Integrable (fun x => (f x - g x) ^ 2) ν := by
    apply hMajor.mono' ((hfmeas.sub hgmeas).pow 2)
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hPoint x
  refine ⟨hDiff, ?_⟩
  calc
    _ ≤ ∫ x, 2 * (f x) ^ 2 + 2 * (g x) ^ 2 ∂ν := integral_mono hDiff hMajor hPoint
    _ = 2 * (∫ x, (f x) ^ 2 ∂ν) + 2 * (∫ x, (g x) ^ 2 ∂ν) := by
      rw [integral_add (hf.const_mul 2) (hg.const_mul 2),
        integral_const_mul, integral_const_mul]

private theorem ridge_average_abs_le {N : ℕ} (hN : 0 < (N : ℝ))
    (f : Fin N → ℝ) :
    |(∑ i : Fin N, f i) / (N : ℝ)| ≤
      (∑ i : Fin N, |f i|) / (N : ℝ) := by
  have hsum := Finset.abs_sum_le_sum_abs (s := Finset.univ) f
  rw [abs_div, abs_of_pos hN]
  exact div_le_div_of_nonneg_right hsum hN.le

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

private def ridgeActualSnocFeatureAverage (r : ℕ)
    (q : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) ×
      LOOConcentration.Observation 1 1) : ℝ :=
  (∑ i : Fin (r + 2),
    ((Fin.snoc q.1 q.2 : LOOConcentration.Dataset
      (LOOConcentration.Observation 1 1) (r + 2)) i).1 0) / (r + 2 : ℝ)

private def ridgeActualSnocTestCenter (r : ℕ)
    (p : (LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) ×
      LOOConcentration.Observation 1 1) × LOOConcentration.Observation 1 1) : ℝ :=
  (p.2).1 0 - ridgeActualSnocFeatureAverage r p.1

/-- The affine coefficient used below is read from the public fitted
predictor, rather than from a separate estimator definition. -/
private theorem ridge_actual_predictor_affine
    (r : ℕ)
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1))
    (b δ : {t : ℝ // 0 < t}) (x : ℝ) :
    let N : ℝ := ((r + 1 : ℕ) : ℝ)
    let X := LOOConcentrationManuscript.featureValues D
    let a : ℝ := (∑ i : Fin (r + 1), X i) / N
    let ybar : ℝ := (∑ i : Fin (r + 1), (D i).2 0) / N
    ((LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r D)
      (fun _ : Fin 1 => x)) 0 =
      ybar + ridgeActualPublicSlope b δ r D * (x - a) := by
  classical
  let N : ℝ := ((r + 1 : ℕ) : ℝ)
  let X := LOOConcentrationManuscript.featureValues D
  let U := LOOConcentrationManuscript.clippedResponseValues D b.val
  let a : ℝ := (∑ i : Fin (r + 1), X i) / N
  let c : ℝ := (∑ i : Fin (r + 1), U i) / N
  let v : ℝ := (∑ i : Fin (r + 1), (X i - a) ^ 2) / N
  let s : ℝ := (∑ i : Fin (r + 1), (X i - a) * (U i - c)) / N
  let ybar : ℝ := (∑ i : Fin (r + 1), (D i).2 0) / N
  let beta : ℝ := s / (v + δ.val)
  have hEval := ridge_actual_public_predictor_eval_formula r D b δ x
  have hOne := ridge_actual_public_predictor_eval_formula r D b δ 1
  have hZero := ridge_actual_public_predictor_eval_formula r D b δ 0
  have hEval' :
      ((LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r D)
        (fun _ : Fin 1 => x)) 0 = ybar + beta * (x - a) := by
    simpa [N, X, U, a, c, v, s, ybar, beta] using hEval
  have hOne' :
      ((LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r D)
        (fun _ : Fin 1 => 1)) 0 = ybar + beta * (1 - a) := by
    simpa [N, X, U, a, c, v, s, ybar, beta] using hOne
  have hZero' :
      ((LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r D)
        (fun _ : Fin 1 => 0)) 0 = ybar + beta * (0 - a) := by
    simpa [N, X, U, a, c, v, s, ybar, beta] using hZero
  have hBeta : beta = ridgeActualPublicSlope b δ r D := by
    dsimp [ridgeActualPublicSlope]
    rw [hOne', hZero']
    dsimp [beta]
    ring
  rw [hEval', hBeta]

/-- Exact add-one identity for the actual public Ridge predictor. Here the
short sample has `r+1` observations and the long sample has `r+2`. -/
theorem ridge_actual_add_one_prediction_change_identity
    (r : ℕ)
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1))
    (z : LOOConcentration.Observation 1 1)
    (b δ : {t : ℝ // 0 < t}) (x : ℝ) :
    let N : ℝ := ((r + 1 : ℕ) : ℝ)
    let a : ℝ := (∑ i : Fin (r + 1), (D i).1 0) / N
    let ap : ℝ :=
      (∑ i : Fin (r + 2), ((Fin.snoc D z :
        LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 2)) i).1 0) /
        (N + 1)
    let ybar : ℝ := (∑ i : Fin (r + 1), (D i).2 0) / N
    ((LOOConcentration.Manuscript.stabilizedLinearEstimator b δ (r + 1)
        (Fin.snoc D z) (fun _ : Fin 1 => x)) 0 -
      (LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r D
        (fun _ : Fin 1 => x)) 0) =
      (z.2 0 - ybar) / (N + 1) +
        (ridgeActualPublicSlope b δ (r + 1) (Fin.snoc D z) -
          ridgeActualPublicSlope b δ r D) * (x - ap) -
        ridgeActualPublicSlope b δ r D * (z.1 0 - a) / (N + 1) := by
  classical
  let N : ℝ := ((r + 1 : ℕ) : ℝ)
  let a : ℝ := (∑ i : Fin (r + 1), (D i).1 0) / N
  let ap : ℝ := (∑ i : Fin (r + 2),
    ((Fin.snoc D z : LOOConcentration.Dataset
      (LOOConcentration.Observation 1 1) (r + 2)) i).1 0) / (N + 1)
  let ybar : ℝ := (∑ i : Fin (r + 1), (D i).2 0) / N
  let ybarp : ℝ := (∑ i : Fin (r + 2),
    ((Fin.snoc D z : LOOConcentration.Dataset
      (LOOConcentration.Observation 1 1) (r + 2)) i).2 0) / (N + 1)
  let beta := ridgeActualPublicSlope b δ r D
  let betap := ridgeActualPublicSlope b δ (r + 1) (Fin.snoc D z)
  let d := z.1 0 - a
  have hN : 0 < N := by dsimp [N]; positivity
  have hNp : 0 < N + 1 := by positivity
  have hSumX : (∑ i : Fin (r + 2),
      ((Fin.snoc D z : LOOConcentration.Dataset
        (LOOConcentration.Observation 1 1) (r + 2)) i).1 0) =
      (∑ i : Fin (r + 1), (D i).1 0) + z.1 0 := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
  have hSumY : (∑ i : Fin (r + 2),
      ((Fin.snoc D z : LOOConcentration.Dataset
        (LOOConcentration.Observation 1 1) (r + 2)) i).2 0) =
      (∑ i : Fin (r + 1), (D i).2 0) + z.2 0 := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
  have hA : ap - a = d / (N + 1) := by
    dsimp [ap, a, d]
    rw [hSumX]
    field_simp [hN.ne', hNp.ne']
    ring
  have hYbar : ybarp = ((∑ i : Fin (r + 1), (D i).2 0) + z.2 0) / (N + 1) := by
    dsimp [ybarp]
    rw [hSumY]
  have hYbar' : ybarp = ybar + (z.2 0 - ybar) / (N + 1) := by
    rw [hYbar]
    dsimp [ybar]
    field_simp [hN.ne', hNp.ne']
    ring
  have hNew :
      ((LOOConcentration.Manuscript.stabilizedLinearEstimator b δ (r + 1)
        (Fin.snoc D z)) (fun _ : Fin 1 => x)) 0 = ybarp + betap * (x - ap) := by
    simpa [N, ybarp, ap, betap, LOOConcentrationManuscript.featureValues,
      Nat.cast_add, Nat.cast_one] using
      ridge_actual_predictor_affine (r + 1) (Fin.snoc D z) b δ x
  have hOld :
      ((LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r D)
        (fun _ : Fin 1 => x)) 0 = ybar + beta * (x - a) := by
    simpa [N, ybar, a, beta, LOOConcentrationManuscript.featureValues] using
      ridge_actual_predictor_affine r D b δ x
  have hDiff :
      ((LOOConcentration.Manuscript.stabilizedLinearEstimator b δ (r + 1)
        (Fin.snoc D z) (fun _ : Fin 1 => x)) 0 -
       (LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r D
        (fun _ : Fin 1 => x)) 0) =
        (z.2 0 - ybar) / (N + 1) + (betap - beta) * (x - ap) -
          beta * (z.1 0 - a) / (N + 1) := by
    rw [hNew, hOld, hYbar']
    have hQuery : x - a = (x - ap) + d / (N + 1) := by linarith [hA]
    rw [hQuery]
    ring
  change ((LOOConcentration.Manuscript.stabilizedLinearEstimator b δ (r + 1)
      (Fin.snoc D z) (fun _ : Fin 1 => x)) 0 -
    (LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r D
      (fun _ : Fin 1 => x)) 0) =
    (z.2 0 - ybar) / (N + 1) + (betap - beta) * (x - ap) -
      beta * (z.1 0 - a) / (N + 1)
  exact hDiff

private theorem ridge_actual_add_one_feature_mean_square_bound
    (μ : Measure (LOOConcentration.Observation 1 1)) [IsProbabilityMeasure μ]
    (hX2 : Integrable (fun z => (z.1 0) ^ 2) μ) (r : ℕ) :
    let Q := (Measure.pi fun _ : Fin (r + 1) => μ).prod μ
    let ap := fun q : LOOConcentration.Dataset
        (LOOConcentration.Observation 1 1) (r + 1) ×
        LOOConcentration.Observation 1 1 =>
      (∑ i : Fin (r + 2),
        ((Fin.snoc q.1 q.2 : LOOConcentration.Dataset
          (LOOConcentration.Observation 1 1) (r + 2)) i).1 0) / (r + 2 : ℝ)
    Integrable (fun q => (ap q) ^ 2) Q ∧
      (∫ q, (ap q) ^ 2 ∂Q) ≤ ∫ z, (z.1 0) ^ 2 ∂μ := by
  classical
  let Q := (Measure.pi fun _ : Fin (r + 1) => μ).prod μ
  let ap := fun q : LOOConcentration.Dataset
      (LOOConcentration.Observation 1 1) (r + 1) ×
      LOOConcentration.Observation 1 1 =>
    (∑ i : Fin (r + 2),
      ((Fin.snoc q.1 q.2 : LOOConcentration.Dataset
        (LOOConcentration.Observation 1 1) (r + 2)) i).1 0) / (r + 2 : ℝ)
  let avgSq := fun q : LOOConcentration.Dataset
      (LOOConcentration.Observation 1 1) (r + 1) ×
      LOOConcentration.Observation 1 1 =>
    (((∑ i : Fin (r + 1), ((q.1 i).1 0) ^ 2)) + ((q.2).1 0) ^ 2) /
      ((r + 1 + 1 : ℕ) : ℝ)
  have hN : 0 < r + 1 := by omega
  have hAvg := ridge_snoc_average_integrable_and_integral μ (r + 1) hN
    (fun z => (z.1 0) ^ 2) hX2
  have hAvgSqInt : Integrable avgSq Q := by
    simpa only [avgSq, Q, Nat.cast_add, Nat.cast_one] using hAvg.1
  have hAvgSqIntegral : (∫ q, avgSq q ∂Q) = ∫ z, (z.1 0) ^ 2 ∂μ := by
    simpa only [avgSq, Q, Nat.cast_add, Nat.cast_one] using hAvg.2
  have hMeanSq (q : LOOConcentration.Dataset
      (LOOConcentration.Observation 1 1) (r + 1) ×
      LOOConcentration.Observation 1 1) : (ap q) ^ 2 ≤ avgSq q := by
    have hSum : (∑ i : Fin (r + 2),
        ((Fin.snoc q.1 q.2 : LOOConcentration.Dataset
          (LOOConcentration.Observation 1 1) (r + 2)) i).1 0 ^ 2) =
        (∑ i : Fin (r + 1), ((q.1 i).1 0) ^ 2) + ((q.2).1 0) ^ 2 := by
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
    have hCS := ridge_mean_square_le_average_square (by omega)
      (fun i => ((Fin.snoc q.1 q.2 : LOOConcentration.Dataset
        (LOOConcentration.Observation 1 1) (r + 2)) i).1 0)
    have hden : (r : ℝ) + 2 = ((r + 1 + 1 : ℕ) : ℝ) := by
      push_cast
      ring
    calc
      _ ≤ (∑ i : Fin (r + 2),
          ((Fin.snoc q.1 q.2 : LOOConcentration.Dataset
            (LOOConcentration.Observation 1 1) (r + 2)) i).1 0 ^ 2) /
            ((r : ℝ) + 2) := by
          change ((∑ i : Fin (r + 2),
            ((Fin.snoc q.1 q.2 : LOOConcentration.Dataset
              (LOOConcentration.Observation 1 1) (r + 2)) i).1 0) / ((r : ℝ) + 2)) ^ 2 ≤ _
          have hCS' := hCS
          rw [← hden] at hCS'
          exact hCS'
      _ = avgSq q := by
        dsimp [avgSq]
        rw [hSum, hden]
  have hApSqInt : Integrable (fun q => (ap q) ^ 2) Q := by
    apply hAvgSqInt.mono' (by fun_prop)
    filter_upwards with q
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hMeanSq q
  refine ⟨hApSqInt, ?_⟩
  calc
    _ ≤ ∫ q, avgSq q ∂Q := integral_mono hApSqInt hAvgSqInt hMeanSq
    _ = ∫ z, (z.1 0) ^ 2 ∂μ := hAvgSqIntegral

private theorem ridge_actual_public_slope_abs_bound
    (r : ℕ)
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1))
    (b δ : {t : ℝ // 0 < t}) :
    |ridgeActualPublicSlope b δ r D| ≤ b.val / (2 * Real.sqrt δ.val) := by
  let N : ℝ := ((r + 1 : ℕ) : ℝ)
  let X := LOOConcentrationManuscript.featureValues D
  let U := LOOConcentrationManuscript.clippedResponseValues D b.val
  let a : ℝ := (∑ i : Fin (r + 1), X i) / N
  let c : ℝ := (∑ i : Fin (r + 1), U i) / N
  let v : ℝ := (∑ i : Fin (r + 1), (X i - a) ^ 2) / N
  let s : ℝ := (∑ i : Fin (r + 1), (X i - a) * (U i - c)) / N
  let beta : ℝ := s / (v + δ.val)
  let S : ℝ := b.val / (2 * Real.sqrt δ.val)
  have hSlope := LOOConcentrationManuscript.Internal.ridgePredictor_actual_query_derivative_and_slope_bound
    r D b.val δ.val b.property δ.property
  have hBeta : |beta| ≤ S := by
    simpa [X, U, a, c, v, s, beta, N, S,
      LOOConcentrationManuscript.featureValues,
      LOOConcentrationManuscript.clippedResponseValues,
      Nat.cast_add, Nat.cast_one] using (hSlope 0).2
  let ybar : ℝ := (∑ i : Fin (r + 1), (D i).2 0) / N
  have hOne : ((LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r D)
      (fun _ : Fin 1 => 1)) 0 = ybar + beta * (1 - a) := by
    simpa [N, X, U, a, c, v, s, beta, ybar,
      LOOConcentrationManuscript.featureValues,
      LOOConcentrationManuscript.clippedResponseValues] using
      ridge_actual_public_predictor_eval_formula r D b δ 1
  have hZero : ((LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r D)
      (fun _ : Fin 1 => 0)) 0 = ybar + beta * (0 - a) := by
    simpa [N, X, U, a, c, v, s, beta, ybar,
      LOOConcentrationManuscript.featureValues,
      LOOConcentrationManuscript.clippedResponseValues] using
      ridge_actual_public_predictor_eval_formula r D b δ 0
  have hEq : ridgeActualPublicSlope b δ r D = beta := by
    dsimp [ridgeActualPublicSlope]
    rw [hOne, hZero]
    ring
  rw [hEq]
  simpa only [S] using hBeta

noncomputable def ridgeActualAddOnePredictionChangeAbs (r : ℕ)
    (b δ : {t : ℝ // 0 < t})
    (p : (LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) ×
      LOOConcentration.Observation 1 1) × LOOConcentration.Observation 1 1) : ℝ :=
  abs (((LOOConcentration.Manuscript.stabilizedLinearEstimator b δ (r + 1)
      (Fin.snoc p.1.1 p.1.2)) (fun _ : Fin 1 => (p.2).1 0)) 0 -
    ((LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r p.1.1)
      (fun _ : Fin 1 => (p.2).1 0)) 0)

/-- The expected absolute change of the literal public Ridge predictor under
the actual iid training, added-observation, and independent-test laws. The
constant is fixed before `r` and depends only on the source moments and
regularization parameters. -/
theorem ridge_actual_expected_prediction_change_L1
    (μ : Measure (LOOConcentration.Observation 1 1)) [IsProbabilityMeasure μ]
    (hY1 : Integrable (fun z => |z.2 0|) μ)
    (hX4 : Integrable (fun z => (z.1 0) ^ 4) μ)
    (b δ : {t : ℝ // 0 < t}) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ,
      let P := Measure.pi (fun _ : Fin (r + 1) => μ)
      let Q := P.prod μ
      let R := Q.prod μ
      Integrable (ridgeActualAddOnePredictionChangeAbs r b δ) R ∧
        integral R (ridgeActualAddOnePredictionChangeAbs r b δ) ≤ C / (r + 2 : ℝ) := by
  obtain ⟨K, hK, hSlope⟩ := ridge_actual_add_one_public_slope_difference_L2 μ hX4 b δ
  have hSource := ridge_actual_first_moment_feature_sq_source μ hX4 hY1
  have hX1 := hSource.1
  have hX2 := hSource.2.1
  have hX := hSource.2.2.1
  have hY := hSource.2.2.2
  let MY : ℝ := ∫ z, |z.2 0| ∂μ
  let MX : ℝ := ∫ z, |z.1 0| ∂μ
  let MX2 : ℝ := ∫ z, (z.1 0) ^ 2 ∂μ
  let S : ℝ := b.val / (2 * Real.sqrt δ.val)
  let Cmid : ℝ := Real.sqrt K * Real.sqrt (4 * MX2)
  let C : ℝ := 1 + 2 * MY + Cmid + 2 * S * MX
  have hMY0 : 0 ≤ MY := by
    dsimp [MY]
    exact integral_nonneg (fun z => abs_nonneg (z.2 0))
  have hMX0 : 0 ≤ MX := by
    dsimp [MX]
    exact integral_nonneg (fun z => abs_nonneg (z.1 0))
  have hMX20 : 0 ≤ MX2 := by
    dsimp [MX2]
    exact integral_nonneg (fun z => sq_nonneg (z.1 0))
  have hS0 : 0 ≤ S := by
    dsimp [S]
    exact div_nonneg b.property.le
      (le_of_lt (mul_pos (by norm_num) (Real.sqrt_pos.2 δ.property)))
  refine ⟨C, ?_, ?_⟩
  · dsimp [C, Cmid]
    positivity
  · intro r P Q R
    classical
    let actualChangeAbs := ridgeActualAddOnePredictionChangeAbs r b δ
    let N : ℝ := ((r + 1 : ℕ) : ℝ)
    let den : ℝ := N + 1
    let ybar := fun D : LOOConcentration.Dataset
        (LOOConcentration.Observation 1 1) (r + 1) =>
      (∑ i : Fin (r + 1), (D i).2 0) / N
    let abar := fun D : LOOConcentration.Dataset
        (LOOConcentration.Observation 1 1) (r + 1) =>
      (∑ i : Fin (r + 1), (D i).1 0) / N
    let ap := ridgeActualSnocFeatureAverage r
    let slopeDiff := fun q : LOOConcentration.Dataset
        (LOOConcentration.Observation 1 1) (r + 1) ×
        LOOConcentration.Observation 1 1 =>
      ridgeActualPublicSlope b δ (r + 1) (Fin.snoc q.1 q.2) -
        ridgeActualPublicSlope b δ r q.1
    let yChange := fun q : LOOConcentration.Dataset
        (LOOConcentration.Observation 1 1) (r + 1) ×
        LOOConcentration.Observation 1 1 => |(q.2).2 0 - ybar q.1|
    let xChange := fun q : LOOConcentration.Dataset
        (LOOConcentration.Observation 1 1) (r + 1) ×
        LOOConcentration.Observation 1 1 => |(q.2).1 0 - abar q.1|
    let center := fun p : (LOOConcentration.Dataset
        (LOOConcentration.Observation 1 1) (r + 1) ×
        LOOConcentration.Observation 1 1) × LOOConcentration.Observation 1 1 =>
      (p.2).1 0 - ap p.1
    have hN : 0 < N := by dsimp [N]; positivity
    have hden : 0 < den := by dsimp [den]; positivity
    have hP : P = Measure.pi (fun _ : Fin (r + 1) => μ) := rfl
    have hQ : Q = P.prod μ := rfl
    have hR : R = Q.prod μ := rfl
    have hYbarStat := ridge_pi_average_integrable_and_integral μ (r + 1)
      (by omega) (fun z => z.2 0) hY
    have hAbarStat := ridge_pi_average_integrable_and_integral μ (r + 1)
      (by omega) (fun z => z.1 0) hX
    have hYbarAbsMean := ridge_pi_average_abs_mean_bound μ (r + 1)
      (by positivity) (fun z => z.2 0) hY hY1
    have hAbarAbsMean := ridge_pi_average_abs_mean_bound μ (r + 1)
      (by positivity) (fun z => z.1 0) hX hX1
    have hYbarAbsInt : Integrable (fun D => |ybar D|) P := by
      change Integrable (fun D : Fin (r + 1) → LOOConcentration.Observation 1 1 =>
        |ybar D|) P
      simpa only [ybar, N, Real.norm_eq_abs] using hYbarStat.1.norm
    have hAbarAbsInt : Integrable (fun D => |abar D|) P := by
      change Integrable (fun D : Fin (r + 1) → LOOConcentration.Observation 1 1 =>
        |abar D|) P
      simpa only [abar, N, Real.norm_eq_abs] using hAbarStat.1.norm
    have hYbarQ := ridge_prod_fst_integral P μ (fun D => |ybar D|) hYbarAbsInt
    have hAbarQ := ridge_prod_fst_integral P μ (fun D => |abar D|) hAbarAbsInt
    have hYaddQ := ridge_prod_snd_integral P μ (fun z => |z.2 0|) hY1
    have hXaddQ := ridge_prod_snd_integral P μ (fun z => |z.1 0|) hX1
    have hYmajor : Integrable (fun q : LOOConcentration.Dataset
        (LOOConcentration.Observation 1 1) (r + 1) ×
        LOOConcentration.Observation 1 1 =>
          |(q.2).2 0| + |ybar q.1|) Q := by
      change Integrable ((fun q => |(q.2).2 0|) + (fun q => |ybar q.1|)) Q
      simpa only [hP, hQ] using hYaddQ.1.add hYbarQ.1
    have hXmajor : Integrable (fun q : LOOConcentration.Dataset
        (LOOConcentration.Observation 1 1) (r + 1) ×
        LOOConcentration.Observation 1 1 =>
          |(q.2).1 0| + |abar q.1|) Q := by
      change Integrable ((fun q => |(q.2).1 0|) + (fun q => |abar q.1|)) Q
      simpa only [hP, hQ] using hXaddQ.1.add hAbarQ.1
    have hyChangeInt : Integrable yChange Q := by
      apply hYmajor.mono' (by fun_prop)
      filter_upwards with q
      rw [Real.norm_eq_abs]
      dsimp [yChange]
      rw [abs_abs]
      exact abs_sub _ _
    have hxChangeInt : Integrable xChange Q := by
      apply hXmajor.mono' (by fun_prop)
      filter_upwards with q
      rw [Real.norm_eq_abs]
      dsimp [xChange]
      rw [abs_abs]
      exact abs_sub _ _
    have hyChangeBound : (∫ q, yChange q ∂Q) ≤ 2 * MY := by
      calc
        _ ≤ ∫ q : LOOConcentration.Dataset (LOOConcentration.Observation 1 1)
            (r + 1) × LOOConcentration.Observation 1 1,
            |(q.2).2 0| + |ybar q.1| ∂Q := integral_mono hyChangeInt hYmajor
            (fun q => abs_sub _ _)
        _ = (∫ z, |z.2 0| ∂μ) + ∫ D, |ybar D| ∂P := by
          rw [integral_add hYaddQ.1 hYbarQ.1, hYaddQ.2, hYbarQ.2]
        _ ≤ MY + MY := by
          dsimp [MY]
          linarith [hYbarAbsMean]
        _ = 2 * MY := by ring
    have hxChangeBound : (∫ q, xChange q ∂Q) ≤ 2 * MX := by
      calc
        _ ≤ ∫ q : LOOConcentration.Dataset (LOOConcentration.Observation 1 1)
            (r + 1) × LOOConcentration.Observation 1 1,
            |(q.2).1 0| + |abar q.1| ∂Q := integral_mono hxChangeInt hXmajor
              (fun q => abs_sub _ _)
        _ = (∫ z, |z.1 0| ∂μ) + ∫ D, |abar D| ∂P := by
          rw [integral_add hXaddQ.1 hAbarQ.1, hXaddQ.2, hAbarQ.2]
        _ ≤ MX + MX := by
          dsimp [MX]
          linarith [hAbarAbsMean]
        _ = 2 * MX := by ring
    have hyChangeR := ridge_prod_fst_integral Q μ yChange hyChangeInt
    have hxChangeR := ridge_prod_fst_integral Q μ xChange hxChangeInt
    have hSlopeData := hSlope r
    have hSlopeQ : MemLp slopeDiff 2 Q := by
      simpa only [slopeDiff, Q, N] using hSlopeData.1
    have hSlopeQSq := hSlopeQ.integrable_sq
    have hSlopeQBound : (∫ q, (slopeDiff q) ^ 2 ∂Q) ≤ K / den ^ 2 := by
      have hDen : den = (r : ℝ) + 1 + 1 := by
        dsimp [den, N]
        push_cast
        ring
      rw [hDen]
      change (∫ q, (slopeDiff q) ^ 2 ∂(Measure.pi (fun _ : Fin (r + 1) => μ)).prod μ) ≤
        K / ((r : ℝ) + 1 + 1) ^ 2
      simpa only [slopeDiff, Nat.cast_add, Nat.cast_one] using hSlopeData.2
    have hSlopeRSq := ridge_prod_fst_integral Q μ
      (fun q => (slopeDiff q) ^ 2) hSlopeQSq
    have hSlopeRSqBound : integral R (fun p => (slopeDiff p.1) ^ 2) ≤ K / den ^ 2 := by
      calc
        _ = integral Q (fun q => (slopeDiff q) ^ 2) := by
          simpa only [hR] using hSlopeRSq.2
        _ ≤ K / den ^ 2 := hSlopeQBound
    have hSlopeR : MemLp (fun p => slopeDiff p.1) 2 R := by
      simpa only [hR] using hSlopeQ.comp_fst μ
    have hApSq := ridge_actual_add_one_feature_mean_square_bound μ hX2 r
    have hApSqInt : Integrable (fun q => (ap q) ^ 2) Q := by
      simpa only [ap, ridgeActualSnocFeatureAverage, Q] using hApSq.1
    have hApSqBound : (∫ q, (ap q) ^ 2 ∂Q) ≤ MX2 := by
      simpa only [ap, ridgeActualSnocFeatureAverage, Q, MX2] using hApSq.2
    have hApSqR := ridge_prod_fst_integral Q μ (fun q => (ap q) ^ 2) hApSqInt
    have hX2R := ridge_prod_snd_integral Q μ (fun z => (z.1 0) ^ 2) hX2
    have hTestXMeas : AEStronglyMeasurable
        (fun p : (LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) ×
          LOOConcentration.Observation 1 1) × LOOConcentration.Observation 1 1 =>
        (p.2).1 0) R := by fun_prop
    have hApMeas : AEStronglyMeasurable
        (fun p : (LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) ×
          LOOConcentration.Observation 1 1) × LOOConcentration.Observation 1 1 =>
        ap p.1) R := by
      change AEStronglyMeasurable
        (fun p : (LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) ×
          LOOConcentration.Observation 1 1) × LOOConcentration.Observation 1 1 =>
          ridgeActualSnocFeatureAverage r p.1) R
      fun_prop [ridgeActualSnocFeatureAverage]
    have hCenterSqInfo := ridge_difference_square_bound R
      (fun p : (LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) ×
          LOOConcentration.Observation 1 1) × LOOConcentration.Observation 1 1 =>
        (p.2).1 0)
      (fun p : (LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) ×
          LOOConcentration.Observation 1 1) × LOOConcentration.Observation 1 1 =>
        ap p.1) hX2R.1 hApSqR.1 hTestXMeas hApMeas
    have hCenterSqInt : Integrable (fun p => (center p) ^ 2) R := by
      simpa only [center] using hCenterSqInfo.1
    have hCenterSqBound : integral R (fun p => (center p) ^ 2) ≤ 4 * MX2 := by
      have hBound := hCenterSqInfo.2
      rw [hX2R.2, hApSqR.2] at hBound
      have hAvgBound : (∫ q, (ap q) ^ 2 ∂Q) ≤ MX2 := by
        simpa only [MX2] using hApSqBound
      calc
        _ ≤ 2 * (∫ z, (z.1 0) ^ 2 ∂μ) + 2 * (∫ q, (ap q) ^ 2 ∂Q) := by
          simpa only [center] using hBound
        _ ≤ 2 * MX2 + 2 * MX2 := by
          dsimp [MX2]
          nlinarith [hAvgBound]
        _ = 4 * MX2 := by ring
    have hCenterMem : MemLp center 2 R := by
      have hCenterMeas : AEStronglyMeasurable center R := by
        change AEStronglyMeasurable (fun p => (p.2).1 0 - ap p.1) R
        exact hTestXMeas.sub hApMeas
      apply (memLp_two_iff_integrable_sq hCenterMeas).2
      exact hCenterSqInt
    have hSlopeRHolder : MemLp (fun p => slopeDiff p.1) (ENNReal.ofReal (2 : ℝ)) R := by
      simpa using hSlopeR
    have hCenterHolder : MemLp center (ENNReal.ofReal (2 : ℝ)) R := by
      simpa using hCenterMem
    have hMidInt : Integrable
        (fun p => |slopeDiff p.1| * |center p|) R := by
      have hProd : MemLp (fun p => slopeDiff p.1 * center p) 1 R := by
        exact hCenterMem.mul hSlopeR
      have hProdInt : Integrable (fun p => slopeDiff p.1 * center p) R :=
        (memLp_one_iff_integrable).1 hProd
      convert hProdInt.norm using 1
      ext p
      rw [Real.norm_eq_abs, abs_mul]
    have hHolder := integral_mul_norm_le_Lp_mul_Lq
      (μ := R) Real.HolderConjugate.two_two hSlopeRHolder hCenterHolder
    have hMidHolder :
        integral R (fun p => |slopeDiff p.1| * |center p|) ≤
          (integral R (fun p => |slopeDiff p.1| ^ (2 : ℝ))) ^ (1 / (2 : ℝ)) *
            (integral R (fun p => |center p| ^ (2 : ℝ))) ^ (1 / (2 : ℝ)) := by
      calc
        _ = integral R (fun p => ‖slopeDiff p.1‖ * ‖center p‖) := by
          congr 1
        _ ≤ _ := by
          simpa only [Real.norm_eq_abs] using hHolder
    have hMidBound :
        integral R (fun p => |slopeDiff p.1| * |center p|) ≤ Cmid / den := by
      have hSqNorm1 : integral R (fun p => |slopeDiff p.1| ^ (2 : ℝ)) =
          integral R (fun p => (slopeDiff p.1) ^ 2) := by
        apply integral_congr_ae
        filter_upwards with p
        rw [Real.rpow_ofNat, sq_abs]
      have hSqNorm2 : integral R (fun p => |center p| ^ (2 : ℝ)) =
          integral R (fun p => (center p) ^ 2) := by
        apply integral_congr_ae
        filter_upwards with p
        rw [Real.rpow_ofNat, sq_abs]
      have hRootBound :
          (Real.sqrt (integral R (fun p => (slopeDiff p.1) ^ 2))) *
            Real.sqrt (integral R (fun p => (center p) ^ 2)) ≤
          Real.sqrt (K / den ^ 2) * Real.sqrt (4 * MX2) := by
        apply mul_le_mul
        · exact Real.sqrt_le_sqrt hSlopeRSqBound
        · exact Real.sqrt_le_sqrt hCenterSqBound
        · exact Real.sqrt_nonneg _
        · exact Real.sqrt_nonneg _
      rw [hSqNorm1, hSqNorm2, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
        at hMidHolder
      calc
        _ ≤ Real.sqrt (integral R (fun p => (slopeDiff p.1) ^ 2)) *
            Real.sqrt (integral R (fun p => (center p) ^ 2)) := hMidHolder
        _ ≤ Real.sqrt (K / den ^ 2) * Real.sqrt (4 * MX2) := hRootBound
        _ = Cmid / den := by
          dsimp [Cmid]
          rw [Real.sqrt_div (le_of_lt hK), Real.sqrt_sq_eq_abs, abs_of_pos hden]
          ring
    let termY := fun p : (LOOConcentration.Dataset
        (LOOConcentration.Observation 1 1) (r + 1) ×
        LOOConcentration.Observation 1 1) × LOOConcentration.Observation 1 1 =>
      den⁻¹ * yChange p.1
    let termSlope := fun p : (LOOConcentration.Dataset
        (LOOConcentration.Observation 1 1) (r + 1) ×
        LOOConcentration.Observation 1 1) × LOOConcentration.Observation 1 1 =>
      |slopeDiff p.1| * |center p|
    let termX := fun p : (LOOConcentration.Dataset
        (LOOConcentration.Observation 1 1) (r + 1) ×
        LOOConcentration.Observation 1 1) × LOOConcentration.Observation 1 1 =>
      (S / den) * xChange p.1
    let envelope := fun p => termY p + (termSlope p + termX p)
    have hTermYInt : Integrable termY R := by
      change Integrable (fun p => den⁻¹ * yChange p.1) R
      exact (hyChangeR.1.const_mul den⁻¹)
    have hTermSlopeInt : Integrable termSlope R := by
      exact hMidInt
    have hTermXInt : Integrable termX R := by
      change Integrable (fun p => (S / den) * xChange p.1) R
      exact hxChangeR.1.const_mul (S / den)
    have hEnvelopeInt : Integrable envelope R := by
      change Integrable ((fun p => termY p) +
        ((fun p => termSlope p) + (fun p => termX p))) R
      exact hTermYInt.add (hTermSlopeInt.add hTermXInt)
    have hTermYBound : integral R termY ≤ 2 * MY / den := by
      calc
        _ = den⁻¹ * integral R (fun p => yChange p.1) := by
          rw [show termY = fun p => den⁻¹ * yChange p.1 by rfl,
            integral_const_mul]
        _ = den⁻¹ * (∫ q, yChange q ∂Q) := by rw [hyChangeR.2]
        _ ≤ den⁻¹ * (2 * MY) :=
          mul_le_mul_of_nonneg_left hyChangeBound (inv_nonneg.mpr hden.le)
        _ = 2 * MY / den := by ring
    have hTermXBound : integral R termX ≤ 2 * S * MX / den := by
      calc
        _ = (S / den) * integral R (fun p => xChange p.1) := by
          rw [show termX = fun p => (S / den) * xChange p.1 by rfl,
            integral_const_mul]
        _ = (S / den) * (∫ q, xChange q ∂Q) := by rw [hxChangeR.2]
        _ ≤ (S / den) * (2 * MX) :=
          mul_le_mul_of_nonneg_left hxChangeBound (div_nonneg hS0 hden.le)
        _ = 2 * S * MX / den := by ring
    have hIdPoint (p : (LOOConcentration.Dataset
        (LOOConcentration.Observation 1 1) (r + 1) ×
        LOOConcentration.Observation 1 1) × LOOConcentration.Observation 1 1) :
        ((LOOConcentration.Manuscript.stabilizedLinearEstimator b δ (r + 1)
            (Fin.snoc p.1.1 p.1.2) (fun _ : Fin 1 => (p.2).1 0)) 0 -
          ((LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r p.1.1)
            (fun _ : Fin 1 => (p.2).1 0)) 0) =
        ((p.1.2).2 0 - ybar p.1.1) / den +
          slopeDiff p.1 * center p -
            ridgeActualPublicSlope b δ r p.1.1 *
              ((p.1.2).1 0 - abar p.1.1) / den := by
      have h := ridge_actual_add_one_prediction_change_identity r p.1.1 p.1.2 b δ
        ((p.2).1 0)
      have hcast : (↑r + 1 + 1 : ℝ) = ↑r + 2 := by ring
      simpa [N, den, ybar, abar, ap, center, slopeDiff,
        ridgeActualSnocFeatureAverage, Nat.cast_add, Nat.cast_one, hcast] using h
    have hOldSlopeBound (p : (LOOConcentration.Dataset
        (LOOConcentration.Observation 1 1) (r + 1) ×
        LOOConcentration.Observation 1 1) × LOOConcentration.Observation 1 1) :
        |ridgeActualPublicSlope b δ r p.1.1| ≤ S := by
      simpa only [S] using ridge_actual_public_slope_abs_bound r p.1.1 b δ
    have hPoint (p : (LOOConcentration.Dataset
        (LOOConcentration.Observation 1 1) (r + 1) ×
        LOOConcentration.Observation 1 1) × LOOConcentration.Observation 1 1) :
        actualChangeAbs p ≤ envelope p := by
      dsimp [actualChangeAbs, ridgeActualAddOnePredictionChangeAbs, envelope]
      rw [hIdPoint p]
      let A := ((p.1.2).2 0 - ybar p.1.1) / den
      let B := slopeDiff p.1 * center p
      let C0 := ridgeActualPublicSlope b δ r p.1.1 *
        ((p.1.2).1 0 - abar p.1.1) / den
      have hA : |A| = termY p := by
        dsimp [A, termY, yChange]
        rw [abs_div, abs_of_pos hden]
        ring
      have hB : |B| = termSlope p := by
        dsimp [B, termSlope]
        rw [abs_mul]
      have hC : |C0| ≤ termX p := by
        dsimp [C0, termX, xChange]
        calc
          _ = |ridgeActualPublicSlope b δ r p.1.1| *
              |(p.1.2).1 0 - abar p.1.1| / den := by
            rw [abs_div, abs_of_pos hden, abs_mul]
          _ ≤ S * |(p.1.2).1 0 - abar p.1.1| / den := by
            gcongr
            exact hOldSlopeBound p
          _ = _ := by ring
      calc
        _ = |A + B - C0| := by rfl
        _ ≤ |A + B| + |C0| := abs_sub _ _
        _ ≤ |A| + |B| + |C0| := by
          exact add_le_add_left (abs_add_le A B) _
        _ ≤ termY p + termSlope p + termX p := by
          rw [hA, hB]
          exact add_le_add le_rfl hC
        _ = termY p + (termSlope p + termX p) := add_assoc _ _ _
    have hChangeInt : Integrable actualChangeAbs R := by
      apply hEnvelopeInt.mono' (by
        have hCont : Continuous actualChangeAbs := by
          change Continuous (ridgeActualAddOnePredictionChangeAbs r b δ)
          unfold ridgeActualAddOnePredictionChangeAbs
          dsimp [LOOConcentration.Manuscript.stabilizedLinearEstimator]
          apply continuous_abs.comp
          apply Continuous.sub <;>
            (apply Continuous.add
             · fun_prop
             · apply Continuous.mul
               · apply Continuous.div
                 · fun_prop
                 · fun_prop
                 · intro p
                   exact ne_of_gt (add_pos_of_nonneg_of_pos
                     (mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
                     δ.property)
               · fun_prop)
        exact hCont.measurable.aestronglyMeasurable)
      filter_upwards with p
      simpa [actualChangeAbs, ridgeActualAddOnePredictionChangeAbs] using hPoint p
    have hIntBound : integral R actualChangeAbs ≤ C / den := by
      have hEnvelopeBound : integral R envelope ≤
          (2 * MY + Cmid + 2 * S * MX) / den := by
        calc
          _ = integral R termY +
              (integral R termSlope + integral R termX) := by
            exact (integral_add hTermYInt (hTermSlopeInt.add hTermXInt)).trans
              (congrArg (fun t => integral R termY + t)
                (integral_add hTermSlopeInt hTermXInt))
          _ ≤ 2 * MY / den + (Cmid / den + 2 * S * MX / den) :=
            add_le_add hTermYBound (add_le_add hMidBound hTermXBound)
          _ = (2 * MY + Cmid + 2 * S * MX) / den := by ring
      have hNum : 2 * MY + Cmid + 2 * S * MX ≤ C := by
        dsimp [C]
        linarith
      calc
        _ ≤ integral R envelope := integral_mono hChangeInt hEnvelopeInt hPoint
        _ ≤ C / den :=
          hEnvelopeBound.trans (div_le_div_of_nonneg_right hNum hden.le)
    have hDenEq : den = (r + 2 : ℝ) := by
      dsimp [den, N]
      simp only [Nat.cast_add, Nat.cast_one]
      ring
    constructor
    · simpa only [actualChangeAbs, P, Q, R, ridgeActualAddOnePredictionChangeAbs] using hChangeInt
    · simpa only [actualChangeAbs, P, Q, R, hDenEq, ridgeActualAddOnePredictionChangeAbs] using hIntBound

end
end LOOConcentration.Manuscript.Internal
