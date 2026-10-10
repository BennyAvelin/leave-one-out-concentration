import LOOConcentrationManuscript.Internal.NativeLSIFourthMoment
import LOOConcentrationManuscript.Internal.RidgeAddOneSlopeBoundConsumer
import LOOConcentrationManuscript.Internal.RidgePredictorQueryFeature
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

open MeasureTheory
open ProbabilityTheory
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

private theorem ridge_average_square_sq_le_average_fourth {N : ℕ} (hN : 0 < N)
    (x : Fin N → ℝ) :
    ((∑ i : Fin N, (x i) ^ 2) / (N : ℝ)) ^ 2 ≤
      (∑ i : Fin N, (x i) ^ 4) / (N : ℝ) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : Fin N => (1 : ℝ)) (fun i => (x i) ^ 2)
  have hsum : (∑ i : Fin N, (x i) ^ 2) ^ 2 ≤
      (N : ℝ) * ∑ i : Fin N, (x i) ^ 4 := by
    calc
      _ = (∑ i : Fin N, (1 : ℝ) * (x i) ^ 2) ^ 2 := by simp
      _ ≤ (∑ i : Fin N, (1 : ℝ) ^ 2) *
          ∑ i : Fin N, ((x i) ^ 2) ^ 2 := hcs
      _ = (N : ℝ) * ∑ i : Fin N, (x i) ^ 4 := by
        simp only [one_pow, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, mul_one]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        ring
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  rw [div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hNr)).2
  calc
    _ ≤ (N : ℝ) * ∑ i : Fin N, (x i) ^ 4 := hsum
    _ = ((∑ i : Fin N, (x i) ^ 4) / (N : ℝ)) * ((N : ℝ) ^ 2) := by
      field_simp [hNr]

private theorem ridge_empirical_variance_eq {N : ℕ} (hN : 0 < N)
    (x : Fin N → ℝ) :
    let a := (∑ i : Fin N, x i) / (N : ℝ)
    let q := (∑ i : Fin N, (x i) ^ 2) / (N : ℝ)
    let v := (∑ i : Fin N, (x i - a) ^ 2) / (N : ℝ)
    v = q - a ^ 2 := by
  intro a q v
  have hsum : (∑ i : Fin N, x i) = (N : ℝ) * a := by
    dsimp [a]
    field_simp
  have hexpand : (∑ i : Fin N, (x i - a) ^ 2) =
      (∑ i : Fin N, (x i) ^ 2) - (2 * a) * (∑ i : Fin N, x i) +
        (N : ℝ) * a ^ 2 := by
    calc
      _ = ∑ i : Fin N, ((x i) ^ 2 - 2 * a * x i + a ^ 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        rw [← Finset.mul_sum]
  have hcenter : (∑ i : Fin N, (x i - a) ^ 2) =
      (∑ i : Fin N, (x i) ^ 2) - (N : ℝ) * a ^ 2 := by
    rw [hexpand, hsum]
    ring
  dsimp [v, q]
  rw [hcenter]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  field_simp

private theorem ridge_integral_prod_fst
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

private theorem ridge_integral_prod_snd
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

private theorem ridge_sub_fourth_bound (x y : ℝ) :
    (x - y) ^ 4 ≤ 8 * (x ^ 4 + y ^ 4) := by
  nlinarith [sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x + y), sq_nonneg (x - y)]

/-- The two literal source fourth-moment estimates under the actual iid
sample and added-observation law. Integrability is proved internally. -/
theorem ridge_actual_add_one_feature_moments
    (μ : Measure (LOOConcentration.Observation 1 1)) [IsProbabilityMeasure μ]
    (hX4 : Integrable (fun z => (z.1 0) ^ 4) μ) (r : ℕ) :
    let N : ℝ := ((r + 1 : ℕ) : ℝ)
    let a := fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+1) =>
      (∑ i : Fin (r+1), (D i).1 0) / N
    let v := fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+1) =>
      (∑ i : Fin (r+1), ((D i).1 0 - a D) ^ 2) / N
    let Q := (Measure.pi fun _ : Fin (r+1) => μ).prod μ
    Integrable (fun q => (v q.1)^2) Q ∧
      (∫ q, (v q.1)^2 ∂Q) ≤ ∫ z, (z.1 0)^4 ∂μ ∧
      Integrable (fun q => ((q.2).1 0 - a q.1)^4) Q ∧
      (∫ q, ((q.2).1 0 - a q.1)^4 ∂Q) ≤ 16 * ∫ z, (z.1 0)^4 ∂μ := by
  classical
  intro N a v Q
  let P := Measure.pi fun _ : Fin (r+1) => μ
  let q2 := fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+1) =>
    (∑ i : Fin (r+1), ((D i).1 0)^2) / N
  let q4 := fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+1) =>
    (∑ i : Fin (r+1), ((D i).1 0)^4) / N
  have hN : 0 < r+1 := by omega
  have hNr : 0 < N := by dsimp [N]; positivity
  have hq2 : ∀ D, 0 ≤ q2 D := by intro D; dsimp [q2]; positivity
  have ha2 : ∀ D, (a D)^2 ≤ q2 D := by
    intro D
    exact ridge_mean_square_le_average_square hN (fun i => (D i).1 0)
  have hq24 : ∀ D, (q2 D)^2 ≤ q4 D := by
    intro D
    exact ridge_average_square_sq_le_average_fourth hN (fun i => (D i).1 0)
  have ha4 : ∀ D, (a D)^4 ≤ q4 D := by
    intro D
    have h := ((sq_le_sq₀ (sq_nonneg (a D)) (hq2 D)).2 (ha2 D)).trans (hq24 D)
    simpa only [← pow_mul] using h
  have hv : ∀ D, 0 ≤ v D ∧ (v D)^2 ≤ q4 D := by
    intro D
    have hv0 : 0 ≤ v D := by dsimp [v]; positivity
    have hid := ridge_empirical_variance_eq hN (fun i => (D i).1 0)
    change v D = q2 D - (a D)^2 at hid
    have hvq : v D ≤ q2 D := by linarith only [hid, sq_nonneg (a D)]
    exact ⟨hv0, ((sq_le_sq₀ hv0 (hq2 D)).2 hvq).trans (hq24 D)⟩
  have hq4Int := ridge_pi_average_integrable_and_integral μ (r+1) hN
    (fun z => (z.1 0)^4) hX4
  have hq4P : Integrable q4 P := hq4Int.1
  have hq4Eq : (∫ D, q4 D ∂P) = ∫ z, (z.1 0)^4 ∂μ := hq4Int.2
  have hq4Q := ridge_integral_prod_fst P μ q4 hq4P
  have hstarQ := ridge_integral_prod_snd P μ (fun z => (z.1 0)^4) hX4
  have hvInt : Integrable (fun q => (v q.1)^2) Q := by
    apply hq4Q.1.mono' (by dsimp [v, a]; fun_prop)
    filter_upwards with q
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (v q.1))]
    exact (hv q.1).2
  have hvBound : (∫ q, (v q.1)^2 ∂Q) ≤ ∫ z, (z.1 0)^4 ∂μ := by
    calc
      _ ≤ ∫ q, q4 q.1 ∂Q := integral_mono hvInt hq4Q.1 (fun q => (hv q.1).2)
      _ = ∫ z, (z.1 0)^4 ∂μ := hq4Q.2.trans hq4Eq
  let B := fun q : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+1) × LOOConcentration.Observation 1 1 => 8 * ((q.2).1 0 ^ 4 + q4 q.1)
  have hBInt : Integrable B Q := (hstarQ.1.add hq4Q.1).const_mul 8
  have hdPoint : ∀ q, ((q.2).1 0 - a q.1)^4 ≤ B q := by
    intro q
    exact (ridge_sub_fourth_bound ((q.2).1 0) (a q.1)).trans
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl (ha4 q.1)) (by norm_num))
  have hdMeas : Measurable (fun q : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+1) × LOOConcentration.Observation 1 1 => ((q.2).1 0 - a q.1)^4) := by
    dsimp [a]; fun_prop
  have hdInt : Integrable (fun q => ((q.2).1 0 - a q.1)^4) Q := by
    apply hBInt.mono' hdMeas.aestronglyMeasurable
    filter_upwards with q
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ((q.2).1 0 - a q.1)^4)]
      using hdPoint q
  refine ⟨hvInt, hvBound, hdInt, ?_⟩
  calc
    _ ≤ ∫ q, B q ∂Q := integral_mono hdInt hBInt hdPoint
    _ = 8 * ((∫ q, (q.2).1 0 ^ 4 ∂Q) + ∫ q, q4 q.1 ∂Q) := by
      rw [show B = (fun q => 8 * ((q.2).1 0 ^ 4 + q4 q.1)) by rfl,
        integral_const_mul, integral_add hstarQ.1 hq4Q.1]
    _ = 16 * ∫ z, (z.1 0)^4 ∂μ := by
      rw [hstarQ.2, hq4Q.2, hq4Eq]
      ring

/-- The Ridge source application internally derives its fourth-moment
premise from the original native LSI constant and second moment. -/
theorem ridge_nativeLSI_add_one_feature_moments
    (μ : Measure (LOOConcentration.Observation 1 1)) [IsProbabilityMeasure μ]
    (hFinite : LOOConcentration.Revision.observationLogSobolevConstant μ < ⊤)
    (hSecond : Integrable LOOConcentration.observationNormSq μ) :
    ∀ r : ℕ,
    let N : ℝ := ((r + 1 : ℕ) : ℝ)
    let a := fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+1) =>
      (∑ i : Fin (r+1), (D i).1 0) / N
    let v := fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+1) =>
      (∑ i : Fin (r+1), ((D i).1 0 - a D) ^ 2) / N
    let Q := (Measure.pi fun _ : Fin (r+1) => μ).prod μ
    Integrable (fun q => (v q.1)^2) Q ∧
      (∫ q, (v q.1)^2 ∂Q) ≤ ∫ z, (z.1 0)^4 ∂μ ∧
      Integrable (fun q => ((q.2).1 0 - a q.1)^4) Q ∧
      (∫ q, ((q.2).1 0 - a q.1)^4 ∂Q) ≤ 16 * ∫ z, (z.1 0)^4 ∂μ := by
  intro r
  exact ridge_actual_add_one_feature_moments μ
    (observation_nativeLSI_feature_fourth_moment μ hFinite hSecond).2 r

end
end LOOConcentration.Manuscript.Internal
