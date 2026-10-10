import LOOConcentrationManuscript.Internal.RidgeSlopeFeatureDerivative
import LOOConcentrationManuscript.Internal.RidgeSlopeBound
import LOOConcentrationManuscript.Internal.PositiveQuotientDerivative
import LOOConcentrationManuscript.Frozen.Definitions.StabilizedLinearEstimator

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

/-!
The source-literal response-coordinate derivative of the clipped ridge slope,
and its direct consumption by the public stabilized estimator.
-/

namespace LOOConcentrationManuscript

/-- Replace one scalar response while preserving the feature vector. -/
def varyResponse {N : ℕ}
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) N)
    (j : Fin N) (t : ℝ) :
    LOOConcentration.Dataset (LOOConcentration.Observation 1 1) N :=
  Function.update D j ((D j).1, fun _ : Fin 1 => t)

private theorem featureValues_varyResponse {N : ℕ}
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) N)
    (j : Fin N) (t : ℝ) :
    featureValues (varyResponse D j t) = featureValues D := by
  funext i
  by_cases hij : i = j
  · subst i
    simp [featureValues, varyResponse]
  · simp [featureValues, varyResponse, Function.update_of_ne hij]

private theorem clippedResponseValues_varyResponse {N : ℕ}
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) N)
    (j : Fin N) (t b : ℝ) :
    clippedResponseValues (varyResponse D j t) b =
      Function.update (clippedResponseValues D b) j (max (min t b) (-b)) := by
  funext i
  by_cases hij : i = j
  · subst i
    simp [clippedResponseValues, varyResponse]
  · simp [clippedResponseValues, varyResponse, Function.update_of_ne hij]

private noncomputable abbrev ridgeResponseMean {N : ℕ} (U : Fin N → ℝ) : ℝ :=
  (∑ i, U i) * (N : ℝ)⁻¹

private noncomputable abbrev ridgeResponseCovariance {N : ℕ}
    (X U : Fin N → ℝ) : ℝ :=
  (∑ i, (X i - ridgeResponseMean X) * (U i - ridgeResponseMean U)) *
    (N : ℝ)⁻¹

private theorem ridgeResponseCovariance_comm {N : ℕ}
    (X U : Fin N → ℝ) :
    ridgeResponseCovariance X U = ridgeResponseCovariance U X := by
  unfold ridgeResponseCovariance
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

private theorem clippedDatasetCovariance_response_hasDerivAt (r : ℕ)
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1))
    (j : Fin (r + 1)) (b γ : ℝ)
    (hclip : HasDerivAt (fun y : ℝ => max (min y b) (-b)) γ ((D j).2 0)) :
    HasDerivAt
      (fun t : ℝ =>
        ridgeResponseCovariance (featureValues D)
          (clippedResponseValues (varyResponse D j t) b))
      (((featureValues D j -
          ridgeResponseMean (featureValues D)) / ((r + 1 : ℕ) : ℝ)) * γ)
      ((D j).2 0) := by
  have hN : 0 < r + 1 := by omega
  have hEq (t : ℝ) :
      ridgeResponseCovariance (featureValues D)
          (clippedResponseValues (varyResponse D j t) b) =
        ridgeResponseCovariance (Function.update (clippedResponseValues D b) j
          (max (min t b) (-b))) (featureValues D) := by
    rw [clippedResponseValues_varyResponse]
    exact ridgeResponseCovariance_comm _ _
  have hclip' : HasDerivAt (fun y : ℝ => max (min y b) (-b)) γ ((D j).2 0) := hclip
  have hcov' :=
    LOOConcentrationManuscript.Internal.centeredCovariance_update_hasDerivAt
      (N := r + 1) hN (clippedResponseValues D b) (featureValues D) j
  have hcomp := hcov'.comp ((D j).2 0) hclip'
  have hcomp' : HasDerivAt
      (fun t : ℝ =>
        ridgeResponseCovariance (Function.update (clippedResponseValues D b) j
          (max (min t b) (-b))) (featureValues D))
      (((featureValues D j - ridgeResponseMean (featureValues D)) /
          ((r + 1 : ℕ) : ℝ)) * γ) ((D j).2 0) :=
    hcomp.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => by
        simp only [Function.comp_apply, ridgeResponseCovariance, ridgeResponseMean])
  have hfinal : HasDerivAt
      (fun t : ℝ =>
        ridgeResponseCovariance (Function.update (clippedResponseValues D b) j
          (max (min t b) (-b))) (featureValues D))
      (((featureValues D j - ridgeResponseMean (featureValues D)) /
          ((r + 1 : ℕ) : ℝ)) * γ) ((D j).2 0) := by
    simpa [ridgeResponseMean, div_eq_mul_inv, mul_comm, mul_left_comm,
      mul_assoc] using hcomp'
  have hEqFun :
      (fun t : ℝ =>
        ridgeResponseCovariance (featureValues D)
          (clippedResponseValues (varyResponse D j t) b)) =
      (fun t : ℝ =>
        ridgeResponseCovariance (Function.update (clippedResponseValues D b) j
          (max (min t b) (-b))) (featureValues D)) := by
    funext t
    exact hEq t
  rw [hEqFun]
  exact hfinal

/-- Exact response-coordinate derivative of the literal stabilized ridge slope
on a scalar dataset. The hypothesis is precisely differentiability of the
source clipping map at the updated response. -/
theorem clippedDataset_ridgeSlope_response_hasDerivAt (r : ℕ)
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1))
    (j : Fin (r + 1)) (b δ γ : ℝ) (hδ : 0 < δ)
    (hclip : HasDerivAt (fun y : ℝ => max (min y b) (-b)) γ ((D j).2 0)) :
    let N : ℝ := ((r + 1 : ℕ) : ℝ)
    let X := featureValues D
    let a : ℝ := (∑ i : Fin (r + 1), X i) * N⁻¹
    let v : ℝ := (∑ i : Fin (r + 1), (X i - a) ^ 2) * N⁻¹
    HasDerivAt
      (fun t : ℝ =>
        let Dt := varyResponse D j t
        let Xt := featureValues Dt
        let Ut := clippedResponseValues Dt b
        ((∑ i : Fin (r + 1),
          (Xt i - (∑ k : Fin (r + 1), Xt k) * N⁻¹) *
            (Ut i - (∑ k : Fin (r + 1), Ut k) * N⁻¹)) * N⁻¹) /
          (((∑ i : Fin (r + 1),
            (Xt i - (∑ k : Fin (r + 1), Xt k) * N⁻¹) ^ 2) * N⁻¹) + δ))
      (((X j - a) * γ) / (N * (v + δ))) ((D j).2 0) := by
  classical
  let N : ℝ := ((r + 1 : ℕ) : ℝ)
  let X := featureValues D
  let U := clippedResponseValues D b
  let a : ℝ := (∑ i : Fin (r + 1), X i) * N⁻¹
  let c : ℝ := (∑ i : Fin (r + 1), U i) * N⁻¹
  let v : ℝ := (∑ i : Fin (r + 1), (X i - a) ^ 2) * N⁻¹
  let s : ℝ := (∑ i : Fin (r + 1), (X i - a) * (U i - c)) * N⁻¹
  let beta : ℝ := s / (v + δ)
  let C : ℝ → ℝ := fun t =>
    ridgeResponseCovariance X (clippedResponseValues (varyResponse D j t) b)
  let V : ℝ := v
  let B : ℝ → ℝ := fun _ => V + δ
  change HasDerivAt _ (((X j - a) * γ) / (N * (v + δ))) ((D j).2 0)
  have hcurve :
      (fun t : ℝ =>
        (∑ i : Fin (r + 1),
          (featureValues (varyResponse D j t) i -
            (∑ k : Fin (r + 1), featureValues (varyResponse D j t) k) * N⁻¹) *
            (clippedResponseValues (varyResponse D j t) b i -
              (∑ k : Fin (r + 1), clippedResponseValues (varyResponse D j t) b k) * N⁻¹)) * N⁻¹ /
          (((∑ i : Fin (r + 1),
            (featureValues (varyResponse D j t) i -
              (∑ k : Fin (r + 1), featureValues (varyResponse D j t) k) * N⁻¹) ^ 2) * N⁻¹) + δ)) =
      (fun t : ℝ => C t / B t) := by
    funext t
    simp [C, B, V, ridgeResponseCovariance, ridgeResponseMean,
      featureValues_varyResponse, clippedResponseValues_varyResponse,
      N, X, a, v]
  rw [hcurve]
  have hC := clippedDatasetCovariance_response_hasDerivAt r D j b γ hclip
  have hC' : HasDerivAt C (((X j - a) / N) * γ) ((D j).2 0) := by
    simpa [C, X, ridgeResponseMean, N, a, div_eq_mul_inv,
      mul_comm, mul_left_comm, mul_assoc] using hC
  have hN : 0 < N := by dsimp [N]; positivity
  have hv : 0 ≤ v := by
    dsimp [v]
    exact mul_nonneg
      (Finset.sum_nonneg fun i hi => sq_nonneg (X i - a))
      (inv_nonneg.mpr hN.le)
  have hpos : 0 < V + δ := by dsimp [V]; linarith
  have hupdate : varyResponse D j ((D j).2 0) = D := by
    funext i
    by_cases hij : i = j
    · subst i
      change (Function.update D j
        ((D j).1, fun _ : Fin 1 => (D j).2 0)) j = D j
      rw [Function.update_self]
      apply Prod.ext
      · rfl
      · funext k
        fin_cases k
        rfl
    · simp [varyResponse, Function.update_of_ne hij]
  have hC0 : C ((D j).2 0) = s := by
    dsimp [C]
    rw [hupdate]
  have hquotF :=
    LOOConcentration.Manuscript.Internal.positiveDenominator_quotient_hasFDerivAt
      C B _ _ ((D j).2 0) hC'.hasFDerivAt
      (hasDerivAt_const ((D j).2 0) (V + δ)).hasFDerivAt hpos
  have hquot := hquotF.hasDerivAt
  convert hquot using 1
  · simp only [smul_apply, sub_apply, ContinuousLinearMap.toSpanSingleton_apply,
      smul_eq_mul, one_mul]
    rw [hC0]
    simp only [B]
    dsimp [V, beta]
    have hvδ : 0 < v + δ := add_pos_of_nonneg_of_pos hv hδ
    field_simp [hN.ne', hvδ.ne']
    ring

private theorem actualEstimator_prediction_difference_eq_slope (r : ℕ)
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1))
    (b δ : {t : ℝ // 0 < t}) (j : Fin (r + 1)) (t : ℝ) :
    (LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r
        (varyResponse D j t) (fun _ : Fin 1 => 1) 0) -
      (LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r
        (varyResponse D j t) (fun _ : Fin 1 => 0) 0) =
      (let Dt := varyResponse D j t
       let N : ℝ := ((r + 1 : ℕ) : ℝ)
       let X : Fin (r + 1) → ℝ := fun i => (Dt i).1 0
       let U : Fin (r + 1) → ℝ := fun i => max (min ((Dt i).2 0) b.val) (-b.val)
       let a := N⁻¹ * ∑ i : Fin (r + 1), X i
       let c := N⁻¹ * ∑ i : Fin (r + 1), U i
       let v := N⁻¹ * ∑ i : Fin (r + 1), (X i - a) ^ 2
       let s := N⁻¹ * ∑ i : Fin (r + 1), (X i - a) * (U i - c)
       s / (v + δ.val)) := by
  let Dt := varyResponse D j t
  let N : ℝ := ((r + 1 : ℕ) : ℝ)
  let X : Fin (r + 1) → ℝ := fun i => (Dt i).1 0
  let U : Fin (r + 1) → ℝ := fun i => max (min ((Dt i).2 0) b.val) (-b.val)
  let a := N⁻¹ * ∑ i : Fin (r + 1), X i
  let c := N⁻¹ * ∑ i : Fin (r + 1), U i
  let v := N⁻¹ * ∑ i : Fin (r + 1), (X i - a) ^ 2
  let s := N⁻¹ * ∑ i : Fin (r + 1), (X i - a) * (U i - c)
  let beta := s / (v + δ.val)
  simp only [LOOConcentration.Manuscript.stabilizedLinearEstimator,
    ContinuousMap.coe_mk]
  simp only [Nat.cast_add, Nat.cast_one]
  ring

/-- On every actual scalar dataset, the slope of the literal public estimator
is recovered by subtracting its predictions at queries one and zero. -/
theorem stabilizedLinearEstimator_actual_slope_identity (r : ℕ)
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1))
    (b δ : {t : ℝ // 0 < t}) :
    (LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r D
        (fun _ : Fin 1 => 1) 0) -
      (LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r D
        (fun _ : Fin 1 => 0) 0) =
      (let N : ℝ := ((r + 1 : ℕ) : ℝ)
       let X : Fin (r + 1) → ℝ := fun i => (D i).1 0
       let U : Fin (r + 1) → ℝ := fun i => max (min ((D i).2 0) b.val) (-b.val)
       let a := N⁻¹ * ∑ i : Fin (r + 1), X i
       let c := N⁻¹ * ∑ i : Fin (r + 1), U i
       let v := N⁻¹ * ∑ i : Fin (r + 1), (X i - a) ^ 2
       let s := N⁻¹ * ∑ i : Fin (r + 1), (X i - a) * (U i - c)
       s / (v + δ.val)) := by
  have hu : varyResponse D 0 ((D 0).2 0) = D := by
    funext i
    by_cases hi : i = 0
    · subst i
      change (Function.update D 0 ((D 0).1, fun _ : Fin 1 => (D 0).2 0)) 0 = D 0
      rw [Function.update_self]
      apply Prod.ext
      · rfl
      · funext k
        fin_cases k
        rfl
    · simp [varyResponse, Function.update_of_ne hi]
  have hpoint := actualEstimator_prediction_difference_eq_slope r D b δ 0 ((D 0).2 0)
  simpa [hu] using hpoint

/-- The response-coordinate derivative is consumed by the literal public
stabilized estimator: subtracting its predictions at queries one and zero
extracts the slope, whose response-coordinate derivative is the stated value. -/
theorem stabilizedLinearEstimator_actual_responseSlope_hasDerivAt (r : ℕ)
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1))
    (j : Fin (r + 1)) (b δ γ : ℝ) (hb : 0 < b) (hδ : 0 < δ)
    (hclip : HasDerivAt (fun y : ℝ => max (min y b) (-b)) γ ((D j).2 0)) :
    let N : ℝ := ((r + 1 : ℕ) : ℝ)
    let X := featureValues D
    let a : ℝ := (∑ i : Fin (r + 1), X i) * N⁻¹
    let v : ℝ := (∑ i : Fin (r + 1), (X i - a) ^ 2) * N⁻¹
    HasDerivAt
      (fun t : ℝ =>
        (LOOConcentration.Manuscript.stabilizedLinearEstimator ⟨b, hb⟩
          ⟨δ, hδ⟩ r (varyResponse D j t) (fun _ : Fin 1 => 1) 0) -
        (LOOConcentration.Manuscript.stabilizedLinearEstimator ⟨b, hb⟩
          ⟨δ, hδ⟩ r (varyResponse D j t) (fun _ : Fin 1 => 0) 0))
      (((X j - a) * γ) /
        (N * (v + δ))) ((D j).2 0) := by
  classical
  let bb : {t : ℝ // 0 < t} := ⟨b, hb⟩
  let dd : {t : ℝ // 0 < t} := ⟨δ, hδ⟩
  have hSlope := clippedDataset_ridgeSlope_response_hasDerivAt r D j b δ γ hδ hclip
  have hEq :
      (fun t : ℝ =>
        (LOOConcentration.Manuscript.stabilizedLinearEstimator bb dd r
          (varyResponse D j t) (fun _ : Fin 1 => 1) 0) -
        (LOOConcentration.Manuscript.stabilizedLinearEstimator bb dd r
          (varyResponse D j t) (fun _ : Fin 1 => 0) 0)) =
      (fun t : ℝ =>
        let Dt := varyResponse D j t
        let N : ℝ := ((r + 1 : ℕ) : ℝ)
        let Xt : Fin (r + 1) → ℝ := fun i => (Dt i).1 0
        let Ut : Fin (r + 1) → ℝ := fun i => max (min ((Dt i).2 0) b) (-b)
        let meanXt := N⁻¹ * ∑ k : Fin (r + 1), Xt k
        let ct := N⁻¹ * ∑ k : Fin (r + 1), Ut k
        let vt := N⁻¹ * ∑ k : Fin (r + 1), (Xt k - meanXt) ^ 2
        let st := N⁻¹ * ∑ k : Fin (r + 1), (Xt k - meanXt) * (Ut k - ct)
        st /
          (vt + δ)) := by
    funext t
    have hpoint := actualEstimator_prediction_difference_eq_slope r D bb dd j t
    simpa [bb, dd] using hpoint
  rw [hEq]
  have hnorm :
      (fun t : ℝ =>
        let Dt := varyResponse D j t
        let N : ℝ := ((r + 1 : ℕ) : ℝ)
        let Xt : Fin (r + 1) → ℝ := fun i => (Dt i).1 0
        let Ut : Fin (r + 1) → ℝ := fun i => max (min ((Dt i).2 0) b) (-b)
        let meanXt := N⁻¹ * ∑ k : Fin (r + 1), Xt k
        let ct := N⁻¹ * ∑ k : Fin (r + 1), Ut k
        let vt := N⁻¹ * ∑ k : Fin (r + 1), (Xt k - meanXt) ^ 2
        let st := N⁻¹ * ∑ k : Fin (r + 1), (Xt k - meanXt) * (Ut k - ct)
        st / (vt + δ)) =
      (fun t : ℝ =>
        let Dt := varyResponse D j t
        let Xt := featureValues Dt
        let Ut := clippedResponseValues Dt b
        let N : ℝ := ((r + 1 : ℕ) : ℝ)
        ((∑ i : Fin (r + 1),
          (Xt i - (∑ k : Fin (r + 1), Xt k) * N⁻¹) *
            (Ut i - (∑ k : Fin (r + 1), Ut k) * N⁻¹)) * N⁻¹) /
          (((∑ i : Fin (r + 1),
            (Xt i - (∑ k : Fin (r + 1), Xt k) * N⁻¹) ^ 2) * N⁻¹) + δ)) := by
    funext t
    simp [featureValues, clippedResponseValues, mul_comm]
  rw [hnorm]
  simpa using hSlope

end LOOConcentrationManuscript
