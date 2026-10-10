import LOOConcentrationManuscript.Internal.RidgeSlopeResponseDerivative
import LOOConcentrationManuscript.Internal.RidgeSlopeFeatureDerivative
import LOOConcentrationManuscript.Internal.RidgeSlopeBound
import LOOConcentrationRevision.Frozen.Definitions.DatasetOfEuclidean
import LOOConcentration.Geometry.LipschitzCoordinateEnergy
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

/-!
Grouped response and feature gradient bounds for the exact slope extracted
from the public stabilized estimator on the full paired Euclidean carrier.
-/

namespace LOOConcentration.Manuscript.Internal
open scoped RealInnerProductSpace

private noncomputable abbrev ridgeSlopeFormula (b δ : ℝ) (r : ℕ)
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1)) : ℝ :=
  let N : ℝ := ((r + 1 : ℕ) : ℝ)
  let X := LOOConcentrationManuscript.featureValues D
  let U := LOOConcentrationManuscript.clippedResponseValues D b
  let a := N⁻¹ * ∑ i : Fin (r + 1), X i
  let c := N⁻¹ * ∑ i : Fin (r + 1), U i
  let v := N⁻¹ * ∑ i : Fin (r + 1), (X i - a) ^ 2
  let s := N⁻¹ * ∑ i : Fin (r + 1), (X i - a) * (U i - c)
  s / (v + δ)

private noncomputable def ridgeSlopeFormulaEuclidean (b δ : ℝ) (r : ℕ)
    (E : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1))) : ℝ :=
  ridgeSlopeFormula b δ r (LOOConcentration.Revision.datasetOfEuclidean E)

noncomputable def stabilizedLinearEstimator_actualSlope (b δ : {t : ℝ // 0 < t}) (r : ℕ)
    (E : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1))) : ℝ :=
  (LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r
      (LOOConcentration.Revision.datasetOfEuclidean E) (fun _ : Fin 1 => 1) 0) -
    (LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r
      (LOOConcentration.Revision.datasetOfEuclidean E) (fun _ : Fin 1 => 0) 0)

private theorem stabilizedLinearEstimator_actualSlope_eq_formula (b δ : {t : ℝ // 0 < t}) (r : ℕ)
    (E : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1))) :
    stabilizedLinearEstimator_actualSlope b δ r E =
      ridgeSlopeFormula b.val δ.val r (LOOConcentration.Revision.datasetOfEuclidean E) := by
  exact LOOConcentrationManuscript.stabilizedLinearEstimator_actual_slope_identity
    r (LOOConcentration.Revision.datasetOfEuclidean E) b δ

private theorem ridge_actual_slope_gradient_coordinate_eq_update_section
    (b δ : {t : ℝ // 0 < t}) (r : ℕ)
    (E : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1)))
    (p : Fin (r + 1) × (Fin 1 ⊕ Fin 1))
    (hdiff : DifferentiableAt ℝ (stabilizedLinearEstimator_actualSlope b δ r) E) :
    gradient (stabilizedLinearEstimator_actualSlope b δ r) E p =
      deriv (fun t : ℝ =>
        stabilizedLinearEstimator_actualSlope b δ r
          (WithLp.toLp 2 (Function.update (fun q => E q) p t))) (E p) := by
  have hPath (t : ℝ) :
      LOOConcentration.euclideanCoordinatePath E p t =
        WithLp.toLp 2 (Function.update (fun q => E q) p t) := by
    ext q
    by_cases hqp : q = p
    · subst q
      simp [LOOConcentration.euclideanCoordinatePath]
    · simp [LOOConcentration.euclideanCoordinatePath, hqp]
  have hSection :
      LOOConcentration.euclideanCoordinateSection (stabilizedLinearEstimator_actualSlope b δ r) E p =
        fun t : ℝ => stabilizedLinearEstimator_actualSlope b δ r
          (WithLp.toLp 2 (Function.update (fun q => E q) p t)) := by
    funext t
    exact congrArg (stabilizedLinearEstimator_actualSlope b δ r) (hPath t)
  have hDeriv := LOOConcentration.deriv_euclideanCoordinateSection_eq_fderiv
    (stabilizedLinearEstimator_actualSlope b δ r) E p hdiff
  rw [hSection] at hDeriv
  have hDual :
      fderiv ℝ (stabilizedLinearEstimator_actualSlope b δ r) E (EuclideanSpace.single p (1 : ℝ)) =
        gradient (stabilizedLinearEstimator_actualSlope b δ r) E p := by
    rw [← toDual_gradient]
    rw [InnerProductSpace.toDual_apply_apply, EuclideanSpace.inner_single_right]
    simp
  have hDeriv' :
      deriv (fun t : ℝ => stabilizedLinearEstimator_actualSlope b δ r
          (WithLp.toLp 2 (Function.update (fun q => E q) p t))) (E p) =
        fderiv ℝ (stabilizedLinearEstimator_actualSlope b δ r) E (EuclideanSpace.single p (1 : ℝ)) := by
    convert hDeriv using 1
    apply congrArg (fderiv ℝ (stabilizedLinearEstimator_actualSlope b δ r) E)
    ext q
    simp
  exact (hDeriv'.trans hDual).symm

private theorem datasetOfEuclidean_responseUpdate (r : ℕ)
    (E : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1)))
    (j : Fin (r + 1)) (t : ℝ) :
    LOOConcentration.Revision.datasetOfEuclidean
        (WithLp.toLp 2 (Function.update (fun q => E q) (j, Sum.inr 0) t)) =
      LOOConcentrationManuscript.varyResponse
        (LOOConcentration.Revision.datasetOfEuclidean E) j t := by
  funext i
  by_cases hij : i = j
  · subst i
    apply Prod.ext
    · funext k
      fin_cases k
      simp [LOOConcentration.Revision.datasetOfEuclidean,
        LOOConcentrationManuscript.varyResponse, Function.update]
    · funext k
      fin_cases k
      simp [LOOConcentration.Revision.datasetOfEuclidean,
        LOOConcentrationManuscript.varyResponse, Function.update]
  · apply Prod.ext
    · funext k
      fin_cases k
      simp [LOOConcentration.Revision.datasetOfEuclidean,
        LOOConcentrationManuscript.varyResponse, Function.update, hij]
    · funext k
      fin_cases k
      simp [LOOConcentration.Revision.datasetOfEuclidean,
        LOOConcentrationManuscript.varyResponse, Function.update, hij]

private theorem datasetOfEuclidean_featureUpdate (r : ℕ)
    (E : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1)))
    (j : Fin (r + 1)) (t : ℝ) :
    LOOConcentration.Revision.datasetOfEuclidean
        (WithLp.toLp 2 (Function.update (fun q => E q) (j, Sum.inl 0) t)) =
      LOOConcentrationManuscript.varyFeature
        (LOOConcentration.Revision.datasetOfEuclidean E) j t := by
  funext i
  by_cases hij : i = j
  · subst i
    apply Prod.ext
    · funext k
      fin_cases k
      simp [LOOConcentration.Revision.datasetOfEuclidean,
        LOOConcentrationManuscript.varyFeature, Function.update]
    · funext k
      fin_cases k
      simp [LOOConcentration.Revision.datasetOfEuclidean,
        LOOConcentrationManuscript.varyFeature, Function.update]
  · apply Prod.ext
    · funext k
      fin_cases k
      simp [LOOConcentration.Revision.datasetOfEuclidean,
        LOOConcentrationManuscript.varyFeature, Function.update, hij]
    · funext k
      fin_cases k
      simp [LOOConcentration.Revision.datasetOfEuclidean,
        LOOConcentrationManuscript.varyFeature, Function.update, hij]

/-- The response-coordinate formula is the corresponding coordinate of the
Fréchet gradient of the actual public-estimator slope whenever that slope is
Fréchet differentiable. -/
theorem stabilizedLinearEstimator_actual_response_gradient_coordinate
    (r : ℕ) (b δ : {t : ℝ // 0 < t})
    (E : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1)))
    (j : Fin (r + 1)) (γ : ℝ)
    (hdiff : DifferentiableAt ℝ (stabilizedLinearEstimator_actualSlope b δ r) E)
    (hclip : HasDerivAt
      (fun y : ℝ => max (min y b.val) (-b.val)) γ
      ((LOOConcentration.Revision.datasetOfEuclidean E j).2 0)) :
    let D := LOOConcentration.Revision.datasetOfEuclidean E
    let N : ℝ := ((r + 1 : ℕ) : ℝ)
    let X := LOOConcentrationManuscript.featureValues D
    let a : ℝ := (∑ i : Fin (r + 1), X i) * N⁻¹
    let v : ℝ := (∑ i : Fin (r + 1), (X i - a) ^ 2) * N⁻¹
    gradient (stabilizedLinearEstimator_actualSlope b δ r) E (j, Sum.inr 0) =
      ((X j - a) * γ) / (N * (v + δ.val)) := by
  classical
  let D := LOOConcentration.Revision.datasetOfEuclidean E
  have hcoord := ridge_actual_slope_gradient_coordinate_eq_update_section
    b δ r E (j, Sum.inr 0) hdiff
  rw [hcoord]
  have hsection :
      (fun t : ℝ => stabilizedLinearEstimator_actualSlope b δ r
        (WithLp.toLp 2 (Function.update (fun q => E q) (j, Sum.inr 0) t))) =
      (fun t : ℝ =>
        (LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r
          (LOOConcentrationManuscript.varyResponse D j t) (fun _ : Fin 1 => 1) 0) -
        (LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r
          (LOOConcentrationManuscript.varyResponse D j t) (fun _ : Fin 1 => 0) 0)) := by
    funext t
    simp only [stabilizedLinearEstimator_actualSlope]
    rw [datasetOfEuclidean_responseUpdate]
  rw [hsection]
  have hresp := LOOConcentrationManuscript.stabilizedLinearEstimator_actual_responseSlope_hasDerivAt
    r D j b.val δ.val γ b.property δ.property hclip
  have hbase : E (j, Sum.inr 0) = (D j).2 0 := rfl
  rw [hbase]
  simpa [D, div_eq_mul_inv, mul_comm] using hresp.deriv

/-- The feature-coordinate formula is the corresponding coordinate of the
Fréchet gradient of the actual public-estimator slope. -/
theorem stabilizedLinearEstimator_actual_feature_gradient_coordinate
    (r : ℕ) (b δ : {t : ℝ // 0 < t})
    (E : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1)))
    (j : Fin (r + 1))
    (hdiff : DifferentiableAt ℝ (stabilizedLinearEstimator_actualSlope b δ r) E) :
    let D := LOOConcentration.Revision.datasetOfEuclidean E
    let N : ℝ := ((r + 1 : ℕ) : ℝ)
    let X := LOOConcentrationManuscript.featureValues D
    let U := LOOConcentrationManuscript.clippedResponseValues D b.val
    let a : ℝ := (∑ i : Fin (r + 1), X i) * N⁻¹
    let c : ℝ := (∑ i : Fin (r + 1), U i) * N⁻¹
    let v : ℝ := (∑ i : Fin (r + 1), (X i - a) ^ 2) * N⁻¹
    let s : ℝ := (∑ i : Fin (r + 1), (X i - a) * (U i - c)) * N⁻¹
    let β : ℝ := s / (v + δ.val)
    gradient (stabilizedLinearEstimator_actualSlope b δ r) E (j, Sum.inl 0) =
      (U j - c - 2 * β * (X j - a)) / (N * (v + δ.val)) := by
  classical
  let D := LOOConcentration.Revision.datasetOfEuclidean E
  have hcoord := ridge_actual_slope_gradient_coordinate_eq_update_section
    b δ r E (j, Sum.inl 0) hdiff
  rw [hcoord]
  have hsection :
      (fun t : ℝ => stabilizedLinearEstimator_actualSlope b δ r
        (WithLp.toLp 2 (Function.update (fun q => E q) (j, Sum.inl 0) t))) =
      (fun t : ℝ =>
        let Dt := LOOConcentrationManuscript.varyFeature D j t
        let Xt := LOOConcentrationManuscript.featureValues Dt
        let Ut := LOOConcentrationManuscript.clippedResponseValues Dt b.val
        let N : ℝ := ((r + 1 : ℕ) : ℝ)
        ((∑ i : Fin (r + 1),
          (Xt i - (∑ k : Fin (r + 1), Xt k) * N⁻¹) *
            (Ut i - (∑ k : Fin (r + 1), Ut k) * N⁻¹)) * N⁻¹) /
          (((∑ i : Fin (r + 1),
            (Xt i - (∑ k : Fin (r + 1), Xt k) * N⁻¹) ^ 2) * N⁻¹) + δ.val)) := by
    funext t
    have hpoint := LOOConcentrationManuscript.stabilizedLinearEstimator_actual_slope_identity
      r (LOOConcentrationManuscript.varyFeature D j t) b δ
    simp only [stabilizedLinearEstimator_actualSlope]
    rw [datasetOfEuclidean_featureUpdate]
    simpa [LOOConcentrationManuscript.featureValues,
      LOOConcentrationManuscript.clippedResponseValues, mul_comm] using hpoint
  rw [hsection]
  have hfeature := clippedDataset_ridgeSlope_feature_hasDerivAt
    r D j b.val δ.val δ.property
  have hbase : E (j, Sum.inl 0) = LOOConcentrationManuscript.featureValues D j := rfl
  change _ = _
  rw [hbase]
  simpa [D] using hfeature.deriv

/-- Finite dimensional block bounds for the exact coordinate derivatives of
the normalized ridge slope. The energy hypotheses are the centered feature
variance identity and the clipped-response energy bound. -/
theorem ridgeSlope_coordinateBlock_norm_bounds
    (N : ℕ) (hN : 0 < N) (b δ v β : ℝ)
    (hb : 0 ≤ b) (hδ : 0 < δ) (hv : 0 ≤ v)
    (x u γ : Fin N → ℝ)
    (hx : (∑ i : Fin N, x i ^ 2) = (N : ℝ) * v)
    (hu : (∑ i : Fin N, u i ^ 2) ≤ (N : ℝ) * b ^ 2)
    (hγ : ∀ i, |γ i| ≤ 1) :
    ‖WithLp.toLp 2 (fun i : Fin N =>
        x i * γ i / ((N : ℝ) * (v + δ)))‖ ≤
      Real.sqrt v / (Real.sqrt (N : ℝ) * (v + δ)) ∧
    ‖WithLp.toLp 2 (fun i : Fin N =>
        (u i - 2 * β * x i) / ((N : ℝ) * (v + δ)))‖ ≤
      (b + 2 * |β| * Real.sqrt v) /
        (Real.sqrt (N : ℝ) * (v + δ)) := by
  classical
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hsqrtN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNr
  have hsqrtV : 0 ≤ Real.sqrt v := Real.sqrt_nonneg v
  have hsqrtNV : Real.sqrt ((N : ℝ) * v) =
      Real.sqrt (N : ℝ) * Real.sqrt v := by
    rw [Real.sqrt_mul hNr.le]
  have hden : 0 < (N : ℝ) * (v + δ) :=
    mul_pos hNr (add_pos_of_nonneg_of_pos hv hδ)
  have hxNormSq : ‖WithLp.toLp 2 x‖ ^ 2 = (N : ℝ) * v := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact hx
  have hxNorm : ‖WithLp.toLp 2 x‖ =
      Real.sqrt (N : ℝ) * Real.sqrt v := by
    rw [← hsqrtNV]
    apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).1
    rw [Real.sq_sqrt (mul_nonneg hNr.le hv)]
    exact hxNormSq
  have huNorm : ‖WithLp.toLp 2 u‖ ≤ b * Real.sqrt (N : ℝ) := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hb (Real.sqrt_nonneg _))).1
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      (∑ i : Fin N, u i ^ 2) ≤ (N : ℝ) * b ^ 2 := hu
      _ = (b * Real.sqrt (N : ℝ)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hNr.le]
        ring
  let w : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 (fun i => x i * γ i)
  have hγsq : ∀ i : Fin N, γ i ^ 2 ≤ 1 := by
    intro i
    rw [← sq_abs (γ i)]
    simpa using (sq_le_sq₀ (abs_nonneg _) (by norm_num)).2 (hγ i)
  have hwSq : (∑ i : Fin N, (x i * γ i) ^ 2) ≤ (N : ℝ) * v := by
    calc
      _ ≤ ∑ i : Fin N, x i ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        have hm := mul_le_mul_of_nonneg_left (hγsq i) (sq_nonneg (x i))
        nlinarith [hm]
      _ = _ := hx
  have hwNorm : ‖w‖ ≤ Real.sqrt (N : ℝ) * Real.sqrt v := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _))).1
    calc
      ‖w‖ ^ 2 = ∑ i : Fin N, (x i * γ i) ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
      _ ≤ (N : ℝ) * v := hwSq
      _ = (Real.sqrt (N : ℝ) * Real.sqrt v) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hNr.le, Real.sq_sqrt hv]
  let z : EuclideanSpace ℝ (Fin N) :=
    WithLp.toLp 2 (fun i => u i - 2 * β * x i)
  have hzEq : z = WithLp.toLp 2 u - (2 * β) • WithLp.toLp 2 x := by
    ext i
    simp [z, two_mul]
  have hzNorm : ‖z‖ ≤ b * Real.sqrt (N : ℝ) +
      2 * |β| * (Real.sqrt (N : ℝ) * Real.sqrt v) := by
    rw [hzEq]
    calc
      ‖WithLp.toLp 2 u - (2 * β) • WithLp.toLp 2 x‖ ≤
          ‖WithLp.toLp 2 u‖ + ‖(2 * β) • WithLp.toLp 2 x‖ := norm_sub_le _ _
      _ = ‖WithLp.toLp 2 u‖ + |2 * β| * ‖WithLp.toLp 2 x‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ ≤ b * Real.sqrt (N : ℝ) +
          2 * |β| * (Real.sqrt (N : ℝ) * Real.sqrt v) := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        exact add_le_add huNorm (mul_le_mul_of_nonneg_left (le_of_eq hxNorm)
          (mul_nonneg (by norm_num) (abs_nonneg β)))
  have hrespEq : WithLp.toLp 2 (fun i : Fin N =>
      x i * γ i / ((N : ℝ) * (v + δ))) =
        ((N : ℝ) * (v + δ))⁻¹ • w := by
    ext i
    simp [w, div_eq_mul_inv, mul_comm, mul_assoc]
  have hfeatEq : WithLp.toLp 2 (fun i : Fin N =>
      (u i - 2 * β * x i) / ((N : ℝ) * (v + δ))) =
        ((N : ℝ) * (v + δ))⁻¹ • z := by
    ext i
    simp [z, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  constructor
  · rw [hrespEq, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 hden)]
    calc
      ((N : ℝ) * (v + δ))⁻¹ * ‖w‖ ≤
          ((N : ℝ) * (v + δ))⁻¹ *
            (Real.sqrt (N : ℝ) * Real.sqrt v) :=
        mul_le_mul_of_nonneg_left hwNorm (inv_nonneg.2 hden.le)
      _ = Real.sqrt v / (Real.sqrt (N : ℝ) * (v + δ)) := by
        field_simp [ne_of_gt hsqrtN, ne_of_gt hden]
        rw [Real.sq_sqrt hNr.le]

  · rw [hfeatEq, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 hden)]
    calc
      ((N : ℝ) * (v + δ))⁻¹ * ‖z‖ ≤
          ((N : ℝ) * (v + δ))⁻¹ *
            (b * Real.sqrt (N : ℝ) +
              2 * |β| * (Real.sqrt (N : ℝ) * Real.sqrt v)) :=
        mul_le_mul_of_nonneg_left hzNorm (inv_nonneg.2 hden.le)
      _ = (b + 2 * |β| * Real.sqrt v) /
            (Real.sqrt (N : ℝ) * (v + δ)) := by
        field_simp [ne_of_gt hsqrtN, ne_of_gt hden]
        rw [Real.sq_sqrt hNr.le]

private theorem stabilizedLinearEstimator_actualSlope_differentiableAt_of_clipDerivatives
    (r : ℕ) (b δ : {t : ℝ // 0 < t})
    (E : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1)))
    (hclips : ∀ j : Fin (r + 1), ∃ γ : ℝ,
      HasDerivAt (fun y : ℝ => max (min y b.val) (-b.val)) γ
        ((LOOConcentration.Revision.datasetOfEuclidean E j).2 0)) :
    DifferentiableAt ℝ (stabilizedLinearEstimator_actualSlope b δ r) E := by
  classical
  let N : ℝ := ((r + 1 : ℕ) : ℝ)
  let Xfun : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1)) →
      Fin (r + 1) → ℝ := fun E =>
        LOOConcentrationManuscript.featureValues
          (LOOConcentration.Revision.datasetOfEuclidean E)
  let Ufun : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1)) →
      Fin (r + 1) → ℝ := fun E =>
        LOOConcentrationManuscript.clippedResponseValues
          (LOOConcentration.Revision.datasetOfEuclidean E) b.val
  have hX : DifferentiableAt ℝ Xfun E := by
    rw [differentiableAt_pi]
    intro j
    have hp : DifferentiableAt ℝ (fun E => E (j, Sum.inl 0)) E := by fun_prop
    simpa [Xfun, LOOConcentrationManuscript.featureValues,
      LOOConcentration.Revision.datasetOfEuclidean] using hp
  have hU : DifferentiableAt ℝ Ufun E := by
    rw [differentiableAt_pi]
    intro j
    have hp : DifferentiableAt ℝ (fun E => E (j, Sum.inr 0)) E := by fun_prop
    have hscalar := (Classical.choose_spec (hclips j)).differentiableAt
    have hcomp := hscalar.comp E hp
    exact hcomp
  let afun : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1)) → ℝ :=
    fun E => N⁻¹ * ∑ i, Xfun E i
  let cfun : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1)) → ℝ :=
    fun E => N⁻¹ * ∑ i, Ufun E i
  let vfun : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1)) → ℝ :=
    fun E => N⁻¹ * ∑ i, (Xfun E i - afun E) ^ 2
  let sfun : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1)) → ℝ :=
    fun E => N⁻¹ * ∑ i, (Xfun E i - afun E) * (Ufun E i - cfun E)
  have ha : DifferentiableAt ℝ afun E := by dsimp [afun]; fun_prop
  have hc : DifferentiableAt ℝ cfun E := by dsimp [cfun]; fun_prop
  have hv : DifferentiableAt ℝ vfun E := by dsimp [vfun]; fun_prop
  have hs : DifferentiableAt ℝ sfun E := by dsimp [sfun]; fun_prop
  have hden : DifferentiableAt ℝ (fun E => vfun E + δ.val) E :=
    hv.add_const δ.val
  have hNr : 0 < N := by dsimp [N]; positivity
  have hdenpos : 0 < vfun E + δ.val := by
    have hV : 0 ≤ vfun E := by
      dsimp [vfun]
      exact mul_nonneg (inv_nonneg.mpr hNr.le)
        (Finset.sum_nonneg fun i hi => sq_nonneg _)
    exact add_pos_of_nonneg_of_pos hV δ.property
  have hquot : DifferentiableAt ℝ
      (fun E' => sfun E' / (vfun E' + δ.val)) E := by
    change DifferentiableAt ℝ
      (fun E' => sfun E' * (vfun E' + δ.val)⁻¹) E
    exact hs.mul (hden.inv hdenpos.ne')
  have hform : DifferentiableAt ℝ
      (fun E =>
        let X := Xfun E
        let U := Ufun E
        let a := afun E
        let c := cfun E
        let v := vfun E
        let s := sfun E
        s / (v + δ.val)) E := by
    simpa only [Function.comp_apply, afun, cfun, vfun, sfun] using hquot
  have hEq :
      (fun E => stabilizedLinearEstimator_actualSlope b δ r E) =
        (fun E => ridgeSlopeFormulaEuclidean b.val δ.val r E) := by
    funext E'
    exact stabilizedLinearEstimator_actualSlope_eq_formula b δ r E'
  change DifferentiableAt ℝ (fun E' => stabilizedLinearEstimator_actualSlope b δ r E') E
  rw [hEq]
  simpa [ridgeSlopeFormulaEuclidean, ridgeSlopeFormula, Xfun, Ufun,
    LOOConcentrationManuscript.featureValues,
    LOOConcentrationManuscript.clippedResponseValues, N, afun, cfun, vfun, sfun]
    using hform

/-- The grouped coordinate bounds for the actual slope extracted from the
public estimator. At points where the response clipping coordinates have
derivatives, the block vectors are exactly the source response and feature
coordinate derivatives. -/
theorem stabilizedLinearEstimator_actual_grouped_gradient_bounds
    (r : ℕ) (b δ : {t : ℝ // 0 < t})
    (E : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1)))
    (hclips : ∀ j : Fin (r + 1), ∃ γ : ℝ,
      HasDerivAt (fun y : ℝ => max (min y b.val) (-b.val)) γ
        ((LOOConcentration.Revision.datasetOfEuclidean E j).2 0)) :
    let D := LOOConcentration.Revision.datasetOfEuclidean E
    let N : ℝ := ((r + 1 : ℕ) : ℝ)
    let X := LOOConcentrationManuscript.featureValues D
    let U := LOOConcentrationManuscript.clippedResponseValues D b.val
    let a : ℝ := (∑ i : Fin (r + 1), X i) * N⁻¹
    let c : ℝ := (∑ i : Fin (r + 1), U i) * N⁻¹
    let v : ℝ := (∑ i : Fin (r + 1), (X i - a) ^ 2) * N⁻¹
    let s : ℝ := (∑ i : Fin (r + 1), (X i - a) * (U i - c)) * N⁻¹
    let β : ℝ := s / (v + δ.val)
    ‖WithLp.toLp 2 (fun j : Fin (r + 1) =>
        gradient (stabilizedLinearEstimator_actualSlope b δ r) E (j, Sum.inr 0))‖ ≤
      Real.sqrt v / (Real.sqrt N * (v + δ.val)) ∧
    ‖WithLp.toLp 2 (fun j : Fin (r + 1) =>
        gradient (stabilizedLinearEstimator_actualSlope b δ r) E (j, Sum.inl 0))‖ ≤
      (b.val + 2 * |β| * Real.sqrt v) /
        (Real.sqrt N * (v + δ.val)) := by
  classical
  let D := LOOConcentration.Revision.datasetOfEuclidean E
  let N : ℝ := ((r + 1 : ℕ) : ℝ)
  let X := LOOConcentrationManuscript.featureValues D
  let U := LOOConcentrationManuscript.clippedResponseValues D b.val
  let a : ℝ := (∑ i : Fin (r + 1), X i) * N⁻¹
  let c : ℝ := (∑ i : Fin (r + 1), U i) * N⁻¹
  let v : ℝ := (∑ i : Fin (r + 1), (X i - a) ^ 2) * N⁻¹
  let s : ℝ := (∑ i : Fin (r + 1), (X i - a) * (U i - c)) * N⁻¹
  let β : ℝ := s / (v + δ.val)
  have hdiff := stabilizedLinearEstimator_actualSlope_differentiableAt_of_clipDerivatives r b δ E hclips
  let γ : Fin (r + 1) → ℝ := fun j => Classical.choose (hclips j)
  have hclip j : HasDerivAt (fun y : ℝ => max (min y b.val) (-b.val))
      (γ j) ((D j).2 0) := by
    exact Classical.choose_spec (hclips j)
  have hgamma : ∀ j, |γ j| ≤ 1 := by
    intro j
    have hLip := scalarClipping_lipschitz_and_bound b.val (le_of_lt b.property)
    have hnorm := (hclip j).le_of_lipschitz hLip.1
    simpa [Real.norm_eq_abs] using hnorm
  let x : Fin (r + 1) → ℝ := fun j => X j - a
  let u : Fin (r + 1) → ℝ := fun j => U j - c
  have hN : 0 < r + 1 := by omega
  have hNr : 0 < (r + 1 : ℝ) := by exact_mod_cast hN
  have hv : 0 ≤ v := by
    dsimp [v]
    positivity
  have hx : (∑ j : Fin (r + 1), x j ^ 2) = (r + 1 : ℝ) * v := by
    dsimp [x, v, N]
    field_simp [ne_of_gt hNr]
    rw [Nat.cast_add, Nat.cast_one]
  have hsumU : (∑ j : Fin (r + 1), U j) = (r + 1 : ℝ) * c := by
    dsimp [c, N]
    field_simp [ne_of_gt hNr]
    rw [Nat.cast_add, Nat.cast_one]
  have hcross : (∑ j : Fin (r + 1), 2 * U j * c) =
      2 * c * (∑ j : Fin (r + 1), U j) := by
    calc
      _ = ∑ j : Fin (r + 1), (2 * c) * U j := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by rw [Finset.mul_sum]
  have hcenterU :
      (∑ j : Fin (r + 1), u j ^ 2) =
        (∑ j : Fin (r + 1), U j ^ 2) - (r + 1 : ℝ) * c ^ 2 := by
    dsimp [u]
    calc
      _ = ∑ j : Fin (r + 1),
          (U j ^ 2 - 2 * U j * c + c ^ 2) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = (∑ j : Fin (r + 1), U j ^ 2) -
          2 * c * (∑ j : Fin (r + 1), U j) + (r + 1 : ℝ) * c ^ 2 := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul]
            rw [hcross]
            rw [Nat.cast_add, Nat.cast_one]
      _ = _ := by rw [hsumU]; ring
  have hu : (∑ j : Fin (r + 1), u j ^ 2) ≤
      (r + 1 : ℝ) * b.val ^ 2 := by
    have hU2 : (∑ j : Fin (r + 1), U j ^ 2) ≤
        (r + 1 : ℝ) * b.val ^ 2 := by
      calc
        _ ≤ ∑ _j : Fin (r + 1), b.val ^ 2 := by
          apply Finset.sum_le_sum
          intro j hj
          have hbound := (scalarClipping_lipschitz_and_bound b.val
            (le_of_lt b.property)).2 ((D j).2 0)
          have hsquare := (sq_le_sq₀ (abs_nonneg (U j)) (le_of_lt b.property)).2 hbound
          simpa [U, sq_abs] using hsquare
        _ = _ := by simp
    rw [hcenterU]
    nlinarith [sq_nonneg c]
  have hbeta : β = s / (v + δ.val) := rfl
  have hx' : (∑ j : Fin (r + 1), x j ^ 2) = ((r + 1 : ℕ) : ℝ) * v := by
    simpa [Nat.cast_add, Nat.cast_one] using hx
  have hu' : (∑ j : Fin (r + 1), u j ^ 2) ≤
      ((r + 1 : ℕ) : ℝ) * b.val ^ 2 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hu
  have hrespVec : WithLp.toLp 2 (fun j : Fin (r + 1) =>
      gradient (stabilizedLinearEstimator_actualSlope b δ r) E (j, Sum.inr 0)) =
      WithLp.toLp 2 (fun j : Fin (r + 1) =>
        x j * γ j / ((r + 1 : ℝ) * (v + δ.val))) := by
    ext j
    have hcoord := stabilizedLinearEstimator_actual_response_gradient_coordinate
      r b δ E j (γ j) hdiff (hclip j)
    simpa [D, N, X, a, v, x] using hcoord
  have hfeatVec : WithLp.toLp 2 (fun j : Fin (r + 1) =>
      gradient (stabilizedLinearEstimator_actualSlope b δ r) E (j, Sum.inl 0)) =
      WithLp.toLp 2 (fun j : Fin (r + 1) =>
        (u j - 2 * β * x j) / ((r + 1 : ℝ) * (v + δ.val))) := by
    ext j
    have hcoord := stabilizedLinearEstimator_actual_feature_gradient_coordinate
      r b δ E j hdiff
    simpa [D, N, X, U, a, c, v, s, β, x, u] using hcoord
  have hblocks := ridgeSlope_coordinateBlock_norm_bounds (r + 1) (by omega)
    b.val δ.val v β (le_of_lt b.property) δ.property hv x u γ hx' hu' hgamma
  constructor
  · rw [hrespVec]
    simpa [Nat.cast_add, Nat.cast_one, N, D, X, a, v,
      LOOConcentrationManuscript.featureValues] using hblocks.1
  · rw [hfeatVec]
    simpa [Nat.cast_add, Nat.cast_one, N, D, X, U, a, c, v, s, β, x, u,
      LOOConcentrationManuscript.featureValues,
      LOOConcentrationManuscript.clippedResponseValues] using hblocks.2

end LOOConcentration.Manuscript.Internal
