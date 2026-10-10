import LOOConcentrationManuscript.Internal.RidgePredictorTrainingRegularityConsumer
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal
open scoped ContDiff

/-- The three literal branches of response clipping. -/
def ridgeResponsePieceValue (b : ℝ) (mode : Fin 3) (y : ℝ) : ℝ :=
  if mode = 0 then -b else if mode = 1 then y else b

/-- Closed response chambers, with clipping endpoints shared by adjacent pieces. -/
def ridgeResponseChamber (b : ℝ) (r : ℕ) (mode : Fin (r + 1) → Fin 3) :
    Set (EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1))) :=
  {E | ∀ j, if mode j = 0 then E (j, Sum.inr 0) ≤ -b
    else if mode j = 1 then -b ≤ E (j, Sum.inr 0) ∧ E (j, Sum.inr 0) ≤ b
    else b ≤ E (j, Sum.inr 0)}

/-- A smooth Ridge branch keeps the raw-response intercept and replaces only
covariance clipping by its selected affine branch. -/
noncomputable def ridgePredictorSmoothPiece (b δ : {t : ℝ // 0 < t}) (r : ℕ)
    (x : ℝ) (mode : Fin (r + 1) → Fin 3)
    (E : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1))) : ℝ :=
  let a : ℝ := (r + 1 : ℝ)⁻¹ * ∑ j : Fin (r + 1), E (j, Sum.inl 0)
  let U := fun j : Fin (r + 1) => ridgeResponsePieceValue b.val (mode j) (E (j, Sum.inr 0))
  let c : ℝ := (r + 1 : ℝ)⁻¹ * ∑ j : Fin (r + 1), U j
  let v : ℝ := (r + 1 : ℝ)⁻¹ * ∑ j : Fin (r + 1), (E (j, Sum.inl 0) - a) ^ 2
  let s : ℝ := (r + 1 : ℝ)⁻¹ * ∑ j : Fin (r + 1), (E (j, Sum.inl 0) - a) * (U j - c)
  ((r + 1 : ℝ)⁻¹ * ∑ j : Fin (r + 1), E (j, Sum.inr 0)) + s / (v + δ.val) * (x - a)

private theorem ridgeResponsePieceValue_eq_clip (b : {t : ℝ // 0 < t})
    (mode : Fin 3) (y : ℝ)
    (h : if mode = 0 then y ≤ -b.val
      else if mode = 1 then -b.val ≤ y ∧ y ≤ b.val else b.val ≤ y) :
    ridgeResponsePieceValue b.val mode y = max (min y b.val) (-b.val) := by
  have hb : -b.val ≤ b.val := by linarith [b.property]
  unfold ridgeResponsePieceValue
  split_ifs with h0 h1
  · rw [if_pos h0] at h
    rw [min_eq_left (h.trans hb), max_eq_right h]
  · rw [if_neg h0, if_pos h1] at h
    rw [min_eq_left h.2, max_eq_left h.1]
  · rw [if_neg h0, if_neg h1] at h
    rw [min_eq_right h, max_eq_left hb]

/-- Every dataset belongs to one of the finite response chambers. -/
theorem ridgeResponseChambers_cover (b : ℝ) (r : ℕ)
    (E : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1))) :
    ∃ mode : Fin (r + 1) → Fin 3, E ∈ ridgeResponseChamber b r mode := by
  classical
  let mode := fun j : Fin (r + 1) =>
    if E (j, Sum.inr 0) ≤ -b then (0 : Fin 3)
    else if E (j, Sum.inr 0) ≤ b then (1 : Fin 3) else (2 : Fin 3)
  refine ⟨mode, ?_⟩
  intro j
  by_cases h0 : E (j, Sum.inr 0) ≤ -b
  · simp [mode, h0]
  · by_cases h1 : E (j, Sum.inr 0) ≤ b
    · simpa [mode, h0, h1] using And.intro (not_le.mp h0).le h1
    · simpa [mode, h0, h1] using (not_le.mp h1).le

/-- Each response chamber is closed in the full paired Euclidean carrier. -/
theorem ridgeResponseChamber_isClosed (b : ℝ) (r : ℕ) (mode : Fin (r + 1) → Fin 3) :
    IsClosed (ridgeResponseChamber b r mode) := by
  unfold ridgeResponseChamber
  rw [Set.ofPred_forall]
  apply isClosed_iInter
  intro j
  have hcoord : Continuous (fun E : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1)) =>
    E (j, Sum.inr 0)) := by fun_prop
  split_ifs
  · exact isClosed_le hcoord continuous_const
  · exact (isClosed_le (f := fun _ => -b) continuous_const hcoord).inter
      (isClosed_le hcoord (g := fun _ => b) continuous_const)
  · exact isClosed_le continuous_const hcoord

private theorem ridgePredictorSmoothPiece_contDiff (b δ : {t : ℝ // 0 < t})
    (r : ℕ) (x : ℝ) (mode : Fin (r + 1) → Fin 3) :
    ContDiff ℝ ∞ (ridgePredictorSmoothPiece b δ r x mode) := by
  classical
  let a := fun E : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1)) =>
    (r + 1 : ℝ)⁻¹ * ∑ j : Fin (r + 1), E (j, Sum.inl 0)
  let U := fun j : Fin (r + 1) =>
    fun E : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1)) =>
      ridgeResponsePieceValue b.val (mode j) (E (j, Sum.inr 0))
  let c := fun E => (r + 1 : ℝ)⁻¹ * ∑ j : Fin (r + 1), U j E
  let v := fun E => (r + 1 : ℝ)⁻¹ * ∑ j : Fin (r + 1), (E (j, Sum.inl 0) - a E) ^ 2
  let s := fun E => (r + 1 : ℝ)⁻¹ * ∑ j : Fin (r + 1),
    (E (j, Sum.inl 0) - a E) * (U j E - c E)
  have ha : ContDiff ℝ ∞ a := by dsimp [a]; fun_prop
  have hU : ∀ j, ContDiff ℝ ∞ (U j) := by
    intro j
    dsimp [U, ridgeResponsePieceValue]
    split_ifs <;> fun_prop
  have hc : ContDiff ℝ ∞ c := by
    dsimp [c]
    fun_prop
  have hv : ContDiff ℝ ∞ v := by dsimp [v]; fun_prop
  have hs : ContDiff ℝ ∞ s := by dsimp [s]; fun_prop
  have hden : ∀ E, v E + δ.val ≠ 0 := by
    intro E
    have hv0 : 0 ≤ v E := by
      dsimp [v]
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => sq_nonneg _)
    exact ne_of_gt (lt_of_lt_of_le δ.property (le_add_of_nonneg_left hv0))
  have hquot := hs.div (hv.add contDiff_const) hden
  change ContDiff ℝ ∞ (fun E =>
    ((r + 1 : ℝ)⁻¹ * ∑ j : Fin (r + 1), E (j, Sum.inr 0)) +
      s E / (v E + δ.val) * (x - a E))
  apply ContDiff.add
  · fun_prop
  · exact hquot.mul (contDiff_const.sub ha)

/-- The literal public Ridge predictor is smooth on each member of a finite
closed cover, including agreement at all clipping boundaries. -/
theorem stabilizedLinearEstimator_finite_smooth_pieces (b δ : {t : ℝ // 0 < t})
    (r : ℕ) (x : ℝ) :
    (∀ mode : Fin (r + 1) → Fin 3,
      ContDiff ℝ ∞ (ridgePredictorSmoothPiece b δ r x mode) ∧
        Set.EqOn (stabilizedLinearEstimatorActualTrainingPredictor b δ r x)
          (ridgePredictorSmoothPiece b δ r x mode) (ridgeResponseChamber b.val r mode)) ∧
    (∀ E, ∃ mode : Fin (r + 1) → Fin 3, E ∈ ridgeResponseChamber b.val r mode) := by
  classical
  refine ⟨?_, ridgeResponseChambers_cover b.val r⟩
  intro mode
  refine ⟨ridgePredictorSmoothPiece_contDiff b δ r x mode, ?_⟩
  intro E hE
  have hU : (fun j : Fin (r + 1) => ridgeResponsePieceValue b.val (mode j) (E (j, Sum.inr 0))) =
      (fun j : Fin (r + 1) => max (min (E (j, Sum.inr 0)) b.val) (-b.val)) := by
    funext j
    exact ridgeResponsePieceValue_eq_clip b (mode j) _ (hE j)
  change
    ((r + 1 : ℝ)⁻¹ * ∑ j : Fin (r + 1), E (j, Sum.inr 0)) +
      ((r + 1 : ℝ)⁻¹ * ∑ j : Fin (r + 1),
        (E (j, Sum.inl 0) - (r + 1 : ℝ)⁻¹ * ∑ i : Fin (r + 1), E (i, Sum.inl 0)) *
          (max (min (E (j, Sum.inr 0)) b.val) (-b.val) -
            (r + 1 : ℝ)⁻¹ * ∑ i : Fin (r + 1), max (min (E (i, Sum.inr 0)) b.val) (-b.val))) /
        ((r + 1 : ℝ)⁻¹ * ∑ j : Fin (r + 1),
          (E (j, Sum.inl 0) - (r + 1 : ℝ)⁻¹ * ∑ i : Fin (r + 1), E (i, Sum.inl 0)) ^ 2 + δ.val) *
          (x - (r + 1 : ℝ)⁻¹ * ∑ j : Fin (r + 1), E (j, Sum.inl 0)) =
      ridgePredictorSmoothPiece b δ r x mode E
  dsimp only [ridgePredictorSmoothPiece]
  simp_rw [← congrFun hU]

/-- The actual public slope (prediction at one minus prediction at zero) uses
the same finite response cover and smooth branches. -/
theorem stabilizedLinearEstimator_slope_finite_smooth_pieces
    (b δ : {t : ℝ // 0 < t}) (r : ℕ) :
    ∀ mode : Fin (r + 1) → Fin 3,
      ContDiff ℝ ∞ (fun E => ridgePredictorSmoothPiece b δ r 1 mode E -
        ridgePredictorSmoothPiece b δ r 0 mode E) ∧
      Set.EqOn (fun E => stabilizedLinearEstimatorActualTrainingPredictor b δ r 1 E -
        stabilizedLinearEstimatorActualTrainingPredictor b δ r 0 E)
        (fun E => ridgePredictorSmoothPiece b δ r 1 mode E -
          ridgePredictorSmoothPiece b δ r 0 mode E) (ridgeResponseChamber b.val r mode) := by
  intro mode
  have h1 := (stabilizedLinearEstimator_finite_smooth_pieces b δ r 1).1 mode
  have h0 := (stabilizedLinearEstimator_finite_smooth_pieces b δ r 0).1 mode
  refine ⟨h1.1.sub h0.1, ?_⟩
  intro E hE
  dsimp only
  rw [h1.2 hE, h0.2 hE]

end LOOConcentration.Manuscript.Internal
