import LOOConcentrationManuscript.Internal.PositiveQuotientDerivative
import LOOConcentration.Frozen.Foundations.Observation
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Algebra.BigOperators.Field

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal

/-- Positive stabilization supplies the denominator condition for every dataset,
without an additional proof-step hypothesis. -/
theorem stabilizedKernel_denominator_pos
    (r : ℕ) (w : Fin (r + 1) → ℝ) (hw : ∀ i, 0 ≤ w i)
    (δ : ℝ) (hδ : 0 < δ) :
    0 < (∑ i : Fin (r + 1), w i) + (r + 1 : ℝ) * δ := by
  have hsum : 0 ≤ ∑ i : Fin (r + 1), w i := Finset.sum_nonneg (fun i _ => hw i)
  exact add_pos_of_nonneg_of_pos hsum (mul_pos (by positivity) hδ)

/-- The actual response-coordinate derivative of the manuscript's stabilized
kernel quotient. The nonzero denominator is derived from source kernel and
stabilization assumptions. -/
theorem stabilizedKernel_response_coordinate_hasDerivAt
    (K : ℝ → ℝ) (hK : ∀ t, 0 ≤ K t) (h δ : ℝ) (hh : 0 < h) (hδ : 0 < δ)
    (r : ℕ) (D : Fin (r + 1) → LOOConcentration.Observation 1 1)
    (x : ℝ) (j : Fin (r + 1)) :
    let w := fun i : Fin (r + 1) => K ((x - (D i).1 0) / h) / h
    let B := (∑ i : Fin (r + 1), w i) + (r + 1 : ℝ) * δ
    HasDerivAt
      (fun t : ℝ => (∑ i : Fin (r + 1), w i *
        Function.update (fun i : Fin (r + 1) => (D i).2 0) j t i) / B)
      (w j / B) ((D j).2 0) := by
  classical
  intro w B
  have hB : 0 < B := stabilizedKernel_denominator_pos r w
    (fun i => div_nonneg (hK _) hh.le) δ hδ
  have hcoord (i : Fin (r + 1)) : HasDerivAt
      (fun t : ℝ => Function.update (fun i : Fin (r + 1) => (D i).2 0) j t i)
      (if i = j then 1 else 0) ((D j).2 0) := by
    by_cases hij : i = j
    · subst i
      simpa only [Function.update_self, if_pos rfl, ite_true] using hasDerivAt_id' (𝕜 := ℝ) ((D j).2 0)
    · simpa only [Function.update_of_ne hij, if_neg hij] using
        hasDerivAt_const ((D j).2 0) ((D i).2 0)
  have hNum : HasDerivAt
      (fun t : ℝ => ∑ i : Fin (r + 1), w i *
        Function.update (fun i : Fin (r + 1) => (D i).2 0) j t i)
      (w j) ((D j).2 0) := by
    simpa using HasDerivAt.fun_sum (u := Finset.univ)
      (fun i _ => (hasDerivAt_const ((D j).2 0) (w i)).mul (hcoord i))
  have hDen : HasDerivAt (fun _t : ℝ => B) 0 ((D j).2 0) :=
    hasDerivAt_const ((D j).2 0) B
  have hDivF := positiveDenominator_quotient_hasFDerivAt _ _ _ _ ((D j).2 0)
    hNum.hasFDerivAt hDen.hasFDerivAt hB
  have hc : (B ^ 2)⁻¹ * (B * w j) = w j / B := by
    field_simp
  simpa only [smul_apply, sub_apply,
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_one, one_mul,
    mul_zero, sub_zero, hc] using hDivF.hasDerivAt

/-- The same derivative for the literal predictor on an actual dataset update:
all features and all other responses are retained. -/
theorem stabilizedKernel_actualDataset_response_hasDerivAt
    (K : ℝ → ℝ) (hK : ∀ t, 0 ≤ K t) (h δ : ℝ) (hh : 0 < h) (hδ : 0 < δ)
    (r : ℕ) (D : Fin (r + 1) → LOOConcentration.Observation 1 1)
    (x : ℝ) (j : Fin (r + 1)) :
    let w := fun i : Fin (r + 1) => K ((x - (D i).1 0) / h) / h
    let B := (∑ i : Fin (r + 1), w i) + (r + 1 : ℝ) * δ
    let T := fun E : Fin (r + 1) → LOOConcentration.Observation 1 1 =>
      (∑ i : Fin (r + 1), (K ((x - (E i).1 0) / h) / h) * (E i).2 0) /
        ((∑ i : Fin (r + 1), K ((x - (E i).1 0) / h) / h) + (r + 1 : ℝ) * δ)
    HasDerivAt
      (fun t : ℝ => T (Function.update D j ((D j).1, fun _ : Fin 1 => t)))
      (w j / B) ((D j).2 0) := by
  classical
  intro w B T
  have hFeature (t : ℝ) (i : Fin (r + 1)) :
      (Function.update D j ((D j).1, fun _ : Fin 1 => t) i).1 0 = (D i).1 0 := by
    by_cases hij : i = j <;> simp [hij, Function.update_of_ne]
  have hResponse (t : ℝ) (i : Fin (r + 1)) :
      (Function.update D j ((D j).1, fun _ : Fin 1 => t) i).2 0 =
        Function.update (fun i : Fin (r + 1) => (D i).2 0) j t i := by
    by_cases hij : i = j <;> simp [hij, Function.update_of_ne]
  have hFunction : (fun t : ℝ => T (Function.update D j ((D j).1, fun _ : Fin 1 => t))) =
      (fun t : ℝ => (∑ i : Fin (r + 1), w i *
        Function.update (fun i : Fin (r + 1) => (D i).2 0) j t i) / B) := by
    funext t
    dsimp [T, w, B]
    simp only [hFeature, hResponse]
  rw [hFunction]
  exact stabilizedKernel_response_coordinate_hasDerivAt K hK h δ hh hδ r D x j

end LOOConcentration.Manuscript.Internal
