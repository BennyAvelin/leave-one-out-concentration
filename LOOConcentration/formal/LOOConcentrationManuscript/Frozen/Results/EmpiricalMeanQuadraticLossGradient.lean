import LOOConcentrationManuscript.Frozen.Definitions.EmpiricalMean
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Gradient.Basic
import LOOConcentrationRevision.Frozen.Bridges.Ae_gradient_segment_estimate
import LOOConcentrationRevision.Correspondence.SourceGradient

set_option autoImplicit false
namespace LOOConcentration.Manuscript
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem empiricalMean_quadraticLoss_gradient_bound (r : ℕ) (z : ℝ)
    (D : EuclideanSpace ℝ (Fin (r + 1))) :
    ‖gradient (fun E : EuclideanSpace ℝ (Fin (r + 1)) =>
        (empiricalMean r E - z) ^ 2) D‖ ≤
      2 * |z| / Real.sqrt ((r + 1 : ℕ) : ℝ) +
        (2 / ((r + 1 : ℕ) : ℝ)) * ‖D‖ := by
  classical
  let empiricalMeanVector (r : ℕ) : EuclideanSpace ℝ (Fin (r + 1)) :=
    WithLp.toLp 2 (fun _ : Fin (r + 1) => (1 : ℝ))

  have empiricalMeanVector_norm (r : ℕ) :
      ‖empiricalMeanVector r‖ = Real.sqrt ((r + 1 : ℕ) : ℝ) := by
    rw [EuclideanSpace.norm_eq]
    simp [empiricalMeanVector]

  have empiricalMeanVector_inner (r : ℕ)
      (D : EuclideanSpace ℝ (Fin (r + 1))) :
      inner ℝ (empiricalMeanVector r) D = ∑ i, D i := by
    rw [PiLp.inner_apply]
    simp [empiricalMeanVector]

  let empiricalMeanLinearMap (r : ℕ) :
      EuclideanSpace ℝ (Fin (r + 1)) →L[ℝ] ℝ :=
    ((r + 1 : ℕ) : ℝ)⁻¹ • (innerSL ℝ (empiricalMeanVector r))

  have empiricalMeanLinearMap_apply (r : ℕ)
      (D : EuclideanSpace ℝ (Fin (r + 1))) :
      empiricalMeanLinearMap r D =
        ((r + 1 : ℕ) : ℝ)⁻¹ * inner ℝ (empiricalMeanVector r) D := by
    simp [empiricalMeanLinearMap, innerSL_apply_apply]

  have empiricalMean_eq_linearMap (r : ℕ)
      (D : EuclideanSpace ℝ (Fin (r + 1))) :
      empiricalMean r D = empiricalMeanLinearMap r D := by
    rw [empiricalMean, empiricalMeanLinearMap_apply, empiricalMeanVector_inner]

  have empiricalMean_abs_bound (r : ℕ)
      (D : EuclideanSpace ℝ (Fin (r + 1))) :
      |empiricalMean r D| ≤ ‖D‖ / Real.sqrt ((r + 1 : ℕ) : ℝ) := by
    rw [empiricalMean_eq_linearMap, empiricalMeanLinearMap_apply]
    let n : ℝ := ((r + 1 : ℕ) : ℝ)
    have hn : 0 < n := by dsimp [n]; positivity
    have hn0 : n ≠ 0 := ne_of_gt hn
    have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
    have hs0 : Real.sqrt n ≠ 0 := ne_of_gt hs
    have hcoeff : n⁻¹ * Real.sqrt n = (Real.sqrt n)⁻¹ := by
      field_simp [hn0, hs0]
      nlinarith [Real.sq_sqrt hn.le]
    have hinv_nonneg : 0 ≤ n⁻¹ := by positivity
    calc
      |n⁻¹ * inner ℝ (empiricalMeanVector r) D| =
          n⁻¹ * |inner ℝ (empiricalMeanVector r) D| := by
            rw [abs_mul, abs_of_nonneg hinv_nonneg]
      _ ≤ n⁻¹ * (‖empiricalMeanVector r‖ * ‖D‖) :=
          mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) hinv_nonneg
      _ = ‖D‖ / Real.sqrt n := by
        rw [empiricalMeanVector_norm]
        calc
          n⁻¹ * (Real.sqrt n * ‖D‖) = (n⁻¹ * Real.sqrt n) * ‖D‖ := by ring
          _ = (Real.sqrt n)⁻¹ * ‖D‖ := by rw [hcoeff]
          _ = ‖D‖ / Real.sqrt n := by rw [div_eq_mul_inv]; ring

  have empiricalMean_quadraticLoss_gradient_formula (r : ℕ) (z : ℝ)
      (D : EuclideanSpace ℝ (Fin (r + 1))) :
      gradient (fun E : EuclideanSpace ℝ (Fin (r + 1)) =>
          (empiricalMean r E - z) ^ 2) D =
        ((2 * (empiricalMean r D - z) * ((r + 1 : ℕ) : ℝ)⁻¹) •
          empiricalMeanVector r) := by
    have hf0 : HasFDerivAt (fun E : EuclideanSpace ℝ (Fin (r + 1)) =>
        empiricalMeanLinearMap r E - z) (empiricalMeanLinearMap r) D :=
      (empiricalMeanLinearMap r).hasFDerivAt.sub_const z
    have hf : HasFDerivAt (fun E : EuclideanSpace ℝ (Fin (r + 1)) =>
        empiricalMean r E - z) (empiricalMeanLinearMap r) D := by
      apply hf0.congr_of_eventuallyEq
      filter_upwards with E
      rw [empiricalMean_eq_linearMap]
    have hquad := hf.pow 2
    let g : EuclideanSpace ℝ (Fin (r + 1)) :=
      (2 * (empiricalMean r D - z) * ((r + 1 : ℕ) : ℝ)⁻¹) • empiricalMeanVector r
    have hdual : (InnerProductSpace.toDual ℝ _ ) g =
        (2 • (empiricalMean r D - z) ^ (2 - 1)) • empiricalMeanLinearMap r := by
      ext E
      simp [g, empiricalMeanLinearMap, InnerProductSpace.toDual_apply_apply,
        innerSL_apply_apply, smul_eq_mul]
      ring
    have hgrad : HasFDerivAt (fun E : EuclideanSpace ℝ (Fin (r + 1)) =>
        (empiricalMean r E - z) ^ 2) (InnerProductSpace.toDual ℝ _ g) D :=
      hquad.congr_fderiv hdual.symm
    calc
      gradient (fun E : EuclideanSpace ℝ (Fin (r + 1)) =>
          (empiricalMean r E - z) ^ 2) D =
        ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin (r + 1)))).symm
          ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin (r + 1)))) g)) :=
            hgrad.hasGradientAt.gradient
      _ = g := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin (r + 1)))).symm_apply_apply g

  let n : ℝ := ((r + 1 : ℕ) : ℝ)
  have hn : 0 < n := by dsimp [n]; positivity
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  have hs2 : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn.le
  have hmean := empiricalMean_abs_bound r D
  have hmean' : |empiricalMean r D| / Real.sqrt n ≤ ‖D‖ / n := by
    calc
      |empiricalMean r D| / Real.sqrt n ≤
          (‖D‖ / Real.sqrt n) / Real.sqrt n := by gcongr
      _ = ‖D‖ / n := by rw [div_div, hs2]
  have htriangle : |empiricalMean r D - z| ≤
      |z| + |empiricalMean r D| := by
    calc
      |empiricalMean r D - z| ≤ |empiricalMean r D| + |z| := by
        simpa [add_comm] using abs_sub_le (empiricalMean r D) 0 z
      _ = |z| + |empiricalMean r D| := by ring
  have hbound :
      2 * |empiricalMean r D - z| / Real.sqrt n ≤
        2 * |z| / Real.sqrt n + (2 / n) * ‖D‖ := by
    calc
      2 * |empiricalMean r D - z| / Real.sqrt n ≤
          2 * (|z| + |empiricalMean r D|) / Real.sqrt n := by gcongr
      _ = 2 * |z| / Real.sqrt n + 2 * |empiricalMean r D| / Real.sqrt n := by ring
      _ = 2 * |z| / Real.sqrt n + 2 * (|empiricalMean r D| / Real.sqrt n) := by ring
      _ ≤ 2 * |z| / Real.sqrt n + 2 * (‖D‖ / n) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hmean' (by norm_num : 0 ≤ (2 : ℝ)))
      _ = 2 * |z| / Real.sqrt n + (2 / n) * ‖D‖ := by ring
  have hn0 : n ≠ 0 := ne_of_gt hn
  have hs0 : Real.sqrt n ≠ 0 := ne_of_gt hs
  have hcoeff : n⁻¹ * Real.sqrt n = (Real.sqrt n)⁻¹ := by
    field_simp [hn0, hs0]
    nlinarith [Real.sq_sqrt hn.le]
  calc
    ‖gradient (fun E : EuclideanSpace ℝ (Fin (r + 1)) =>
        (empiricalMean r E - z) ^ 2) D‖ =
      |2 * (empiricalMean r D - z) * n⁻¹| * Real.sqrt n := by
        rw [empiricalMean_quadraticLoss_gradient_formula, norm_smul,
          Real.norm_eq_abs, empiricalMeanVector_norm]
    _ = 2 * |empiricalMean r D - z| / Real.sqrt n := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ)),
        abs_of_nonneg (by positivity : 0 ≤ n⁻¹)]
      calc
        (2 * |empiricalMean r D - z| * n⁻¹) * Real.sqrt n =
            2 * |empiricalMean r D - z| * (n⁻¹ * Real.sqrt n) := by ring
        _ = 2 * |empiricalMean r D - z| * (Real.sqrt n)⁻¹ := by rw [hcoeff]
        _ = 2 * |empiricalMean r D - z| / Real.sqrt n := by rw [div_eq_mul_inv]
    _ ≤ 2 * |z| / Real.sqrt n + (2 / n) * ‖D‖ := hbound

end LOOConcentration.Manuscript
