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

theorem empiricalMean_absoluteLoss_lipschitz (r : ℕ) (z : ℝ) :
    LipschitzWith (Real.toNNReal (Real.sqrt ((r + 1 : ℕ) : ℝ))⁻¹)
      (fun D : EuclideanSpace ℝ (Fin (r + 1)) => |empiricalMean r D - z|) := by
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

  have empiricalMean_sub (r : ℕ)
      (D E : EuclideanSpace ℝ (Fin (r + 1))) :
      empiricalMean r D - empiricalMean r E = empiricalMeanLinearMap r (D - E) := by
    calc
      empiricalMean r D - empiricalMean r E =
          empiricalMeanLinearMap r D - empiricalMeanLinearMap r E := by
            rw [empiricalMean_eq_linearMap, empiricalMean_eq_linearMap]
      _ = empiricalMeanLinearMap r (D - E) := by rw [map_sub]

  refine LipschitzWith.of_dist_le_mul fun D E => ?_
  rw [Real.dist_eq, dist_eq_norm]
  have hn : 0 < ((r + 1 : ℕ) : ℝ) := by positivity
  have hs : 0 < Real.sqrt ((r + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 hn
  have hconstant :
      (Real.toNNReal (Real.sqrt ((r + 1 : ℕ) : ℝ))⁻¹ : ℝ) =
        (Real.sqrt ((r + 1 : ℕ) : ℝ))⁻¹ := by
    simp
  calc
    |(|empiricalMean r D - z| - |empiricalMean r E - z|)| ≤
        |(empiricalMean r D - z) - (empiricalMean r E - z)| :=
          abs_abs_sub_abs_le_abs_sub _ _
    _ = |empiricalMeanLinearMap r (D - E)| := by
      congr 1
      calc
        (empiricalMean r D - z) - (empiricalMean r E - z) =
            empiricalMean r D - empiricalMean r E := by ring
        _ = empiricalMeanLinearMap r (D - E) := empiricalMean_sub r D E
    _ ≤ ‖D - E‖ / Real.sqrt ((r + 1 : ℕ) : ℝ) := by
      rw [← empiricalMean_eq_linearMap r (D - E)]
      exact empiricalMean_abs_bound r (D - E)
    _ = (Real.toNNReal (Real.sqrt ((r + 1 : ℕ) : ℝ))⁻¹ : ℝ) * ‖D - E‖ := by
      rw [hconstant]
      ring

end LOOConcentration.Manuscript
