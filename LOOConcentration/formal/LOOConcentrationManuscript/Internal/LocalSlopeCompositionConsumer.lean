import LOOConcentrationManuscript.Internal.LocalSlopeComposition
import LOOConcentrationManuscript.Internal.LipschitzSlopeGradient
import LOOConcentrationManuscript.Frozen.Results.EmpiricalMeanAbsoluteLossLipschitz

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal

open Filter
open scoped Topology

/-- The approved absolute-loss Lipschitz estimate, evaluated at the second
mean, gives the matching global Lipschitz bound for the actual empirical mean. -/
theorem empiricalMean_lipschitz (r : ℕ) :
    LipschitzWith (Real.toNNReal (Real.sqrt ((r + 1 : ℕ) : ℝ))⁻¹)
      (empiricalMean r) := by
  refine LipschitzWith.of_dist_le_mul fun D E => ?_
  have h := (empiricalMean_absoluteLoss_lipschitz r (empiricalMean r E)).norm_sub_le D E
  simpa [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs] using h

/-- The actual empirical-mean quadratic loss satisfies both its local-slope
bound and the source gradient-growth bound. The gradient conclusion uses the
actual differentiable chain rule at the same point. -/
theorem empiricalMean_quadraticLoss_local_slope_and_gradient_bound
    (r : ℕ) (y : ℝ) (D : EuclideanSpace ℝ (Fin (r + 1))) :
    (limsup (fun E : EuclideanSpace ℝ (Fin (r + 1)) =>
      |(empiricalMean r E - y) ^ 2 - (empiricalMean r D - y) ^ 2| / ‖E - D‖)
      (𝓝[≠] D) ≤ 2 * |empiricalMean r D - y| /
        Real.sqrt ((r + 1 : ℕ) : ℝ)) ∧
    ‖gradient (fun E : EuclideanSpace ℝ (Fin (r + 1)) =>
        (empiricalMean r E - y) ^ 2) D‖ ≤
      2 * |y| / Real.sqrt ((r + 1 : ℕ) : ℝ) +
        (2 / ((r + 1 : ℕ) : ℝ)) * ‖D‖ := by
  let K : NNReal := Real.toNNReal (Real.sqrt ((r + 1 : ℕ) : ℝ))⁻¹
  have hmeanLip : LipschitzWith K (empiricalMean r) := by
    change LipschitzWith (Real.toNNReal (Real.sqrt ((r + 1 : ℕ) : ℝ))⁻¹)
      (empiricalMean r)
    exact empiricalMean_lipschitz r
  have hroot : 0 < Real.sqrt ((r + 1 : ℕ) : ℝ) := by
    apply Real.sqrt_pos.2
    positivity
  have hK : (K : ℝ) = (Real.sqrt ((r + 1 : ℕ) : ℝ))⁻¹ := by
    change ((Real.toNNReal (Real.sqrt ((r + 1 : ℕ) : ℝ))⁻¹ : NNReal) : ℝ) = _
    exact Real.coe_toNNReal _ (inv_nonneg.mpr hroot.le)
  have hmeanLocallyLip : LocallyLipschitz (empiricalMean r) := hmeanLip.locallyLipschitz
  have hmeanSlope := lipschitz_euclidean_slope_and_gradient_le r
    (empiricalMean r) K hmeanLip D
  have hmeanDiff : DifferentiableAt ℝ (empiricalMean r) D := by
    fun_prop [empiricalMean]
  have hmeanFDerivBound : ‖fderiv ℝ (empiricalMean r) D‖ ≤ (K : ℝ) := by
    exact_mod_cast hmeanDiff.hasFDerivAt.le_of_lipschitz hmeanLip
  have hmeanGradientBound : ‖gradient (empiricalMean r) D‖ ≤
      (Real.sqrt ((r + 1 : ℕ) : ℝ))⁻¹ := by
    calc
      ‖gradient (empiricalMean r) D‖ = ‖fderiv ℝ (empiricalMean r) D‖ := by
        rw [gradient]
        exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin (r + 1)))).symm.norm_map _
      _ ≤ (K : ℝ) := hmeanFDerivBound
      _ = (Real.sqrt ((r + 1 : ℕ) : ℝ))⁻¹ := hK
  have hzero : empiricalMean r (0 : EuclideanSpace ℝ (Fin (r + 1))) = 0 := by
    simp [empiricalMean]
  have hmeanAbs : |empiricalMean r D| ≤
      ‖D‖ / Real.sqrt ((r + 1 : ℕ) : ℝ) := by
    have h := hmeanLip.norm_sub_le D 0
    have h' : |empiricalMean r D| ≤ (K : ℝ) * ‖D‖ := by
      simpa [hzero, Real.norm_eq_abs] using h
    calc
      |empiricalMean r D| ≤ (Real.sqrt ((r + 1 : ℕ) : ℝ))⁻¹ * ‖D‖ := by
        simpa only [hK] using h'
      _ = ‖D‖ / Real.sqrt ((r + 1 : ℕ) : ℝ) := by rw [div_eq_mul_inv]; ring
  have hresidual : |empiricalMean r D - y| ≤ |y| + |empiricalMean r D| := by
    calc
      |empiricalMean r D - y| ≤ |empiricalMean r D| + |y| := by
        simpa using abs_sub_le (empiricalMean r D) 0 y
      _ = |y| + |empiricalMean r D| := by ring
  have hn : 0 < ((r + 1 : ℕ) : ℝ) := by positivity
  have hs : 0 < Real.sqrt ((r + 1 : ℕ) : ℝ) := hroot
  have hs2 : Real.sqrt ((r + 1 : ℕ) : ℝ) * Real.sqrt ((r + 1 : ℕ) : ℝ) =
      ((r + 1 : ℕ) : ℝ) := Real.mul_self_sqrt hn.le
  have hmeanAbs' : |empiricalMean r D| / Real.sqrt ((r + 1 : ℕ) : ℝ) ≤
      ‖D‖ / ((r + 1 : ℕ) : ℝ) := by
    calc
      |empiricalMean r D| / Real.sqrt ((r + 1 : ℕ) : ℝ) ≤
          (‖D‖ / Real.sqrt ((r + 1 : ℕ) : ℝ)) /
            Real.sqrt ((r + 1 : ℕ) : ℝ) := by gcongr
      _ = ‖D‖ / ((r + 1 : ℕ) : ℝ) := by rw [div_div, hs2]
  have hgradientBound :
      2 * |empiricalMean r D - y| / Real.sqrt ((r + 1 : ℕ) : ℝ) ≤
        2 * |y| / Real.sqrt ((r + 1 : ℕ) : ℝ) +
          (2 / ((r + 1 : ℕ) : ℝ)) * ‖D‖ := by
    calc
      2 * |empiricalMean r D - y| / Real.sqrt ((r + 1 : ℕ) : ℝ) ≤
          2 * (|y| + |empiricalMean r D|) /
            Real.sqrt ((r + 1 : ℕ) : ℝ) := by gcongr
      _ = 2 * |y| / Real.sqrt ((r + 1 : ℕ) : ℝ) +
          2 * |empiricalMean r D| / Real.sqrt ((r + 1 : ℕ) : ℝ) := by ring
      _ ≤ 2 * |y| / Real.sqrt ((r + 1 : ℕ) : ℝ) +
          2 * (‖D‖ / ((r + 1 : ℕ) : ℝ)) := by
        apply add_le_add_right
        calc
          2 * |empiricalMean r D| / Real.sqrt ((r + 1 : ℕ) : ℝ) =
              2 * (|empiricalMean r D| / Real.sqrt ((r + 1 : ℕ) : ℝ)) := by ring
          _ ≤ 2 * (‖D‖ / ((r + 1 : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left hmeanAbs' (by norm_num)
      _ = 2 * |y| / Real.sqrt ((r + 1 : ℕ) : ℝ) +
          (2 / ((r + 1 : ℕ) : ℝ)) * ‖D‖ := by ring
  constructor
  · have hlocal := local_slope_square_loss_le r (empiricalMean r) hmeanLocallyLip y D
    calc
      limsup (fun E : EuclideanSpace ℝ (Fin (r + 1)) =>
          |(empiricalMean r E - y) ^ 2 - (empiricalMean r D - y) ^ 2| / ‖E - D‖)
          (𝓝[≠] D) ≤
          2 * |empiricalMean r D - y| *
            limsup (fun E : EuclideanSpace ℝ (Fin (r + 1)) =>
              |empiricalMean r E - empiricalMean r D| / ‖E - D‖) (𝓝[≠] D) := hlocal
      _ ≤ 2 * |empiricalMean r D - y| * (K : ℝ) :=
        mul_le_mul_of_nonneg_left hmeanSlope.1 (by positivity)
      _ = 2 * |empiricalMean r D - y| / Real.sqrt ((r + 1 : ℕ) : ℝ) := by
        rw [hK, div_eq_mul_inv]
  · have hchain := gradient_square_loss_chain_rule r (empiricalMean r) y D hmeanDiff
    calc
      ‖gradient (fun E : EuclideanSpace ℝ (Fin (r + 1)) =>
          (empiricalMean r E - y) ^ 2) D‖ =
          2 * |empiricalMean r D - y| * ‖gradient (empiricalMean r) D‖ := by
            rw [hchain, norm_smul, Real.norm_eq_abs, abs_mul,
              abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
      _ ≤ 2 * |empiricalMean r D - y| /
          Real.sqrt ((r + 1 : ℕ) : ℝ) := by
        calc
          2 * |empiricalMean r D - y| * ‖gradient (empiricalMean r) D‖ ≤
              2 * |empiricalMean r D - y| *
                (Real.sqrt ((r + 1 : ℕ) : ℝ))⁻¹ :=
                  mul_le_mul_of_nonneg_left hmeanGradientBound (by positivity)
          _ = 2 * |empiricalMean r D - y| /
              Real.sqrt ((r + 1 : ℕ) : ℝ) := by rw [div_eq_mul_inv]
      _ ≤ 2 * |y| / Real.sqrt ((r + 1 : ℕ) : ℝ) +
          (2 / ((r + 1 : ℕ) : ℝ)) * ‖D‖ := hgradientBound

end LOOConcentration.Manuscript.Internal
