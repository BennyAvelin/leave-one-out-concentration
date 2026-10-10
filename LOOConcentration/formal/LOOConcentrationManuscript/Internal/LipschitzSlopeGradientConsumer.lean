import LOOConcentrationManuscript.Internal.LipschitzSlopeGradient

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LOOConcentration.Manuscript.Internal

open Filter
open scoped Topology ENNReal

theorem empiricalMean_absoluteLoss_slope_and_gradient_bound
    (r : ℕ) (z : ℝ)
    (D : EuclideanSpace ℝ (Fin (r + 1))) :
    (limsup (fun E : EuclideanSpace ℝ (Fin (r + 1)) =>
      |(|empiricalMean r E - z|) - (|empiricalMean r D - z|)| / ‖E - D‖)
      (𝓝[≠] D) ≤ (Real.sqrt ((r + 1 : ℕ) : ℝ))⁻¹) ∧
    ‖gradient (fun E : EuclideanSpace ℝ (Fin (r + 1)) =>
      |empiricalMean r E - z|) D‖ ≤ (Real.sqrt ((r + 1 : ℕ) : ℝ))⁻¹ := by
  let K : NNReal := Real.toNNReal (Real.sqrt ((r + 1 : ℕ) : ℝ))⁻¹
  have hLip : LipschitzWith K
      (fun E : EuclideanSpace ℝ (Fin (r + 1)) => |empiricalMean r E - z|) := by
    change LipschitzWith
      (Real.toNNReal (Real.sqrt ((r + 1 : ℕ) : ℝ))⁻¹)
      (fun E : EuclideanSpace ℝ (Fin (r + 1)) => |empiricalMean r E - z|)
    exact empiricalMean_absoluteLoss_lipschitz r z
  have hroot : 0 < Real.sqrt ((r + 1 : ℕ) : ℝ) := by
    apply Real.sqrt_pos.2
    positivity
  have hK : (K : ℝ) = (Real.sqrt ((r + 1 : ℕ) : ℝ))⁻¹ := by
    change ((Real.toNNReal (Real.sqrt ((r + 1 : ℕ) : ℝ))⁻¹ : NNReal) : ℝ) = _
    exact Real.coe_toNNReal _ (inv_nonneg.mpr hroot.le)
  have hbound := lipschitz_euclidean_slope_and_gradient_le r
    (fun E : EuclideanSpace ℝ (Fin (r + 1)) => |empiricalMean r E - z|)
    K hLip D
  constructor
  · calc
      limsup (fun E : EuclideanSpace ℝ (Fin (r + 1)) =>
          |(|empiricalMean r E - z|) - (|empiricalMean r D - z|)| / ‖E - D‖)
          (𝓝[≠] D) ≤ (K : ℝ) := hbound.1
      _ = (Real.sqrt ((r + 1 : ℕ) : ℝ))⁻¹ := hK
  · calc
      ‖gradient (fun E : EuclideanSpace ℝ (Fin (r + 1)) =>
          |empiricalMean r E - z|) D‖ ≤ (K : ℝ) := hbound.2
      _ = (Real.sqrt ((r + 1 : ℕ) : ℝ))⁻¹ := hK

end LOOConcentration.Manuscript.Internal
