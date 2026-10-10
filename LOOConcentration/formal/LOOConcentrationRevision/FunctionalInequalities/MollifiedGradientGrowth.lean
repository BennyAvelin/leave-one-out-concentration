import LOOConcentration.Analysis.ClipMollify
import LOOConcentrationRevision.FunctionalInequalities.BoundedSmoothPair
import Mathlib.Analysis.Calculus.ContDiff.Convolution

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory Filter InnerProductSpace ContinuousLinearMap
open scoped ENNReal Convolution

/-- Differentiating the compact kernel gives a global bound even when the
clipped function is merely continuous. The same kernel and actual derivative
are used in the convolution. -/
theorem gradient_convolution_uniform_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K G : EuclideanSpace ℝ ι → ℝ) (hK : ContDiff ℝ 1 K)
    (hKsupport : HasCompactSupport K) (hG : Continuous G)
    (R : ℝ) (_hR : 0 ≤ R) (hbound : ∀ x, |G x| ≤ R)
    (x : EuclideanSpace ℝ ι) :
    ‖gradient (K ⋆[lsmul ℝ ℝ, Measure.addHaar] G) x‖ ≤
      R * ∫ t, ‖fderiv ℝ K t‖ ∂(Measure.addHaar : Measure (EuclideanSpace ℝ ι)) := by
  let E := EuclideanSpace ℝ ι
  let L : (E →L[ℝ] ℝ) →L[ℝ] ℝ →L[ℝ] (E →L[ℝ] ℝ) :=
    (lsmul ℝ ℝ).precompL E
  have hpre (v : E →L[ℝ] ℝ) (c : ℝ) : L v c = c • v := by
    ext z
    simp [L, ContinuousLinearMap.precompL_apply, smul_eq_mul, mul_comm]
  have hd := hKsupport.hasFDerivAt_convolution_left (lsmul ℝ ℝ)
    hK (hG.locallyIntegrable (μ := (Measure.addHaar : Measure E))) x
  have hDcont : Continuous (fderiv ℝ K) := hK.continuous_fderiv one_ne_zero
  have hDsupport : HasCompactSupport (fderiv ℝ K) := hKsupport.fderiv ℝ
  have hDint : Integrable (fun t => ‖fderiv ℝ K t‖)
      (Measure.addHaar : Measure E) :=
    hDcont.norm.integrable_of_hasCompactSupport hDsupport.norm
  have hInt : Integrable (fun t => L (fderiv ℝ K t) (G (x - t)))
      (Measure.addHaar : Measure E) :=
    hDsupport.convolutionExists_left L hDcont (hG.locallyIntegrable (μ := (Measure.addHaar : Measure E))) x
  calc
    ‖gradient (K ⋆[lsmul ℝ ℝ, Measure.addHaar] G) x‖ =
        ‖fderiv ℝ (K ⋆[lsmul ℝ ℝ, Measure.addHaar] G) x‖ := by
      rw [gradient, (toDual ℝ E).symm.norm_map]
    _ = ‖∫ t, L (fderiv ℝ K t) (G (x - t)) ∂Measure.addHaar‖ := by
      rw [hd.fderiv]
      rfl
    _ ≤ ∫ t, ‖L (fderiv ℝ K t) (G (x - t))‖ ∂Measure.addHaar := norm_integral_le_integral_norm _
    _ ≤ ∫ t, R * ‖fderiv ℝ K t‖ ∂Measure.addHaar := by
      apply integral_mono hInt.norm (hDint.const_mul R)
      intro t
      dsimp only
      rw [hpre, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hbound (x - t)) (norm_nonneg _)
    _ = R * ∫ t, ‖fderiv ℝ K t‖ ∂Measure.addHaar := integral_const_mul _ _

/-- The segment estimate is still an internal input until its source producer
is integrated. This consumer preserves a, b, radius and the actual gradient. -/
theorem clipThenMollify_gradient_growth {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : EuclideanSpace ℝ ι → ℝ) (hF : Continuous F)
    (a b : NNReal) (R : ℝ) (η : ℝ) (hη : 0 < η)
    (hseg : ∀ x y, |F x - F y| ≤ ‖x - y‖ *
      ((a : ℝ) + (b : ℝ) / 2 * (‖x‖ + ‖y‖)))
    (x : EuclideanSpace ℝ ι) :
    ‖gradient (clipThenMollify F R η) x‖ ≤
      (a : ℝ) + (b : ℝ) * η + (b : ℝ) * ‖x‖ := by
  have hs : HasLinearGrowthSegmentBound F (a : ℝ) (b : ℝ) := by
    intro y z
    simpa only [dist_eq_norm] using hseg y z
  have hc := clipFunction_segmentBound (N := R) hs
  rw [gradient, (toDual ℝ (EuclideanSpace ℝ ι)).symm.norm_map]
  exact clipThenMollify_fderiv_bound hF hη hc a.property b.property x

end LOOConcentration.Revision
