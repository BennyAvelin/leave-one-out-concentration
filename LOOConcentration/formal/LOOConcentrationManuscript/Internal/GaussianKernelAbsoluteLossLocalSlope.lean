import LOOConcentrationManuscript.Internal.GaussianKernelAmbientRegularityConsumer
import LOOConcentrationManuscript.Internal.GaussianKernelSharedGradientConstantConsumer
import LOOConcentration.Geometry.SmoothLocalSlope
import LOOConcentration.Geometry.LocalSlopeFacts
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LOOConcentration.Manuscript.Internal

open Filter
open ProbabilityTheory
open scoped Topology ContDiff

/-- The actual Gaussian absolute fitted loss is locally Lipschitz on the full
source data carrier, and its frozen local slope obeys the source growth bound.
The shared constant is fixed before the sample size, query, response, and data. -/
theorem gaussianKernel_actual_absoluteLoss_localSlope_bound
    (h δ : ℝ) (hh : 0 < h) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℕ) (x y : ℝ),
      ∃ f : LOOConcentration.LocallyLipschitzDataFunction 0 0 r,
        (∀ D : LOOConcentration.DataCarrier 0 0 r,
          f.1 D = abs
            ((∑ i : Fin (r + 1),
                (gaussianPDFReal 0 1 ((x - (D i).1 0) / h) / h) * (D i).2 0) /
              ((∑ i : Fin (r + 1),
                gaussianPDFReal 0 1 ((x - (D i).1 0) / h) / h) +
                (r + 1 : ℝ) * δ) - y)) ∧
        (∀ D : LOOConcentration.DataCarrier 0 0 r,
          LOOConcentration.datasetLocalSlope f D ≤
            C / Real.sqrt (r + 1 : ℝ) +
              C * LOOConcentration.datasetNorm D / (r + 1 : ℝ)) := by
  obtain ⟨C, hC, hShared⟩ :=
    gaussianKernel_source_shared_gradient_constant h δ hh hδ
  refine ⟨C, hC, ?_⟩
  intro r x y
  let Kh : ℝ → ℝ := fun t => gaussianPDFReal 0 1 (t / h) / h
  let T : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1)) → ℝ := fun E =>
    (∑ i : Fin (r + 1), Kh (x - E (i, Sum.inl 0)) * E (i, Sum.inr 0)) /
      ((∑ i : Fin (r + 1), Kh (x - E (i, Sum.inl 0))) + (r + 1 : ℝ) * δ)
  have hSmooth : ContDiff ℝ ∞ T := by
    exact gaussianKernel_predictor_ambient_contDiff h δ hh hδ r x
  have hSmoothOne : ContDiff ℝ 1 T := hSmooth.of_le (by norm_num)
  let g : LOOConcentration.LocallyLipschitzDataFunction 0 0 r :=
    LOOConcentration.smoothDatasetPullback T hSmoothOne
  let f : LOOConcentration.LocallyLipschitzDataFunction 0 0 r := ⟨
    fun D => abs (g.1 D - y), by
      intro D
      obtain ⟨U, hU, K, hK, hLip⟩ := g.2 D
      refine ⟨U, hU, K, hK, ?_⟩
      intro E hE F hF
      calc
        |abs (g.1 E - y) - abs (g.1 F - y)| ≤
            |(g.1 E - y) - (g.1 F - y)| :=
          abs_abs_sub_abs_le_abs_sub _ _
        _ = |g.1 E - g.1 F| := by congr 1; ring
        _ ≤ K * LOOConcentration.datasetNorm (E - F) := hLip E hE F hF⟩
  refine ⟨f, ?_, ?_⟩
  · intro D
    change abs (T (LOOConcentration.datasetToEuclidean D) - y) = _
    simp [T, Kh, LOOConcentration.datasetToEuclidean]
  · intro D
    have hquot : ∀ E : LOOConcentration.DataCarrier 0 0 r,
        |f.1 E - f.1 D| / LOOConcentration.datasetNorm (E - D) ≤
          |g.1 E - g.1 D| / LOOConcentration.datasetNorm (E - D) := by
      intro E
      have hnum : |f.1 E - f.1 D| ≤ |g.1 E - g.1 D| := by
        change |abs (g.1 E - y) - abs (g.1 D - y)| ≤ |g.1 E - g.1 D|
        have h := abs_abs_sub_abs_le_abs_sub (g.1 E - y) (g.1 D - y)
        simpa only [sub_sub_sub_cancel_right] using h
      exact div_le_div_of_nonneg_right hnum (Real.sqrt_nonneg _)
    have hlim := limsup_le_limsup
      (Filter.Eventually.of_forall hquot)
      (LOOConcentration.datasetSlope_cobounded f D)
      (LOOConcentration.datasetSlope_bounded g D)
    have hLossSlope : LOOConcentration.datasetLocalSlope f D ≤
        LOOConcentration.datasetLocalSlope g D := by
      simpa only [LOOConcentration.datasetLocalSlope] using hlim
    have hSmoothSlope : LOOConcentration.datasetLocalSlope g D =
        ‖fderiv ℝ T (LOOConcentration.datasetToEuclidean D)‖ :=
      LOOConcentration.datasetLocalSlope_smoothPullback_eq T hSmoothOne D
    have hDualNorm : ‖fderiv ℝ T (LOOConcentration.datasetToEuclidean D)‖ =
        ‖gradient T (LOOConcentration.datasetToEuclidean D)‖ := by
      rw [← toDual_gradient]
      exact (InnerProductSpace.toDual ℝ _).norm_map _
    have hGradient := hShared r x (LOOConcentration.datasetToEuclidean D)
    change ‖gradient T (LOOConcentration.datasetToEuclidean D)‖ ≤
      C / Real.sqrt (r + 1 : ℝ) +
        C * ‖LOOConcentration.datasetToEuclidean D‖ / (r + 1 : ℝ) at hGradient
    rw [← LOOConcentration.datasetNorm_eq_euclidean D] at hGradient
    calc
      LOOConcentration.datasetLocalSlope f D ≤
          LOOConcentration.datasetLocalSlope g D := hLossSlope
      _ = ‖fderiv ℝ T (LOOConcentration.datasetToEuclidean D)‖ := hSmoothSlope
      _ = ‖gradient T (LOOConcentration.datasetToEuclidean D)‖ := hDualNorm
      _ ≤ C / Real.sqrt (r + 1 : ℝ) +
            C * LOOConcentration.datasetNorm D / (r + 1 : ℝ) := hGradient

end LOOConcentration.Manuscript.Internal
