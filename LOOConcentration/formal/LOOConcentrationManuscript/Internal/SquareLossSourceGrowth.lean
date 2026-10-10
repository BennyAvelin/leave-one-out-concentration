import LOOConcentrationManuscript.Internal.LocalSlopeCompositionConsumer
import LOOConcentrationManuscript.Internal.EuclideanClipping
import LOOConcentration.Geometry.LocallyLipschitzDifferentiability

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal
open MeasureTheory

/-- The source estimator-growth and gradient premises yield the actual
squared-loss gradient bound. The fixed constant is explicit and independent
of the dataset and test response. -/
theorem square_loss_source_growth_gradient
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (T : EuclideanSpace ℝ ι → ℝ) (x : EuclideanSpace ℝ κ)
    (y A δ : ℝ) (hA : 0 ≤ A) (hδ : 0 ≤ δ)
    (hT : LocallyLipschitz T) (hGrowth : ∀ D, |T D| ≤ A * ‖x‖)
    (hGrad : ∀ᵐ D ∂(volume : Measure (EuclideanSpace ℝ ι)), ‖gradient T D‖ ≤ δ) :
    ∀ᵐ D ∂(volume : Measure (EuclideanSpace ℝ ι)),
      DifferentiableAt ℝ (fun E => (T E - y)^2) D ∧
        ‖gradient (fun E => (T E - y)^2) D‖ ≤
          (2 * (1 + A)) * δ * (|y| + ‖x‖) := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hι =>
    let _ := hι
    have hConst : (fun E : EuclideanSpace ℝ ι => (T E-y)^2) =
        (fun _ => (T 0-y)^2) := by
      funext E
      rw [Subsingleton.elim E 0]
    rw [hConst]
    filter_upwards with D
    refine ⟨differentiableAt_const _, ?_⟩
    rw [gradient_fun_const, norm_zero]
    positivity
  | inr hι =>
    let _ := hι
    have hAE := LOOConcentration.locallyLipschitz_ae_differentiableAt_euclidean T hT
    filter_upwards [hAE, hGrad] with D hDiff hBound
    have hSub := hDiff.hasFDerivAt.sub_const y
    have hPow := hSub.pow 2
    refine ⟨hPow.differentiableAt, ?_⟩
    have hDeriv : fderiv ℝ (fun E => (T E-y)^2) D =
        (2 * (T D-y)) • fderiv ℝ T D := by
      rw [hPow.fderiv]
      norm_num [smul_smul]
    have hChain : gradient (fun E => (T E-y)^2) D =
        (2 * (T D-y)) • gradient T D := by
      rw [gradient, hDeriv, map_smul]
      rfl
    have hResidual : |T D-y| ≤ |y| + A * ‖x‖ := by
      calc
        _ ≤ |T D| + |y| := abs_sub _ _
        _ ≤ A * ‖x‖ + |y| := add_le_add (hGrowth D) le_rfl
        _ = |y| + A * ‖x‖ := by ring
    have hCoeff : |y| + A * ‖x‖ ≤ (1 + A) * (|y| + ‖x‖) := by
      calc
        _ ≤ (1+A) * |y| + (1+A) * ‖x‖ := add_le_add
          (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (by linarith : (1:ℝ) ≤ 1+A) (abs_nonneg y))
          (mul_le_mul_of_nonneg_right (by linarith : A ≤ 1+A) (norm_nonneg x))
        _ = _ := by ring
    calc
      _ = 2 * |T D-y| * ‖gradient T D‖ := by
        rw [hChain, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2:ℝ))]
      _ ≤ (2 * (|y| + A * ‖x‖)) * δ := mul_le_mul
        (mul_le_mul_of_nonneg_left hResidual (by norm_num)) hBound
        (norm_nonneg _) (by positivity)
      _ ≤ (2 * ((1+A) * (|y| + ‖x‖))) * δ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hCoeff (by norm_num)) hδ
      _ = (2 * (1+A)) * δ * (|y| + ‖x‖) := by ring

/-- A literal clipped empirical mean consumes the source growth theorem;
the required growth and gradient bounds are proved inside this consumer. -/
theorem clipped_empiricalMean_square_loss_source_consumer
    (b : {t : ℝ // 0 ≤ t}) (r : ℕ) (y : ℝ) :
    let clip := fun D : EuclideanSpace ℝ (Fin (r+1)) =>
      WithLp.toLp 2 (fun i => max (min (D i) b.val) (-b.val))
    ∀ᵐ D ∂(volume : Measure (EuclideanSpace ℝ (Fin (r+1)))),
      DifferentiableAt ℝ (fun E => (empiricalMean r (clip E)-y)^2) D ∧
        ‖gradient (fun E => (empiricalMean r (clip E)-y)^2) D‖ ≤
          (2 * (1 + b.val)) * (Real.sqrt ((r+1 : ℕ) : ℝ))⁻¹ * (|y|+1) := by
  intro clip
  let T := fun D => empiricalMean r (clip D)
  let K : NNReal := Real.toNNReal (Real.sqrt ((r+1 : ℕ) : ℝ))⁻¹
  have hRoot : 0 < Real.sqrt ((r+1 : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
  have hK : (K : ℝ) = (Real.sqrt ((r+1 : ℕ) : ℝ))⁻¹ :=
    Real.coe_toNNReal _ (inv_nonneg.2 hRoot.le)
  have hClip := euclideanClipping_lipschitz_and_norm (Fin (r+1)) b.val b.property
  have hLip : LipschitzWith K T := by
    simpa only [mul_one, K, T, Function.comp_def] using (empiricalMean_lipschitz r).comp hClip.1
  have hMeanZero : empiricalMean r (0 : EuclideanSpace ℝ (Fin (r+1))) = 0 := by
    simp [empiricalMean]
  have hGrowth : ∀ D, |T D| ≤ b.val := by
    intro D
    have hm := (empiricalMean_lipschitz r).norm_sub_le (clip D) 0
    have hm' : |T D| ≤ (K : ℝ) * ‖clip D‖ := by
      simpa only [hMeanZero, sub_zero, Real.norm_eq_abs] using hm
    calc
      _ ≤ (K : ℝ) * ‖clip D‖ := hm'
      _ ≤ (K : ℝ) * (b.val * Real.sqrt ((r+1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left (by simpa only [Fintype.card_fin] using hClip.2 D) (NNReal.coe_nonneg K)
      _ = b.val := by rw [hK]; field_simp [hRoot.ne']
  have hGrad : ∀ᵐ D ∂(volume : Measure (EuclideanSpace ℝ (Fin (r+1)))),
      ‖gradient T D‖ ≤ (Real.sqrt ((r+1 : ℕ) : ℝ))⁻¹ := by
    filter_upwards with D
    simpa only [hK] using (lipschitz_euclidean_slope_and_gradient_le r T K hLip D).2
  let x : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 (fun _ => 1)
  have hx : ‖x‖ = 1 := by simp [x, EuclideanSpace.norm_eq]
  simpa only [hx] using square_loss_source_growth_gradient T x y b.val
    (Real.sqrt ((r+1 : ℕ) : ℝ))⁻¹ b.property (inv_nonneg.2 hRoot.le)
      hLip.locallyLipschitz (by intro D; simpa only [hx, mul_one] using hGrowth D) hGrad

end LOOConcentration.Manuscript.Internal
