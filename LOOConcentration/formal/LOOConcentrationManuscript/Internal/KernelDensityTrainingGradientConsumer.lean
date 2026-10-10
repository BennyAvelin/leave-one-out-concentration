import LOOConcentrationManuscript.Internal.KernelDensityTrainingGradient
import LOOConcentration.Geometry.NormTransport
import LOOConcentration.Frozen.Foundations.FittedLoss
import LOOConcentrationRevision.Frozen.Definitions.DatasetOfEuclidean
import Mathlib.Analysis.Calculus.Gradient.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LOOConcentration.Manuscript.Internal

/-- The literal zero-response KDE estimator's actual absolute fitted loss is
locally Lipschitz and everywhere differentiable on the whole paired data
carrier, with the source `M/(h²√N)` gradient bound. -/
theorem genericKDE_actual_absolute_training_loss_gradient
    (K : ℝ → ℝ) (hK : ContDiff ℝ 1 K)
    (hK_nonneg : ∀ x : ℝ, 0 ≤ K x) (M : ℝ)
    (hM : ∀ t : ℝ, |deriv K t| ≤ M) (h : ℝ) (hh : 0 < h) :
    ∀ (r : ℕ) (z : LOOConcentration.Observation 1 1),
      let T : LOOConcentration.Estimator 1 1 (r + 1) := fun D =>
        { toFun := fun x => WithLp.toLp (2 : ENNReal) (fun _ : Fin 1 =>
            (r + 1 : ℝ)⁻¹ *
              ∑ j : Fin (r + 1), K ((x 0 - (D j).1 0) / h) / h)
          continuous_toFun := by
            have hKC : Continuous K := hK.continuous
            fun_prop }
      let actualLoss : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1)) → ℝ :=
        fun E => LOOConcentration.fittedLoss T (fun a _y => |a 0|)
          (LOOConcentration.Revision.datasetOfEuclidean E) z
      LocallyLipschitz actualLoss ∧
        ∀ E : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1)),
          DifferentiableAt ℝ actualLoss E ∧
          ‖gradient actualLoss E‖ ≤ M /
            (h ^ 2 * Real.sqrt (r + 1 : ℝ)) := by
  classical
  have hM_nonneg : 0 ≤ M := (abs_nonneg (deriv K 0)).trans (hM 0)
  intro r z
  let T : LOOConcentration.Estimator 1 1 (r + 1) := fun D =>
    { toFun := fun x => WithLp.toLp (2 : ENNReal) (fun _ : Fin 1 =>
        (r + 1 : ℝ)⁻¹ * ∑ j : Fin (r + 1), K ((x 0 - (D j).1 0) / h) / h)
      continuous_toFun := by
        have hKC : Continuous K := hK.continuous
        fun_prop }
  let actualLoss : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1)) → ℝ :=
    fun E => LOOConcentration.fittedLoss T (fun a _y => |a 0|)
      (LOOConcentration.Revision.datasetOfEuclidean E) z
  change LocallyLipschitz actualLoss ∧
    ∀ E : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1)),
      DifferentiableAt ℝ actualLoss E ∧
      ‖gradient actualLoss E‖ ≤ M / (h ^ 2 * Real.sqrt (r + 1 : ℝ))
  have hRaw := genericKDE_actual_training_regular K hK M hM h hh r (z.1 0)
  rcases hRaw with ⟨hRawContDiff, hRawLip⟩
  let raw : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1)) → ℝ := fun E =>
    (r + 1 : ℝ)⁻¹ *
      ∑ j : Fin (r + 1), K ((z.1 0 - E (j, Sum.inl 0)) / h) / h
  have hRawNonneg (E : EuclideanSpace ℝ (Fin (r + 1) × (Fin 1 ⊕ Fin 1))) : 0 ≤ raw E := by
    dsimp [raw]
    apply mul_nonneg
    · positivity
    · exact Finset.sum_nonneg fun j _ => div_nonneg (hK_nonneg _) hh.le
  have hLossEq : actualLoss = raw := by
    funext E
    simp only [actualLoss, LOOConcentration.fittedLoss, T,
      LOOConcentration.Revision.datasetOfEuclidean, ContinuousMap.coe_mk]
    exact abs_of_nonneg (hRawNonneg E)
  have hB_nonneg : 0 ≤ M / (h ^ 2 * Real.sqrt (r + 1 : ℝ)) :=
    div_nonneg hM_nonneg (mul_nonneg (sq_nonneg h) (Real.sqrt_nonneg _))
  let B : NNReal := ⟨M / (h ^ 2 * Real.sqrt (r + 1 : ℝ)), hB_nonneg⟩
  have hLip : LipschitzWith B actualLoss := by
    apply LipschitzWith.of_dist_le_mul
    intro E F
    rw [hLossEq]
    change |raw E - raw F| ≤
      M / (h ^ 2 * Real.sqrt (r + 1 : ℝ)) * ‖E - F‖
    simpa [raw] using hRawLip E F
  refine ⟨hLip.locallyLipschitz, ?_⟩
  intro E
  constructor
  · rw [hLossEq]
    exact hRawContDiff.differentiable (by norm_num) E
  · have hFderiv := norm_fderiv_le_of_lipschitz ℝ (x₀ := E) hLip
    have hDualNorm : ‖fderiv ℝ actualLoss E‖ = ‖gradient actualLoss E‖ := by
      rw [← toDual_gradient]
      exact (InnerProductSpace.toDual ℝ _).norm_map _
    calc
      ‖gradient actualLoss E‖ = ‖fderiv ℝ actualLoss E‖ := hDualNorm.symm
      _ ≤ B := hFderiv
      _ = M / (h ^ 2 * Real.sqrt (r + 1 : ℝ)) := rfl

end LOOConcentration.Manuscript.Internal
