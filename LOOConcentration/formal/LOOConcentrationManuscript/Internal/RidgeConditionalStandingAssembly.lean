import LOOConcentrationManuscript.Internal.RidgeSourceJointRegularityConsumer
import LOOConcentrationManuscript.Internal.RidgeExpectedLossQueryConsumer
import LOOConcentrationManuscript.Internal.RidgeExpectedDeleteBiasConsumer
import LOOConcentrationManuscript.Internal.NativeLSIFourthMoment
import LOOConcentrationManuscript.Internal.IIDResponseAbsoluteMean
import LOOConcentrationRevision.Frozen.Definitions.StandingAssumption

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal
open MeasureTheory Filter
open scoped Topology ENNReal

/-- Conditional internal assembly, with its sole unproved source dependency
explicitly named as the ordered expected-bias bound. This is not a source-node
closure. The complete source application must produce this premise internally. -/
theorem ridge_actual_complete_standing_of_ordered_bias
    (μ : Measure (LOOConcentration.Observation 1 1)) [IsProbabilityMeasure μ]
    (hSecond : Integrable LOOConcentration.observationNormSq μ)
    (hLSI : LOOConcentration.Revision.observationLogSobolevConstant μ < ⊤)
    (b δ : {t : ℝ // 0 < t}) (B : ℝ) (hB : 0 ≤ B)
    (hBias : ∀ n (i : Fin (n + 2)),
      |(∫ D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (n + 2),
          LOOConcentration.fittedLoss
            (LOOConcentration.Manuscript.stabilizedLinearEstimator b δ n)
            (fun u v : Fin 1 → ℝ => |u 0 - v 0|)
            (LOOConcentration.deleteAt D i) (D i)
            ∂Measure.pi (fun _ : Fin (n + 2) => μ)) -
        (∫ p : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (n + 2) ×
            LOOConcentration.Observation 1 1,
          LOOConcentration.fittedLoss
            (LOOConcentration.Manuscript.stabilizedLinearEstimator b δ (n + 1))
            (fun u v : Fin 1 → ℝ => |u 0 - v 0|) p.1 p.2
            ∂(Measure.pi (fun _ : Fin (n + 2) => μ)).prod μ)| ≤ B / (n + 2 : ℝ)) :
    let T := fun r => LOOConcentration.Manuscript.stabilizedLinearEstimator b δ r
    let L := fun u v : Fin 1 → ℝ => |u 0 - v 0|
    ∃ C : ℝ, 0 < C ∧ ∃ M : ℝ, 0 < M ∧ ∀ n : ℕ,
      LOOConcentration.Revision.StandingAssumption (n := n) μ T L
        (fun N z => C * (1 + |z.1 0|) / Real.sqrt (N : ℝ))
        (fun N _ => C / (N : ℝ)) (fun N => B / (N : ℝ)) M 0 := by
  intro T L
  obtain ⟨C, hC, hData⟩ := stabilizedLinearEstimator_actual_source_joint_regularity b δ
  let M := Real.sqrt (1 + b.val ^ 2 / (4 * δ.val))
  have hM : 0 < M := Real.sqrt_pos.2 (by
    have hFrac := div_nonneg (sq_nonneg b.val)
      (le_of_lt (mul_pos (by norm_num : (0 : ℝ) < 4) δ.property))
    linarith)
  have hY1 := (iidResponse_full_and_deleted_absolute_mean μ hSecond).1
  have hX4 := (observation_nativeLSI_feature_fourth_moment μ hLSI hSecond).2
  have hMom := ridge_actual_first_moment_feature_sq_source μ hX4 hY1
  have hDeltaInt (N : ℕ) : Integrable
      (fun z : LOOConcentration.Observation 1 1 =>
        C * (1 + |z.1 0|) / Real.sqrt (N : ℝ)) μ :=
    ((integrable_const (1 : ℝ)).add hMom.1).const_mul C |>.div_const _
  have hN₁ : Tendsto (fun r : ℕ => (r : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hN₂ : Tendsto (fun r : ℕ => (r : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hInv₁ := tendsto_inv_atTop_zero.comp hN₁
  have hInv₂ := tendsto_inv_atTop_zero.comp hN₂
  have hInvSqrt := tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp
    hN₁)
  refine ⟨C, hC, M, hM, ?_⟩
  intro n
  have fields := LOOConcentrationManuscript.Internal.stabilizedLinearEstimator_expected_absoluteLoss_query_fields μ hSecond b δ n
  have hFin := fun z : LOOConcentration.Observation 1 1 => fields.1 z
  have hMean := LOOConcentrationManuscript.Internal.stabilizedLinearEstimator_actual_meanFittedLoss_regularity μ hSecond b δ n
  have hStable : LOOConcentration.Revision.Stable μ hLSI T L
      (fun N z => C * (1 + |z.1 0|) / Real.sqrt (N : ℝ))
      (fun N _ => C / (N : ℝ)) (fun N => B / (N : ℝ)) := by
    refine {
      measurable_loss := ?_
      delta₁_nonneg := ?_
      delta₂_nonneg := ?_
      delta₃_nonneg := ?_
      delta₁_tendsto := ?_
      delta₂_tendsto := ?_
      delta₃_tendsto := ?_
      locallyLipschitz_loss := ?_
      gradient_loss := ?_
      integrable_deleted := ?_
      integrable_full := ?_
      bias := ?_ }
    · intro r
      have hCont : Continuous
          (fun p : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) ×
            LOOConcentration.Observation 1 1 => LOOConcentration.fittedLoss (T r) L p.1 p.2) := by
        unfold LOOConcentration.fittedLoss
        dsimp [T, L, LOOConcentration.Manuscript.stabilizedLinearEstimator]
        apply continuous_abs.comp
        apply Continuous.sub
        · apply Continuous.add
          · fun_prop
          · apply Continuous.mul
            · apply Continuous.div
              · fun_prop
              · fun_prop
              · intro p
                exact ne_of_gt (add_pos_of_nonneg_of_pos
                  (mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
                  δ.property)
            · fun_prop
        · fun_prop
      exact hCont.measurable
    · intro r z
      exact div_nonneg (mul_nonneg hC.le (by positivity)) (Real.sqrt_nonneg _)
    · intro r z; exact div_nonneg hC.le (by positivity)
    · intro r; exact div_nonneg hB (by positivity)
    · exact Eventually.of_forall fun z => by
        simpa only [Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_zero, Function.comp_def]
          using hInvSqrt.const_mul (C * (1 + |z.1 0|))
    · exact Eventually.of_forall fun _ => by
        simpa only [Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_zero, Function.comp_def]
          using hInv₁.const_mul C
    · simpa only [Nat.cast_add, Nat.cast_ofNat, div_eq_mul_inv, mul_zero, Function.comp_def]
        using hInv₂.const_mul B
    · intro r
      exact Eventually.of_forall fun z => (hData r z).2.2.1
    · intro r
      apply Eventually.of_forall
      intro z
      filter_upwards [(hData r z).2.2.2.1] with E hField
      refine ⟨hField.2.2.1, ?_⟩
      have hBound : ‖gradient (fun y => LOOConcentration.fittedLoss (T r) L
          (LOOConcentration.Revision.datasetOfEuclidean y) z) E‖ ≤
          C * (1 + |z.1 0|) / Real.sqrt ((r + 1 : ℕ) : ℝ) +
            C * ‖E‖ / ((r + 1 : ℕ) : ℝ) := hField.2.2.2.2.2
      simpa only [Nat.cast_add, Nat.cast_one, div_mul_eq_mul_div] using hBound
    · intro r i
      exact (ridge_actual_ordered_delete_loss_consumer μ hY1 hX4 b δ r).2.2 i |>.1
    · intro r
      exact (ridge_actual_ordered_delete_loss_consumer μ hY1 hX4 b δ r).1
    · intro r i
      simpa only [T, L, Nat.cast_add, Nat.cast_ofNat] using hBias r i
  refine {
    lsi := hLSI
    second_moment := hSecond
    stable := hStable
    delta₁_deleted_integrable := hDeltaInt (n + 1)
    delta₂_deleted_integrable := integrable_const _
    delta₁_full_integrable := hDeltaInt (n + 2)
    delta₂_full_integrable := integrable_const _
    zero_deleted_integrable := ?_
    zero_full_integrable := ?_
    c_nonneg := hM.le
    d_nonneg := le_rfl
    mean_integrable := hFin
    mean_locallyLipschitz := hMean.2.2.2.1
    mean_gradient := ?_ }
  · exact fields.2.2.2.1
  · exact (LOOConcentrationManuscript.Internal.stabilizedLinearEstimator_expected_absoluteLoss_query_fields μ hSecond b δ (n + 1)).2.2.2.1
  · filter_upwards [hMean.2.2.2.2] with E hField
    exact ⟨hField.1, by simpa only [M, zero_mul, add_zero] using hField.2⟩

end LOOConcentration.Manuscript.Internal
