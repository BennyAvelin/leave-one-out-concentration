import LOOConcentrationManuscript.Internal.GaussianKernelAbsoluteLossAmbientGradientConsumer
import LOOConcentrationManuscript.Internal.GaussianKernelHeldoutBiasConsumer
import LOOConcentrationManuscript.Internal.GaussianKernelExpectedLossAmbientGradientConsumer
import LOOConcentrationManuscript.Internal.IIDResponseAbsoluteMean
import LOOConcentrationRevision.Frozen.Definitions.StandingAssumption

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

/-- The complete frozen standing assumption for the literal Gaussian stabilized
predictor and absolute loss. Constants are fixed before every sample size. -/
theorem gaussianKernel_actual_complete_standing
    (μ : Measure (LOOConcentration.Observation 1 1)) [IsProbabilityMeasure μ]
    (hSecond : Integrable LOOConcentration.observationNormSq μ)
    (hLSI : LOOConcentration.Revision.observationLogSobolevConstant μ < ⊤)
    (h δ : ℝ) (hh : 0 < h) (hδ : 0 < δ) :
      let Kh := fun t : ℝ => gaussianPDFReal 0 1 (t/h)/h
      let T : ∀ r : ℕ, LOOConcentration.Estimator 1 1 (r+1) := fun r D =>
        { toFun := fun x => fun _ =>
            (∑ i : Fin (r+1), Kh (x 0-(D i).1 0)*(D i).2 0)/
              ((∑ i : Fin (r+1), Kh (x 0-(D i).1 0))+(r+1 : ℝ)*δ)
          continuous_toFun := by
            apply continuous_pi
            intro _
            have hKh : ∀ t, 0 ≤ Kh t := fun t =>
              div_nonneg (gaussianPDFReal_nonneg 0 1 (t/h)) hh.le
            have hDen (x : LOOConcentration.Features 1) :
                (∑ i : Fin (r+1), Kh (x 0-(D i).1 0))+(r+1 : ℝ)*δ ≠ 0 := by
              exact ne_of_gt (add_pos_of_nonneg_of_pos
                (Finset.sum_nonneg (fun i _ => hKh _)) (by positivity))
            have hCont : Continuous Kh :=
              (gaussianKernel_normalization_and_bounds.1.continuous.comp
                (continuous_id.div_const h)).div_const h
            have hAtom (i : Fin (r+1)) : Continuous
                (fun x : LOOConcentration.Features 1 => Kh (x 0-(D i).1 0)) :=
              hCont.comp ((continuous_apply 0).sub continuous_const)
            apply Continuous.div
              (continuous_finsetSum _ (fun i _ => (hAtom i).mul continuous_const))
              ((continuous_finsetSum _ (fun i _ => hAtom i)).add continuous_const) hDen }
      let L := fun u v : LOOConcentration.Responses 1 => |u 0-v 0|
      ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, 0 ≤ B ∧ ∃ M : ℝ, 0 < M ∧ ∀ n : ℕ,
        LOOConcentration.Revision.StandingAssumption (n := n) μ T L
          (fun N _ => C/Real.sqrt (N : ℝ)) (fun N _ => C/(N : ℝ))
          (fun N => B/(N : ℝ)) M 0 := by
  intro Kh T L
  obtain ⟨C,hC,hData⟩ := gaussianKernel_actual_observation_loss_gradient_fields h δ hh hδ
  obtain ⟨B,hB,hBias⟩ := gaussianKernel_actual_heldout_bias_uniform_rate μ hSecond h δ hh hδ
  obtain ⟨M,hM,hMean⟩ := gaussianKernel_actual_frozen_meanLoss_regularity_fields μ hSecond h δ hh hδ
  refine ⟨C,hC,B,hB,M,hM,?_⟩
  intro n
  obtain ⟨hFin,hMeanLocal,hMeanGradient⟩ := hMean n
  have hAbsY := (iidResponse_full_and_deleted_absolute_mean μ hSecond).1
  have hZero (r : ℕ) (z : LOOConcentration.Observation 1 1) :
      LOOConcentration.fittedLoss (T r) L 0 z = |z.2 0| := by
    simp [LOOConcentration.fittedLoss,T,L]
  have hZeroInt (r : ℕ) : Integrable
      (fun z => LOOConcentration.fittedLoss (T r) L 0 z) μ := by
    simpa only [hZero] using hAbsY
  have hN₁ : Tendsto (fun r : ℕ => (r : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hN₂ : Tendsto (fun r : ℕ => (r : ℝ)+2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hInv₁ := tendsto_inv_atTop_zero.comp hN₁
  have hInv₂ := tendsto_inv_atTop_zero.comp hN₂
  have hInvSqrt := tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hN₁)
  have hStable : LOOConcentration.Revision.Stable μ hLSI T L
      (fun N _ => C/Real.sqrt (N : ℝ)) (fun N _ => C/(N : ℝ))
      (fun N => B/(N : ℝ)) := by
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
      have hKhCont : Continuous Kh :=
        (gaussianKernel_normalization_and_bounds.1.continuous.comp
          (continuous_id.div_const h)).div_const h
      have hKhNonneg : ∀ t, 0 ≤ Kh t := fun t =>
        div_nonneg (gaussianPDFReal_nonneg 0 1 (t/h)) hh.le
      have hNum : Continuous (fun p : (Fin (r+1) → LOOConcentration.Observation 1 1) ×
          LOOConcentration.Observation 1 1 =>
          ∑ j : Fin (r+1), Kh (p.2.1 0-(p.1 j).1 0)*(p.1 j).2 0) :=
        continuous_finsetSum Finset.univ (fun j _ =>
          (hKhCont.comp (by fun_prop)).mul (by fun_prop))
      have hDen : Continuous (fun p : (Fin (r+1) → LOOConcentration.Observation 1 1) ×
          LOOConcentration.Observation 1 1 =>
          (∑ j : Fin (r+1), Kh (p.2.1 0-(p.1 j).1 0))+(r+1 : ℝ)*δ) :=
        (continuous_finsetSum Finset.univ (fun j _ => hKhCont.comp (by fun_prop))).add continuous_const
      have hDenPos (p : (Fin (r+1) → LOOConcentration.Observation 1 1) ×
          LOOConcentration.Observation 1 1) :
          0 < (∑ j : Fin (r+1), Kh (p.2.1 0-(p.1 j).1 0))+(r+1 : ℝ)*δ :=
        add_pos_of_nonneg_of_pos (Finset.sum_nonneg (fun j _ => hKhNonneg _))
          (mul_pos (by positivity) hδ)
      exact (continuous_abs.comp ((hNum.div hDen (fun p => (hDenPos p).ne')).sub
        (by fun_prop))).measurable
    · intro r z; exact div_nonneg hC.le (Real.sqrt_nonneg _)
    · intro r z; exact div_nonneg hC.le (by positivity)
    · intro r; exact div_nonneg hB (by positivity)
    · exact Eventually.of_forall fun _ => by
        simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,div_eq_mul_inv,mul_zero,Function.comp_def] using hInvSqrt.const_mul C
    · exact Eventually.of_forall fun _ => by
        simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,div_eq_mul_inv,mul_zero,Function.comp_def] using hInv₁.const_mul C
    · simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,div_eq_mul_inv,mul_zero,Function.comp_def] using hInv₂.const_mul B
    · intro r
      exact Eventually.of_forall fun z => (hData r z).1
    · intro r
      apply Eventually.of_forall
      intro z
      filter_upwards [(hData r z).2] with E hField
      refine ⟨hField.1,?_⟩
      calc
        _ ≤ C/Real.sqrt (r+1 : ℝ)+C*‖E‖/(r+1 : ℝ) := hField.2
        _ = _ := by simp only [Nat.cast_add,Nat.cast_one]; ring
    · intro r i; exact (hBias r i).1
    · intro r
      simpa only [LOOConcentration.fittedLoss,T,L,ContinuousMap.coe_mk,
        Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,add_assoc,one_add_one_eq_two]
        using (hBias r 0).2.2.1
    · intro r i
      simpa only [LOOConcentration.fittedLoss,T,L,ContinuousMap.coe_mk,
        Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,add_assoc,one_add_one_eq_two]
        using (hBias r i).2.2.2.2
  refine {
    lsi := hLSI
    second_moment := hSecond
    stable := hStable
    delta₁_deleted_integrable := integrable_const _
    delta₂_deleted_integrable := integrable_const _
    delta₁_full_integrable := integrable_const _
    delta₂_full_integrable := integrable_const _
    zero_deleted_integrable := hZeroInt n
    zero_full_integrable := hZeroInt (n+1)
    c_nonneg := hM.le
    d_nonneg := le_rfl
    mean_integrable := hFin
    mean_locallyLipschitz := hMeanLocal
    mean_gradient := ?_ }
  filter_upwards [hMeanGradient] with E hField
  exact ⟨hField.1,by simpa only [zero_mul,add_zero] using hField.2⟩

end LOOConcentration.Manuscript.Internal
