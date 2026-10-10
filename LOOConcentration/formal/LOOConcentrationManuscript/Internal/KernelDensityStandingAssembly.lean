import LOOConcentrationManuscript.Internal.KernelDensityTrainingGradientConsumer
import LOOConcentrationManuscript.Internal.KernelDensityHeldoutZeroBiasConsumer
import LOOConcentrationManuscript.Internal.KernelDensityQueryRegularityConsumer
import LOOConcentrationManuscript.Internal.KernelDensityZeroResponseEmbeddingConsumer
import LOOConcentration.Geometry.LocallyLipschitzDifferentiability
import LOOConcentrationRevision.Frozen.Definitions.StandingAssumption
import LOOConcentrationRevision.Frozen.Definitions.MeanFittedLoss
import LOOConcentrationManuscript.Frozen.Definitions.KernelDensityEstimator
import Mathlib.Analysis.Calculus.Gradient.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LOOConcentration.Manuscript.Internal

open MeasureTheory Filter
open scoped Topology ENNReal

private noncomputable def kdeActualRaw (K : ℝ → ℝ) (h : {t : ℝ // 0 < t}) (r : ℕ)
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1))
    (t : ℝ) : ℝ :=
  (r + 1 : ℝ)⁻¹ * ∑ j : Fin (r + 1), K ((t - (D j).1 0) / h.val) / h.val

private theorem kdeActual_estimator_apply
    (K : {K : ℝ → ℝ // ContDiff ℝ 1 K ∧ (∀ x, 0 ≤ K x) ∧
      (∃ B : ℝ, ∀ x, |K x| ≤ B) ∧ (∫ x : ℝ, K x) = 1 ∧
      (∃ B : ℝ, ∀ x, |deriv K x| ≤ B)})
    (h : {t : ℝ // 0 < t}) (r : ℕ)
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1))
    (x : LOOConcentration.Features 1) :
    ((LOOConcentration.Manuscript.kernelDensityEstimator K h r D) x) 0 =
      kdeActualRaw K.val h r D (x 0) := by
  simp only [LOOConcentration.Manuscript.kernelDensityEstimator,
    ContinuousMap.coe_mk, kdeActualRaw]
  have hn : (r + 1 : ℝ) ≠ 0 := by positivity
  have hh : h.val ≠ 0 := h.property.ne'
  calc
    _ = ((r + 1 : ℝ)⁻¹ * h.val⁻¹) *
        ∑ j : Fin (r + 1), K.val ((x 0 - (D j).1 0) / h.val) := by
      congr 1
      field_simp [hn, hh]
    _ = (r + 1 : ℝ)⁻¹ *
        (h.val⁻¹ * ∑ j : Fin (r + 1),
          K.val ((x 0 - (D j).1 0) / h.val)) := by ring
    _ = (r + 1 : ℝ)⁻¹ *
        ∑ j : Fin (r + 1), h.val⁻¹ *
          K.val ((x 0 - (D j).1 0) / h.val) := by rw [Finset.mul_sum]
    _ = (r + 1 : ℝ)⁻¹ *
        ∑ j : Fin (r + 1),
          K.val ((x 0 - (D j).1 0) / h.val) / h.val := by
      apply congrArg ((r + 1 : ℝ)⁻¹ * ·)
      apply Finset.sum_congr rfl
      intro j hj
      rw [div_eq_mul_inv]
      ring

private noncomputable def kdeActual_rawEstimator
    (K : {K : ℝ → ℝ // ContDiff ℝ 1 K ∧ (∀ x, 0 ≤ K x) ∧
      (∃ B : ℝ, ∀ x, |K x| ≤ B) ∧ (∫ x : ℝ, K x) = 1 ∧
      (∃ B : ℝ, ∀ x, |deriv K x| ≤ B)})
    (h : {t : ℝ // 0 < t}) (r : ℕ) :
    LOOConcentration.Estimator 1 1 (r + 1) := fun D =>
  { toFun := fun x => WithLp.toLp (2 : ENNReal) (fun _ : Fin 1 =>
      kdeActualRaw K.val h r D (x 0))
    continuous_toFun := by
      have hKC : Continuous K.val := K.property.1.continuous
      unfold kdeActualRaw
      fun_prop }

private theorem kdeActual_estimator_eq_raw
    (K : {K : ℝ → ℝ // ContDiff ℝ 1 K ∧ (∀ x, 0 ≤ K x) ∧
      (∃ B : ℝ, ∀ x, |K x| ≤ B) ∧ (∫ x : ℝ, K x) = 1 ∧
      (∃ B : ℝ, ∀ x, |deriv K x| ≤ B)})
    (h : {t : ℝ // 0 < t}) (r : ℕ) :
    LOOConcentration.Manuscript.kernelDensityEstimator K h r =
      kdeActual_rawEstimator K h r := by
  funext D
  ext x i
  fin_cases i
  exact kdeActual_estimator_apply K h r D x

private theorem kdeActual_loss_eq_raw
    (K : {K : ℝ → ℝ // ContDiff ℝ 1 K ∧ (∀ x, 0 ≤ K x) ∧
      (∃ B : ℝ, ∀ x, |K x| ≤ B) ∧ (∫ x : ℝ, K x) = 1 ∧
      (∃ B : ℝ, ∀ x, |deriv K x| ≤ B)})
    (h : {t : ℝ // 0 < t}) (r : ℕ)
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1))
    (z : LOOConcentration.Observation 1 1) :
    LOOConcentration.fittedLoss (LOOConcentration.Manuscript.kernelDensityEstimator K h r)
      (fun a _ => |a 0|) D z = |kdeActualRaw K.val h r D (z.1 0)| := by
  simp only [LOOConcentration.fittedLoss, kdeActual_estimator_apply, kdeActualRaw]

private theorem kdeActual_raw_nonneg
    (K : {K : ℝ → ℝ // ContDiff ℝ 1 K ∧ (∀ x, 0 ≤ K x) ∧
      (∃ B : ℝ, ∀ x, |K x| ≤ B) ∧ (∫ x : ℝ, K x) = 1 ∧
      (∃ B : ℝ, ∀ x, |deriv K x| ≤ B)})
    (h : {t : ℝ // 0 < t}) (r : ℕ)
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1))
    (t : ℝ) : 0 ≤ kdeActualRaw K.val h r D t := by
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro j hj
  exact div_nonneg (K.property.2.1 _) h.property.le

private theorem kdeActual_raw_le_bound
    (K : {K : ℝ → ℝ // ContDiff ℝ 1 K ∧ (∀ x, 0 ≤ K x) ∧
      (∃ B : ℝ, ∀ x, |K x| ≤ B) ∧ (∫ x : ℝ, K x) = 1 ∧
      (∃ B : ℝ, ∀ x, |deriv K x| ≤ B)})
    (h : {t : ℝ // 0 < t}) (C : ℝ) (hC : ∀ t, |K.val t| ≤ C)
    (r : ℕ) (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1))
    (t : ℝ) : kdeActualRaw K.val h r D t ≤ C / h.val := by
  have hh : 0 < h.val := h.property
  have hterm (j : Fin (r + 1)) :
      K.val ((t - (D j).1 0) / h.val) / h.val ≤ C / h.val := by
    apply div_le_div_of_nonneg_right _ hh.le
    exact (le_abs_self _).trans (hC _)
  have hsum :
      (∑ j : Fin (r + 1), K.val ((t - (D j).1 0) / h.val) / h.val) ≤
        (r + 1 : ℝ) * (C / h.val) := by
    calc
      _ ≤ ∑ _j : Fin (r + 1), C / h.val := Finset.sum_le_sum fun j _ => hterm j
      _ = _ := by simp
  dsimp [kdeActualRaw]
  calc
    _ ≤ (r + 1 : ℝ)⁻¹ * ((r + 1 : ℝ) * (C / h.val)) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (by positivity))
    _ = C / h.val := by
      have hn : (r + 1 : ℝ) ≠ 0 := by positivity
      field_simp [hn]

private theorem kdeActual_loss_eq_raw_nonneg
    (K : {K : ℝ → ℝ // ContDiff ℝ 1 K ∧ (∀ x, 0 ≤ K x) ∧
      (∃ B : ℝ, ∀ x, |K x| ≤ B) ∧ (∫ x : ℝ, K x) = 1 ∧
      (∃ B : ℝ, ∀ x, |deriv K x| ≤ B)})
    (h : {t : ℝ // 0 < t}) (r : ℕ)
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1))
    (z : LOOConcentration.Observation 1 1) :
    LOOConcentration.fittedLoss (LOOConcentration.Manuscript.kernelDensityEstimator K h r)
      (fun a _ => |a 0|) D z = kdeActualRaw K.val h r D (z.1 0) := by
  rw [kdeActual_loss_eq_raw]
  exact abs_of_nonneg (kdeActual_raw_nonneg K h r D (z.1 0))

private theorem kdeActual_mean_regularity
    (μ : Measure (LOOConcentration.Observation 1 1)) [IsProbabilityMeasure μ]
    (K : {K : ℝ → ℝ // ContDiff ℝ 1 K ∧ (∀ x, 0 ≤ K x) ∧
      (∃ B : ℝ, ∀ x, |K x| ≤ B) ∧ (∫ x : ℝ, K x) = 1 ∧
      (∃ B : ℝ, ∀ x, |deriv K x| ≤ B)})
    (h : {t : ℝ // 0 < t}) (M : ℝ) (hM : ∀ t, |deriv K.val t| ≤ M)
    (hM_nonneg : 0 ≤ M) (C : ℝ) (hC : ∀ t, |K.val t| ≤ C) :
    ∀ r : ℕ,
      let P := Measure.pi (fun _ : Fin (r + 1) => μ)
      let T := fun s : ℕ => LOOConcentration.Manuscript.kernelDensityEstimator K h s
      let L := fun a _ : LOOConcentration.Responses 1 => |a 0|
      ∃ hFin : ∀ z : LOOConcentration.Observation 1 1,
        Integrable (fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) =>
          LOOConcentration.fittedLoss (T r) L D z) P,
        let G := fun x : EuclideanSpace ℝ (LOOConcentration.ObservationCoordinate 1 1) =>
          LOOConcentration.Revision.meanFittedLoss μ (T r) L
            (LOOConcentration.Revision.observationOfEuclidean x)
            (hFin (LOOConcentration.Revision.observationOfEuclidean x))
        LipschitzWith (Real.toNNReal (M / h.val ^ 2)) G ∧
          ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ
              (LOOConcentration.ObservationCoordinate 1 1))),
            DifferentiableAt ℝ G x ∧ ‖gradient G x‖ ≤ M / h.val ^ 2 := by
  intro r P T L
  have hC_nonneg : 0 ≤ C := (abs_nonneg (K.val 0)).trans (hC 0)
  have hh : 0 < h.val := h.property
  have hc_nonneg : 0 ≤ M / h.val ^ 2 := div_nonneg hM_nonneg (sq_nonneg h.val)
  have hFin : ∀ z : LOOConcentration.Observation 1 1,
      Integrable (fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) =>
        LOOConcentration.fittedLoss (T r) L D z) P := by
    intro z
    have hKC : Continuous K.val := K.property.1.continuous
    have hRawCont : Continuous (fun D : LOOConcentration.Dataset
        (LOOConcentration.Observation 1 1) (r + 1) =>
        kdeActualRaw K.val h r D (z.1 0)) := by
      unfold kdeActualRaw
      exact continuous_const.mul (continuous_finsetSum Finset.univ (fun j _ =>
        (hKC.comp (by fun_prop)).div_const h.val))
    have hRaw_nonneg (D : LOOConcentration.Dataset
        (LOOConcentration.Observation 1 1) (r + 1)) :
        0 ≤ kdeActualRaw K.val h r D (z.1 0) :=
      kdeActual_raw_nonneg K h r D (z.1 0)
    have hLossEq (D : LOOConcentration.Dataset
        (LOOConcentration.Observation 1 1) (r + 1)) :
        LOOConcentration.fittedLoss (T r) L D z = kdeActualRaw K.val h r D (z.1 0) := by
      exact kdeActual_loss_eq_raw_nonneg K h r D z
    have hLossCont : Continuous (fun D : LOOConcentration.Dataset
        (LOOConcentration.Observation 1 1) (r + 1) =>
        LOOConcentration.fittedLoss (T r) L D z) := by
      convert hRawCont using 1
      funext D
      exact hLossEq D
    apply (integrable_const (C / h.val)).mono' hLossCont.measurable.aestronglyMeasurable
    filter_upwards with D
    rw [Real.norm_eq_abs, hLossEq D, abs_of_nonneg (hRaw_nonneg D)]
    exact kdeActual_raw_le_bound K h C hC r D (z.1 0)
  let G := fun x : EuclideanSpace ℝ (LOOConcentration.ObservationCoordinate 1 1) =>
    LOOConcentration.Revision.meanFittedLoss μ (T r) L
      (LOOConcentration.Revision.observationOfEuclidean x)
      (hFin (LOOConcentration.Revision.observationOfEuclidean x))
  have hLip : LipschitzWith (Real.toNNReal (M / h.val ^ 2)) G := by
    apply LipschitzWith.of_dist_le_mul
    intro E F
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hc_nonneg]
    change |(∫ D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1),
        LOOConcentration.fittedLoss (T r) L D
          (LOOConcentration.Revision.observationOfEuclidean E) ∂P) -
      (∫ D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1),
        LOOConcentration.fittedLoss (T r) L D
          (LOOConcentration.Revision.observationOfEuclidean F) ∂P)| ≤
      M / h.val ^ 2 * ‖E - F‖
    rw [← integral_sub (hFin _) (hFin _)]
    have hDiffInt := (hFin (LOOConcentration.Revision.observationOfEuclidean E)).sub
      (hFin (LOOConcentration.Revision.observationOfEuclidean F))
    have hcoord : |E (Sum.inl 0) - F (Sum.inl 0)| ≤ ‖E - F‖ := by
      simpa only [PiLp.sub_apply, Real.norm_eq_abs] using
        (PiLp.norm_apply_le (E - F) (Sum.inl 0))
    have hPoint (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1)) :
        |LOOConcentration.fittedLoss (T r) L D
            (LOOConcentration.Revision.observationOfEuclidean E) -
          LOOConcentration.fittedLoss (T r) L D
            (LOOConcentration.Revision.observationOfEuclidean F)| ≤
          M / h.val ^ 2 * |E (Sum.inl 0) - F (Sum.inl 0)| := by
      have hQuery := genericKDE_actual_query_lipschitz K.val K.property.1 M hM h.val hh r
        (fun j => (D j).1 0) (E (Sum.inl 0)) (F (Sum.inl 0))
      rw [kdeActual_loss_eq_raw_nonneg K h r D
        (LOOConcentration.Revision.observationOfEuclidean E),
        kdeActual_loss_eq_raw_nonneg K h r D
        (LOOConcentration.Revision.observationOfEuclidean F)]
      simpa [kdeActualRaw, LOOConcentration.Revision.observationOfEuclidean] using hQuery
    calc
      _ = ‖∫ D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1),
          LOOConcentration.fittedLoss (T r) L D
            (LOOConcentration.Revision.observationOfEuclidean E) -
          LOOConcentration.fittedLoss (T r) L D
            (LOOConcentration.Revision.observationOfEuclidean F) ∂P‖ := by
        rw [Real.norm_eq_abs]
      _ ≤ ∫ D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1),
          ‖LOOConcentration.fittedLoss (T r) L D
              (LOOConcentration.Revision.observationOfEuclidean E) -
            LOOConcentration.fittedLoss (T r) L D
              (LOOConcentration.Revision.observationOfEuclidean F)‖ ∂P :=
        norm_integral_le_integral_norm _
      _ = ∫ D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1),
          |LOOConcentration.fittedLoss (T r) L D
              (LOOConcentration.Revision.observationOfEuclidean E) -
            LOOConcentration.fittedLoss (T r) L D
              (LOOConcentration.Revision.observationOfEuclidean F)| ∂P := by
        simp only [Real.norm_eq_abs]
      _ ≤ ∫ _D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1),
          M / h.val ^ 2 * |E (Sum.inl 0) - F (Sum.inl 0)| ∂P :=
        integral_mono hDiffInt.abs (integrable_const _) hPoint
      _ = M / h.val ^ 2 * |E (Sum.inl 0) - F (Sum.inl 0)| := by
        rw [integral_const]
        simp [measureReal_def, measure_univ]
      _ ≤ M / h.val ^ 2 * ‖E - F‖ := mul_le_mul_of_nonneg_left hcoord hc_nonneg
  have hAE := LOOConcentration.locallyLipschitz_ae_differentiableAt_euclidean G hLip.locallyLipschitz
  refine ⟨hFin, hLip, ?_⟩
  filter_upwards [hAE] with x hx
  refine ⟨hx, ?_⟩
  have hFderiv := norm_fderiv_le_of_lipschitz ℝ (x₀ := x) hLip
  have hDualNorm : ‖fderiv ℝ G x‖ = ‖gradient G x‖ := by
    rw [← toDual_gradient]
    exact (InnerProductSpace.toDual ℝ _).norm_map _
  calc
    ‖gradient G x‖ = ‖fderiv ℝ G x‖ := hDualNorm.symm
    _ ≤ M / h.val ^ 2 := hFderiv.trans_eq (Real.coe_toNNReal _ hc_nonneg)

private theorem kdeActual_zeroLoss_integrable
    (μ : Measure (LOOConcentration.Observation 1 1)) [IsProbabilityMeasure μ]
    (K : {K : ℝ → ℝ // ContDiff ℝ 1 K ∧ (∀ x, 0 ≤ K x) ∧
      (∃ B : ℝ, ∀ x, |K x| ≤ B) ∧ (∫ x : ℝ, K x) = 1 ∧
      (∃ B : ℝ, ∀ x, |deriv K x| ≤ B)})
    (h : {t : ℝ // 0 < t}) (C : ℝ) (hC : ∀ t, |K.val t| ≤ C)
    (r : ℕ) :
    Integrable
      (fun z : LOOConcentration.Observation 1 1 =>
        LOOConcentration.fittedLoss (LOOConcentration.Manuscript.kernelDensityEstimator K h r)
          (fun a _ => |a 0|) (0 : LOOConcentration.Dataset
            (LOOConcentration.Observation 1 1) (r + 1)) z) μ := by
  have hKC : Continuous K.val := K.property.1.continuous
  have hLossCont : Continuous (fun z : LOOConcentration.Observation 1 1 =>
      LOOConcentration.fittedLoss (LOOConcentration.Manuscript.kernelDensityEstimator K h r)
        (fun a _ => |a 0|) (0 : LOOConcentration.Dataset
          (LOOConcentration.Observation 1 1) (r + 1)) z) := by
    dsimp [LOOConcentration.fittedLoss, LOOConcentration.Manuscript.kernelDensityEstimator]
    fun_prop
  apply (integrable_const (C / h.val)).mono' hLossCont.measurable.aestronglyMeasurable
  filter_upwards with z
  rw [Real.norm_eq_abs, kdeActual_loss_eq_raw_nonneg, abs_of_nonneg
    (kdeActual_raw_nonneg K h r 0 (z.1 0))]
  exact kdeActual_raw_le_bound K h C hC r 0 (z.1 0)

/-- The source's actual fixed-bandwidth KDE, with its zero response embedding,
has all frozen standing fields with one sample-size-independent constant. -/
private theorem kde_actual_complete_standing_core
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hSecond : Integrable (fun x : ℝ => x ^ 2) μ)
    (hLSI : let scalar := fun x : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => x)
      letI : IsProbabilityMeasure (μ.map scalar) := μ.isProbabilityMeasure_map (by fun_prop)
      LOOConcentration.Revision.logSobolevConstant (μ.map scalar) < ⊤)
    (K : {K : ℝ → ℝ // ContDiff ℝ 1 K ∧ (∀ x, 0 ≤ K x) ∧
      (∃ B : ℝ, ∀ x, |K x| ≤ B) ∧ (∫ x : ℝ, K x) = 1 ∧
      (∃ B : ℝ, ∀ x, |deriv K x| ≤ B)})
    (h : {t : ℝ // 0 < t})
    (ν : Measure (LOOConcentration.Observation 1 1)) [IsProbabilityMeasure ν]
    (hν : ν = μ.map (fun x : ℝ =>
      ((fun _ : Fin 1 => x), (fun _ : Fin 1 => (0 : ℝ))))) :
    let T := fun r : ℕ => LOOConcentration.Manuscript.kernelDensityEstimator K h r
    let L := fun a _ : LOOConcentration.Responses 1 => |a 0|
    ∃ M : ℝ, 0 < M ∧ ∀ n : ℕ,
      LOOConcentration.Revision.StandingAssumption (n := n) ν T L
        (fun N _ => M / (h.val ^ 2 * Real.sqrt (N : ℝ)))
        (fun _ _ => 0) (fun _ => 0) (M / h.val ^ 2) 0 := by
  subst ν
  let ν := μ.map (fun x : ℝ =>
    ((fun _ : Fin 1 => x), (fun _ : Fin 1 => (0 : ℝ))))
  intro T L
  have hEmbedding := kde_zeroResponse_actual_estimator_standing_inputs μ hSecond hLSI K.val h
  have hνSecond : Integrable LOOConcentration.observationNormSq ν := hEmbedding.1
  have hνLSI : LOOConcentration.Revision.observationLogSobolevConstant ν < ⊤ :=
    hEmbedding.2.2.2
  obtain ⟨C, hC⟩ := K.property.2.2.1
  obtain ⟨B, hB⟩ := K.property.2.2.2.2
  have hB_nonneg : 0 ≤ B := (abs_nonneg (deriv K.val 0)).trans (hB 0)
  let M : ℝ := B + 1
  have hM_pos : 0 < M := by dsimp [M]; linarith
  have hM_nonneg : 0 ≤ M := le_of_lt hM_pos
  have hMderiv : ∀ t : ℝ, |deriv K.val t| ≤ M := by
    intro t
    dsimp [M]
    exact (hB t).trans (by linarith)
  refine ⟨M, hM_pos, ?_⟩
  intro n
  have hMean := kdeActual_mean_regularity ν K h M hMderiv hM_nonneg C hC n
  rcases hMean with ⟨hFin, hMeanLip, hMeanGradient⟩
  have hZeroDeleted := kdeActual_zeroLoss_integrable ν K h C hC n
  have hZeroFull := kdeActual_zeroLoss_integrable ν K h C hC (n + 1)
  have hN : Tendsto (fun r : ℕ => (r + 1 : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hInvSqrt : Tendsto (fun r : ℕ => (Real.sqrt (r + 1 : ℝ))⁻¹)
      atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hN)
  have hRate (r : ℕ) :
      M / (h.val ^ 2 * Real.sqrt (r + 1 : ℝ)) =
        (M / h.val ^ 2) * (Real.sqrt (r + 1 : ℝ))⁻¹ := by
    have hh2 : h.val ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos h.property)
    have hs : Real.sqrt (r + 1 : ℝ) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (by positivity))
    field_simp [hh2, hs]
  have hRateTendsto : Tendsto
      (fun r : ℕ => M / (h.val ^ 2 * Real.sqrt (r + 1 : ℝ))) atTop (𝓝 0) := by
    simpa only [hRate, mul_zero] using hInvSqrt.const_mul (M / h.val ^ 2)
  have hStable : LOOConcentration.Revision.Stable ν hνLSI T L
      (fun N _ => M / (h.val ^ 2 * Real.sqrt (N : ℝ))) (fun _ _ => 0) (fun _ => 0) := by
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
      have hKC : Continuous K.val := K.property.1.continuous
      have hLossCont : Continuous (fun p :
          LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r + 1) ×
            LOOConcentration.Observation 1 1 =>
          LOOConcentration.fittedLoss (T r) L p.1 p.2) := by
        dsimp [LOOConcentration.fittedLoss, T, L,
          LOOConcentration.Manuscript.kernelDensityEstimator]
        fun_prop
      exact hLossCont.measurable
    · intro r z
      positivity
    · intro r z
      rfl
    · intro r
      rfl
    · filter_upwards with z
      simpa only [Nat.cast_add, Nat.cast_one] using hRateTendsto
    · exact Eventually.of_forall fun _ => tendsto_const_nhds
    · exact tendsto_const_nhds
    · intro r
      filter_upwards [ae_of_all ν (fun z =>
        (genericKDE_actual_absolute_training_loss_gradient K.val K.property.1
          K.property.2.1 M hMderiv h.val h.property r z).1)] with z hz
      -- The accepted training consumer uses the same literal raw KDE formula;
      -- the estimator identity above relates it to the frozen public estimator.
      simpa only [T, L, kdeActual_estimator_eq_raw K h r,
        kdeActual_rawEstimator, kdeActualRaw, LOOConcentration.fittedLoss] using hz
    · intro r
      filter_upwards [ae_of_all ν (fun z =>
        (genericKDE_actual_absolute_training_loss_gradient K.val K.property.1
          K.property.2.1 M hMderiv h.val h.property r z).2)] with z hz
      filter_upwards with E
      have hGrad := hz E
      simpa only [T, L, kdeActual_estimator_eq_raw K h r,
        kdeActual_rawEstimator, kdeActualRaw, LOOConcentration.fittedLoss,
        Nat.cast_add, Nat.cast_one, zero_mul, add_zero] using hGrad
    · intro n i
      have hBias := genericKDE_actual_heldout_zero_bias ν K.val K.property.1.continuous
        K.property.2.1 C hC h.val h.property n i
      simpa only [T, L, kdeActual_estimator_eq_raw K h n,
        kdeActual_rawEstimator, kdeActualRaw, LOOConcentration.fittedLoss] using hBias.1
    · intro n
      have hBias := genericKDE_actual_heldout_zero_bias ν K.val K.property.1.continuous
        K.property.2.1 C hC h.val h.property n ⟨0, by omega⟩
      simpa only [T, L, kdeActual_estimator_eq_raw K h (n + 1),
        kdeActual_rawEstimator, kdeActualRaw, LOOConcentration.fittedLoss,
        Nat.add_assoc] using hBias.2.2.1
    · intro n i
      have hBias := genericKDE_actual_heldout_zero_bias ν K.val K.property.1.continuous
        K.property.2.1 C hC h.val h.property n i
      simpa only [T, L, kdeActual_estimator_eq_raw K h n,
        kdeActual_estimator_eq_raw K h (n + 1),
        kdeActual_rawEstimator, kdeActualRaw, LOOConcentration.fittedLoss] using hBias.2.2.2.2
  refine {
    lsi := hνLSI
    second_moment := hνSecond
    stable := hStable
    delta₁_deleted_integrable := ?_
    delta₂_deleted_integrable := ?_
    delta₁_full_integrable := ?_
    delta₂_full_integrable := ?_
    zero_deleted_integrable := hZeroDeleted
    zero_full_integrable := hZeroFull
    c_nonneg := ?_
    d_nonneg := le_rfl
    mean_integrable := hFin
    mean_locallyLipschitz := hMeanLip.locallyLipschitz
    mean_gradient := ?_ }
  · exact (integrable_const _)
  · exact integrable_const _
  · exact integrable_const _
  · exact integrable_const _
  · exact div_nonneg hM_nonneg (sq_nonneg h.val)
  · filter_upwards [hMeanGradient] with E hG
    exact ⟨hG.1, by simpa only [zero_mul, add_zero] using hG.2⟩

/-- The source's actual fixed-bandwidth KDE, with its zero response embedding,
has all frozen standing fields with one sample-size-independent constant. -/
theorem kde_actual_complete_standing
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hSecond : Integrable (fun x : ℝ => x ^ 2) μ)
    (hLSI : let scalar := fun x : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => x)
      letI : IsProbabilityMeasure (μ.map scalar) := μ.isProbabilityMeasure_map (by fun_prop)
      LOOConcentration.Revision.logSobolevConstant (μ.map scalar) < ⊤)
    (K : {K : ℝ → ℝ // ContDiff ℝ 1 K ∧ (∀ x, 0 ≤ K x) ∧
      (∃ B : ℝ, ∀ x, |K x| ≤ B) ∧ (∫ x : ℝ, K x) = 1 ∧
      (∃ B : ℝ, ∀ x, |deriv K x| ≤ B)})
    (h : {t : ℝ // 0 < t}) :
    let φ := fun x : ℝ => ((fun _ : Fin 1 => x), (fun _ : Fin 1 => (0 : ℝ)))
    let ν := μ.map φ
    letI : IsProbabilityMeasure ν := μ.isProbabilityMeasure_map (by fun_prop)
    let T := fun r : ℕ => LOOConcentration.Manuscript.kernelDensityEstimator K h r
    let L := fun a _ : LOOConcentration.Responses 1 => |a 0|
    ∃ M : ℝ, 0 < M ∧ ∀ n : ℕ,
      LOOConcentration.Revision.StandingAssumption (n := n) ν T L
        (fun N _ => M / (h.val ^ 2 * Real.sqrt (N : ℝ)))
        (fun _ _ => 0) (fun _ => 0) (M / h.val ^ 2) 0 := by
  intro φ ν T L
  have hνProb : IsProbabilityMeasure ν := μ.isProbabilityMeasure_map (by fun_prop)
  exact @kde_actual_complete_standing_core μ ‹IsProbabilityMeasure μ› hSecond hLSI K h
    ν hνProb rfl

end LOOConcentration.Manuscript.Internal
