import LOOConcentrationRevision.Analysis.UnboundedCenteredWholeMomentImporting
import LOOConcentrationRevision.Results.StandingLossDecomposition
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! Actual standing deleted-fit moments. Off-frontier infrastructure only;
no graph scope ruling or root completion is inferred from this module. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true
namespace LOOConcentration.Revision
open MeasureTheory
open scoped ENNReal

/-- The accepted affine moment theorem applied to the actual fitted-loss section,
with its mean and Lp norm on the original ordered deleted sample law. -/
theorem standing_deleted_loss_centered_moment
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1)) (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)
    (p : ℝ) (hp : 2 ≤ p) :
    ∀ᵐ z ∂μ,
      let P := Measure.pi fun _ : Fin (n + 1) => μ
      let X := fun D : Dataset (Observation k m) (n + 1) =>
        meanFittedLoss μ (T n) L z (hSt.mean_integrable z) - fittedLoss (T n) L D z
      MemLp X (ENNReal.ofReal p) P ∧
        eLpNorm X (ENNReal.ofReal p) P ≤ ENNReal.ofReal
          (Real.sqrt ((observationLogSobolevConstant μ).toReal * (p - 1)) *
            (δ₁ (n + 1) z + Real.sqrt ((n + 1 : ℝ) *
              (∫ w, observationNormSq w ∂μ) +
              (observationLogSobolevConstant μ).toReal * (p - 2)) * δ₂ (n + 1) z)) := by
  filter_upwards [hSt.stable.locallyLipschitz_loss n, hSt.stable.gradient_loss n]
    with z hloc hgrad
  let P : Measure (Dataset (Observation k m) (n + 1)) := Measure.pi fun _ : Fin (n + 1) => μ
  let F : EuclideanSpace ℝ (DatasetCoordinate k m (n + 1)) → ℝ :=
    fun x => fittedLoss (T n) L (datasetOfEuclidean x) z
  let a : NNReal := ⟨δ₁ (n + 1) z, hSt.stable.delta₁_nonneg n z⟩
  let b : NNReal := ⟨δ₂ (n + 1) z, hSt.stable.delta₂_nonneg n z⟩
  have hF : LocallyLipschitz F := hloc
  have hg : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (DatasetCoordinate k m (n + 1)))),
      ‖gradient F x‖ ≤ (a : ℝ) + (b : ℝ) * ‖x‖ := by
    filter_upwards [hgrad] with x hx using hx.2
  have hsrc := unbounded_centered_deleted_observation_application μ hSt.lsi
    hSt.second_moment F hF a b hg hp
  let ν := datasetLawOfObservation (r := n + 1) μ
  have hmean : (∫ x, F x ∂ν) = meanFittedLoss μ (T n) L z (hSt.mean_integrable z) := by
    change (∫ x, F x ∂P.map datasetToEuclidean) = _
    rw [integral_map measurable_datasetToEuclidean.aemeasurable hF.continuous.aestronglyMeasurable]
    simp only [F, datasetOfEuclidean_datasetToEuclidean, meanFittedLoss, P]
  let U := fun x => -(F x - ∫ y, F y ∂ν)
  have hU : MemLp U (ENNReal.ofReal p) ν := hsrc.2.1.neg
  have hcomp : MemLp (U ∘ datasetToEuclidean) (ENNReal.ofReal p) P :=
    hU.comp_of_map measurable_datasetToEuclidean.aemeasurable
  have heq : U ∘ datasetToEuclidean =
      fun D => meanFittedLoss μ (T n) L z (hSt.mean_integrable z) - fittedLoss (T n) L D z := by
    funext D
    simp only [Function.comp_apply, U, F, datasetOfEuclidean_datasetToEuclidean, hmean, neg_sub]
  refine ⟨by simpa only [heq] using hcomp, ?_⟩
  rw [← heq, ← eLpNorm_map_measure hU.aestronglyMeasurable measurable_datasetToEuclidean.aemeasurable]
  have hnorm : eLpNorm U (ENNReal.ofReal p) ν =
      eLpNorm (fun x => F x - ∫ y, F y ∂ν) (ENNReal.ofReal p) ν := by
    exact eLpNorm_neg _ _ _
  change eLpNorm U (ENNReal.ofReal p) ν ≤ _
  rw [hnorm]
  have ha : (a : ℝ) = δ₁ (n + 1) z := rfl
  have hb : (b : ℝ) = δ₂ (n + 1) z := rfl
  simpa only [ha, hb, mul_comm] using hsrc.2.2

private theorem conditional_product_eLpNorm_le
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (ν : Measure A) (μ : Measure B) [SFinite ν] [SFinite μ]
    (F : A × B → ℝ) (G : B → ℝ) (hF : Measurable F)
    (hG : ∀ z, 0 ≤ G z) (p : ℝ) (hp : 0 < p)
    (hcond : ∀ᵐ z ∂μ, eLpNorm (fun x => F (x,z)) (ENNReal.ofReal p) ν ≤
      ENNReal.ofReal (G z)) :
    eLpNorm F (ENNReal.ofReal p) (ν.prod μ) ≤ eLpNorm G (ENNReal.ofReal p) μ := by
  have he (f : A → ℝ) : eLpNorm f (ENNReal.ofReal p) ν = eLpNorm' f p ν := by
    rw [eLpNorm_eq_eLpNorm' (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hp.le]
  have hn (f : B → ℝ) : eLpNorm f (ENNReal.ofReal p) μ = eLpNorm' f p μ := by
    rw [eLpNorm_eq_eLpNorm' (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hp.le]
  have hprod (f : A × B → ℝ) : eLpNorm f (ENNReal.ofReal p) (ν.prod μ) =
      eLpNorm' f p (ν.prod μ) := by
    rw [eLpNorm_eq_eLpNorm' (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hp.le]
  have hpow : ∫⁻ q, ‖F q‖ₑ ^ p ∂(ν.prod μ) ≤ eLpNorm' G p μ ^ p := by
    calc
      _ = ∫⁻ z, ∫⁻ x, ‖F (x,z)‖ₑ ^ p ∂ν ∂μ :=
        lintegral_prod_symm _ (hF.enorm.pow_const p).aemeasurable
      _ ≤ ∫⁻ z, (ENNReal.ofReal (G z)) ^ p ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [hcond] with z hz
        rw [lintegral_rpow_enorm_eq_rpow_eLpNorm' hp]
        exact ENNReal.rpow_le_rpow (by rwa [he] at hz) hp.le
      _ = eLpNorm' G p μ ^ p := by
        rw [← lintegral_rpow_enorm_eq_rpow_eLpNorm' hp]
        apply lintegral_congr_ae
        filter_upwards [] with z
        rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hG z)]
  rw [hprod, hn, eLpNorm'_eq_lintegral_enorm]
  calc
    _ ≤ (eLpNorm' G p μ ^ p) ^ (1 / p) := ENNReal.rpow_le_rpow hpow (by positivity)
    _ = eLpNorm' G p μ := by
      rw [← ENNReal.rpow_mul, show p * (1 / p) = 1 by field_simp [hp.ne'], ENNReal.rpow_one]

/-- Genuine product-law p moment for the actual deleted/test fluctuation.
The only additional inputs are the two original root-authorized MemLp premises. -/
theorem standing_deleted_joint_centered_moment
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1)) (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)
    (p : ℝ) (hp : 2 ≤ p)
    (hδ₁ : MemLp (δ₁ (n + 1)) (ENNReal.ofReal p) μ)
    (hδ₂ : MemLp (δ₂ (n + 1)) (ENNReal.ofReal p) μ) :
    let P := (Measure.pi fun _ : Fin (n + 1) => μ).prod μ
    let X := fun q : Dataset (Observation k m) (n + 1) × Observation k m =>
      meanFittedLoss μ (T n) L q.2 (hSt.mean_integrable q.2) - fittedLoss (T n) L q.1 q.2
    let C := (observationLogSobolevConstant μ).toReal
    let Q := Real.sqrt ((n + 1 : ℝ) * (∫ z, observationNormSq z ∂μ) + C * (p - 2))
    MemLp X (ENNReal.ofReal p) P ∧ eLpNorm X (ENNReal.ofReal p) P ≤ ENNReal.ofReal
      (Real.sqrt (C * (p - 1)) * ((eLpNorm (δ₁ (n + 1)) (ENNReal.ofReal p) μ).toReal +
        Q * (eLpNorm (δ₂ (n + 1)) (ENNReal.ofReal p) μ).toReal)) := by
  let ν : Measure (Dataset (Observation k m) (n + 1)) := Measure.pi fun _ : Fin (n + 1) => μ
  let C := (observationLogSobolevConstant μ).toReal
  let Q := Real.sqrt ((n + 1 : ℝ) * (∫ z, observationNormSq z ∂μ) + C * (p - 2))
  let K := Real.sqrt (C * (p - 1))
  let X : Dataset (Observation k m) (n + 1) × Observation k m → ℝ := fun q =>
    meanFittedLoss μ (T n) L q.2 (hSt.mean_integrable q.2) - fittedLoss (T n) L q.1 q.2
  let G : Observation k m → ℝ := fun z => K * (δ₁ (n + 1) z + Q * δ₂ (n + 1) z)
  have hmean : Measurable (fun z => meanFittedLoss μ (T n) L z (hSt.mean_integrable z)) := by
    let f := fun x : EuclideanSpace ℝ (ObservationCoordinate k m) =>
      meanFittedLoss μ (T n) L (observationOfEuclidean x)
        (hSt.mean_integrable (observationOfEuclidean x))
    have hf : Continuous f := hSt.mean_locallyLipschitz.continuous
    have heq : (fun z => meanFittedLoss μ (T n) L z (hSt.mean_integrable z)) =
        f ∘ observationToEuclidean := by
      funext z
      simp [f]
    rw [heq]
    exact hf.measurable.comp measurable_observationToEuclidean
  have hX : Measurable X := (hmean.comp measurable_snd).sub (hSt.stable.measurable_loss n)
  have hG : ∀ z, 0 ≤ G z := fun z => mul_nonneg (Real.sqrt_nonneg _)
    (add_nonneg (hSt.stable.delta₁_nonneg n z)
      (mul_nonneg (Real.sqrt_nonneg _) (hSt.stable.delta₂_nonneg n z)))
  have hcond : ∀ᵐ z ∂μ, eLpNorm (fun D => X (D,z)) (ENNReal.ofReal p) ν ≤
      ENNReal.ofReal (G z) := by
    filter_upwards [standing_deleted_loss_centered_moment μ T L δ₁ δ₂ δ₃ c d hSt p hp]
      with z hz using hz.2
  have hprod := conditional_product_eLpNorm_le ν μ X G hX hG p (by linarith) hcond
  have hp1 : 1 ≤ ENNReal.ofReal p := by
    exact_mod_cast ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith)
  have hscaleQ : eLpNorm (fun z => Q * δ₂ (n + 1) z) (ENNReal.ofReal p) μ =
      ENNReal.ofReal Q * eLpNorm (δ₂ (n + 1)) (ENNReal.ofReal p) μ := by
    change eLpNorm (Q • δ₂ (n + 1)) (ENNReal.ofReal p) μ = _
    rw [eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hsum : eLpNorm (fun z => δ₁ (n + 1) z + Q * δ₂ (n + 1) z) (ENNReal.ofReal p) μ ≤
      eLpNorm (δ₁ (n + 1)) (ENNReal.ofReal p) μ +
        ENNReal.ofReal Q * eLpNorm (δ₂ (n + 1)) (ENNReal.ofReal p) μ := by
    have hs := eLpNorm_add_le hδ₁.aestronglyMeasurable
      (hδ₂.aestronglyMeasurable.const_smul Q) hp1
    change eLpNorm (fun z => δ₁ (n + 1) z + Q * δ₂ (n + 1) z) (ENNReal.ofReal p) μ ≤
      eLpNorm (δ₁ (n + 1)) (ENNReal.ofReal p) μ +
      eLpNorm (fun z => Q * δ₂ (n + 1) z) (ENNReal.ofReal p) μ at hs
    rw [hscaleQ] at hs
    exact hs
  have hnormG : eLpNorm G (ENNReal.ofReal p) μ ≤ ENNReal.ofReal K *
      (eLpNorm (δ₁ (n + 1)) (ENNReal.ofReal p) μ +
        ENNReal.ofReal Q * eLpNorm (δ₂ (n + 1)) (ENNReal.ofReal p) μ) := by
    change eLpNorm (K • (fun z => δ₁ (n + 1) z + Q * δ₂ (n + 1) z)) (ENNReal.ofReal p) μ ≤ _
    rw [eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_left hsum bot_le
  have hfiniteSum : eLpNorm (δ₁ (n + 1)) (ENNReal.ofReal p) μ +
      ENNReal.ofReal Q * eLpNorm (δ₂ (n + 1)) (ENNReal.ofReal p) μ ≠ ⊤ :=
    (ENNReal.add_lt_top.mpr ⟨hδ₁.2, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hδ₂.2⟩).ne
  have hscale : ENNReal.ofReal K *
      (eLpNorm (δ₁ (n + 1)) (ENNReal.ofReal p) μ +
        ENNReal.ofReal Q * eLpNorm (δ₂ (n + 1)) (ENNReal.ofReal p) μ) =
      ENNReal.ofReal (K * ((eLpNorm (δ₁ (n + 1)) (ENNReal.ofReal p) μ).toReal +
        Q * (eLpNorm (δ₂ (n + 1)) (ENNReal.ofReal p) μ).toReal)) := by
    have he : (eLpNorm (δ₁ (n + 1)) (ENNReal.ofReal p) μ +
        ENNReal.ofReal Q * eLpNorm (δ₂ (n + 1)) (ENNReal.ofReal p) μ).toReal =
        (eLpNorm (δ₁ (n + 1)) (ENNReal.ofReal p) μ).toReal +
          Q * (eLpNorm (δ₂ (n + 1)) (ENNReal.ofReal p) μ).toReal := by
      rw [ENNReal.toReal_add hδ₁.eLpNorm_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hδ₂.eLpNorm_ne_top),
        ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
    rw [← he, ENNReal.ofReal_mul (Real.sqrt_nonneg _), ENNReal.ofReal_toReal hfiniteSum]
  have hb := (hprod.trans hnormG).trans_eq hscale
  refine ⟨⟨hX.aestronglyMeasurable, hb.trans_lt ENNReal.ofReal_lt_top⟩, hb⟩

private theorem eLpNorm_average_le
    {A : Type*} [MeasurableSpace A] (ν : Measure A) {N : ℕ}
    (hN : 0 < N) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (f : Fin N → A → ℝ) (hf : ∀ i, AEStronglyMeasurable (f i) ν)
    (B : ℝ≥0∞) (hB : ∀ i, eLpNorm (f i) p ν ≤ B) :
    eLpNorm ((N : ℝ)⁻¹ • ∑ i : Fin N, f i) p ν ≤ B := by
  classical
  have hs := eLpNorm_sum_le (s := Finset.univ) (f := f) (μ := ν) (p := p)
    (fun i _ => hf i) hp
  have hsum : ∑ i : Fin N, eLpNorm (f i) p ν ≤ (N : ℝ≥0∞) * B := by
    calc
      _ ≤ ∑ _i : Fin N, B := Finset.sum_le_sum fun i _ => hB i
      _ = _ := by simp
  have hc : ‖(N : ℝ)⁻¹‖ₑ * (N : ℝ≥0∞) = 1 := by
    rw [Real.enorm_eq_ofReal_abs,
      abs_of_pos (inv_pos.mpr (Nat.cast_pos.mpr hN)),
      ENNReal.ofReal_inv_of_pos (Nat.cast_pos.mpr hN), ← ENNReal.ofReal_natCast N]
    exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr (Nat.cast_pos.mpr hN)).ne'
      ENNReal.ofReal_ne_top
  calc
    _ ≤ ‖(N : ℝ)⁻¹‖ₑ * eLpNorm (∑ i : Fin N, f i) p ν := eLpNorm_const_smul_le
    _ ≤ ‖(N : ℝ)⁻¹‖ₑ * ((N : ℝ≥0∞) * B) := mul_le_mul_of_nonneg_left (hs.trans hsum) bot_le
    _ = B := by rw [← mul_assoc, hc, one_mul]

/-- Actual standing I1 with original sample index, raw second moment and same
intrinsic LSI constant. No independence between the summands is used. -/
theorem standing_I1_actual_moment
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1)) (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)
    (p : ℝ) (hp : 2 ≤ p)
    (hδ₁ : MemLp (δ₁ (n + 1)) (ENNReal.ofReal p) μ)
    (hδ₂ : MemLp (δ₂ (n + 1)) (ENNReal.ofReal p) μ) :
    let P := Measure.pi fun _ : Fin (n + 2) => μ
    let C := (observationLogSobolevConstant μ).toReal
    let Q := Real.sqrt ((n + 1 : ℝ) * (∫ z, observationNormSq z ∂μ) + C * (p - 2))
    MemLp (standingI1 μ T L δ₁ δ₂ δ₃ c d hSt) (ENNReal.ofReal p) P ∧
      eLpNorm (standingI1 μ T L δ₁ δ₂ δ₃ c d hSt) (ENNReal.ofReal p) P ≤
        ENNReal.ofReal (Real.sqrt (C * (p - 1)) *
          ((eLpNorm (δ₁ (n + 1)) (ENNReal.ofReal p) μ).toReal +
            Q * (eLpNorm (δ₂ (n + 1)) (ENNReal.ofReal p) μ).toReal)) ∧
      (∫ D, standingI1 μ T L δ₁ δ₂ δ₃ c d hSt D ∂P) = 0 := by
  classical
  let P : Measure (Dataset (Observation k m) (n + 2)) := Measure.pi fun _ : Fin (n + 2) => μ
  let ν : Measure (Dataset (Observation k m) (n + 1) × Observation k m) :=
    (Measure.pi fun _ : Fin (n + 1) => μ).prod μ
  let X : Dataset (Observation k m) (n + 1) × Observation k m → ℝ := fun q =>
    meanFittedLoss μ (T n) L q.2 (hSt.mean_integrable q.2) - fittedLoss (T n) L q.1 q.2
  let Y : Fin (n + 2) → Dataset (Observation k m) (n + 2) → ℝ :=
    fun i D => X (deleteAt D i, D i)
  have hj := standing_deleted_joint_centered_moment μ T L δ₁ δ₂ δ₃ c d hSt p hp hδ₁ hδ₂
  have hXlp : MemLp X (ENNReal.ofReal p) ν := hj.1
  have hY : ∀ i, MemLp (Y i) (ENNReal.ofReal p) P := fun i =>
    hXlp.comp_measurePreserving (deleted_sample_and_heldout_measurePreserving μ i)
  have hnormY : ∀ i, eLpNorm (Y i) (ENNReal.ofReal p) P = eLpNorm X (ENNReal.ofReal p) ν :=
    fun i => eLpNorm_comp_measurePreserving (g := X) (p := ENNReal.ofReal p)
      hXlp.aestronglyMeasurable (deleted_sample_and_heldout_measurePreserving μ i)
  have heq : standingI1 μ T L δ₁ δ₂ δ₃ c d hSt =
      (n + 2 : ℝ)⁻¹ • ∑ i : Fin (n + 2), Y i := by
    funext D
    simp only [standingI1, standingV, looEstimate, fittedLoss, Y, X,
      Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Finset.sum_sub_distrib, div_eq_mul_inv]
    ring
  have hp1 : 1 ≤ ENNReal.ofReal p := by
    exact_mod_cast ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith)
  have hI : MemLp (standingI1 μ T L δ₁ δ₂ δ₃ c d hSt) (ENNReal.ofReal p) P := by
    rw [heq]
    exact (memLp_finsetSum' Finset.univ (fun i _ => hY i)).const_smul (n + 2 : ℝ)⁻¹
  have hb := eLpNorm_average_le P (by omega : 0 < n + 2) (ENNReal.ofReal p) hp1 Y
    (fun i => (hY i).aestronglyMeasurable) (eLpNorm X (ENNReal.ofReal p) ν)
    (fun i => (hnormY i).le)
  have hbound := hb.trans hj.2
  constructor
  · exact hI
  constructor
  · rw [heq]
    simpa only [Nat.cast_add, Nat.cast_ofNat, P] using hbound
  · have hi := standingLoss_integrability μ T L δ₁ δ₂ δ₃ c d hSt
    change (∫ D, standingV μ T L δ₁ δ₂ δ₃ c d hSt D - looEstimate (T n) L D ∂P) = 0
    rw [integral_sub hi.2.1 hi.2.2.1]
    change standingEV μ T L δ₁ δ₂ δ₃ c d hSt -
      (∫ D, looEstimate (T n) L D ∂P) = 0
    rw [standingEV_eq_joint μ T L δ₁ δ₂ δ₃ c d hSt,
      integral_looEstimate_eq_independent_test μ (T n) L
        (standingShortLoss_integrable μ T L δ₁ δ₂ δ₃ c d hSt)]
    exact sub_self _

end LOOConcentration.Revision
