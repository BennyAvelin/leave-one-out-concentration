import LOOConcentrationRevision.Results.SourceProductThetaTails
import LOOConcentrationRevision.Concentration.StandingI1WholeGrowthAssembly
import LOOConcentrationRevision.Concentration.StandingI1ZeroLsiEndpoint
import LOOConcentrationRevision.Concentration.StandingValidationSourceCorollary
import LOOConcentration.Probability.LooIntegrability
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic

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

private theorem sharp_gaussian_le_theta_deleted
    (C M₂ : ℝ) (hC : 0 ≤ C) (hM₂ : 0 ≤ M₂)
    (r : ℕ) (hr : 1 ≤ r) (t : ℝ) (ht : 0 < t) (a : ℝ) (ha : 0 ≤ a) :
    (if C * a ^ 2 = 0 then 0 else Real.exp (-(t ^ 2 / (2 * C * a ^ 2)))) ≤
      thetaRate C M₂ hC hM₂ r hr t ht a 0 ha le_rfl := by
  by_cases hC0 : C = 0
  · simp [hC0, thetaRate]
  have hCp : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
  by_cases ha0 : a = 0
  · simp [ha0, thetaRate, hC0]
  have ha2 : 0 < a ^ 2 := sq_pos_of_ne_zero ha0
  have hCa : C * a ^ 2 ≠ 0 := ne_of_gt (mul_pos hCp ha2)
  simp only [if_neg hCa, thetaRate, if_neg hC0, zero_pow (by norm_num : 2 ≠ 0),
    mul_zero, zero_mul, add_zero, if_neg (ne_of_gt ha2)]
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  apply div_le_div_of_nonneg_left (sq_nonneg t) (by positivity)
  nlinarith [mul_pos hCp ha2]

/-- The actual deleted fitted loss is a consumer of the source quadratic-gradient
corollary. Its source mean is transported through the Euclidean sample map. -/
theorem standing_deleted_loss_tails_via_source_corollary
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)
    (t : ℝ) (ht : 0 < t) :
    ∀ᵐ z ∂μ,
      let P : Measure (Dataset (Observation k m) (n + 1)) :=
        Measure.pi fun _ : Fin (n + 1) => μ
      let C := (observationLogSobolevConstant μ).toReal
      let M₂ := ∫ y, observationNormSq y ∂μ
      let θ := thetaRate C M₂ ENNReal.toReal_nonneg
        (integral_nonneg_of_ae (Filter.Eventually.of_forall fun y => by
          change 0 ≤ observationNormSq y
          rw [← observationNorm_sq]
          positivity))
        (n + 1) (by omega) t ht (δ₁ (n + 1) z) (δ₂ (n + 1) z)
        (hSt.stable.delta₁_nonneg n z) (hSt.stable.delta₂_nonneg n z)
      P.real {D | fittedLoss (T n) L D z -
        meanFittedLoss μ (T n) L z (hSt.mean_integrable z) > t} ≤ θ ∧
      P.real {D | meanFittedLoss μ (T n) L z
        (hSt.mean_integrable z) - fittedLoss (T n) L D z > t} ≤ θ := by
  let P : Measure (Dataset (Observation k m) (n+1)) := Measure.pi fun _ : Fin (n+1) => μ
  let C : ℝ := (observationLogSobolevConstant μ).toReal
  let M₂ : ℝ := ∫ y, observationNormSq y ∂μ
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hM₂ : 0 ≤ M₂ := by
    dsimp [M₂]
    apply integral_nonneg_of_ae
    filter_upwards with y
    change 0 ≤ observationNormSq y
    rw [← observationNorm_sq]
    positivity
  have hloc := hSt.stable.locallyLipschitz_loss n
  have hgrad := hSt.stable.gradient_loss n
  filter_upwards [hloc, hgrad] with z hloc hgrad
  let μE : Measure (EuclideanSpace ℝ (ObservationCoordinate k m)) := μ.map observationToEuclidean
  let : IsProbabilityMeasure μE :=
    Measure.isProbabilityMeasure_map measurable_observationToEuclidean.aemeasurable
  let F : EuclideanSpace ℝ (Fin (n+1) × ObservationCoordinate k m) → ℝ := fun x =>
    fittedLoss (T n) L (datasetOfEuclidean x) z
  let a : ℝ := δ₁ (n+1) z
  let b : ℝ := δ₂ (n+1) z
  have ha : 0 ≤ a := by dsimp [a]; exact hSt.stable.delta₁_nonneg n z
  have hb : 0 ≤ b := by dsimp [b]; exact hSt.stable.delta₂_nonneg n z
  have hlocF : LocallyLipschitz F := by simpa only [F] using hloc
  have hgradF : ∀ᵐ x ∂(volume : Measure
      (EuclideanSpace ℝ (DatasetCoordinate k m (n+1)))),
      DifferentiableAt ℝ F x ∧ ‖gradient F x‖ ≤ a + b * ‖x‖ := by
    filter_upwards [hgrad] with x hx
    simpa only [F, a, b] using hx
  have hM2 : Integrable
      (fun x : EuclideanSpace ℝ (ObservationCoordinate k m) => ‖x‖ ^ 2) μE := by
    have hcomp : Integrable
        (fun y : Observation k m => ‖observationToEuclidean y‖ ^ 2) μ := by
      convert hSt.second_moment using 1
      funext y
      calc
        ‖observationToEuclidean y‖ ^ 2 = observationNorm y ^ 2 := by
          rw [observationNorm_eq_euclidean]
        _ = observationNormSq y := observationNorm_sq y
    exact (integrable_map_measure (continuous_norm.pow 2).aestronglyMeasurable
      measurable_observationToEuclidean.aemeasurable).2 hcomp
  have hM2eq : (∫ x : EuclideanSpace ℝ (ObservationCoordinate k m), ‖x‖ ^ 2 ∂μE) =
      ∫ y, observationNormSq y ∂μ := by
    calc
      _ = ∫ y, ‖observationToEuclidean y‖ ^ 2 ∂μ :=
        integral_map measurable_observationToEuclidean.aemeasurable
          (continuous_norm.pow 2).aestronglyMeasurable
      _ = ∫ y, observationNormSq y ∂μ := by
        apply integral_congr_ae
        filter_upwards with y
        calc
          ‖observationToEuclidean y‖ ^ 2 = observationNorm y ^ 2 := by
            rw [observationNorm_eq_euclidean]
          _ = observationNormSq y := observationNorm_sq y
  have hsrc := source_product_theta_tails (n+1) (by omega) μE
    (by change logSobolevConstant (μ.map observationToEuclidean) ≠ ⊤; exact hSt.lsi.ne)
    hM2 F hlocF a b ha hb hgradF t ht
  dsimp only at hsrc
  simp only [μE, euclideanProductLaw_observation_map_eq_datasetLaw μ] at hsrc
  let ν := datasetLawOfObservation (r := n+1) μ
  have hmean : (∫ D, F (datasetToEuclidean D) ∂P) =
      meanFittedLoss μ (T n) L z (hSt.mean_integrable z) := by
    rw [meanFittedLoss]
    apply integral_congr_ae
    filter_upwards with D
    simp only [F, datasetOfEuclidean_datasetToEuclidean]
  have hnu : ν = P.map datasetToEuclidean := rfl
  have hmapMean : (∫ x, F x ∂ν) = ∫ D, F (datasetToEuclidean D) ∂P := by
    rw [hnu]
    exact integral_map measurable_datasetToEuclidean.aemeasurable
      hlocF.continuous.aestronglyMeasurable
  have hcenter : (∫ x, F x ∂ν) = meanFittedLoss μ (T n) L z (hSt.mean_integrable z) :=
    hmapMean.trans hmean
  have hsetPlus : MeasurableSet {x | F x - ∫ y, F y ∂ν > t} :=
    measurableSet_Ioi.preimage (hlocF.continuous.sub continuous_const).measurable
  have hsetMinus : MeasurableSet {x | ∫ y, F y ∂ν - F x > t} :=
    measurableSet_Ioi.preimage (continuous_const.sub hlocF.continuous).measurable
  have hprePlus : datasetToEuclidean ⁻¹' {x | F x - ∫ y, F y ∂ν > t} =
      {D | fittedLoss (T n) L D z -
        meanFittedLoss μ (T n) L z (hSt.mean_integrable z) > t} := by
    ext D
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    simp [F, hcenter]
  have hmassPlus : (P.map datasetToEuclidean) {x | F x - ∫ y, F y ∂ν > t} =
      P {D | fittedLoss (T n) L D z -
        meanFittedLoss μ (T n) L z (hSt.mean_integrable z) > t} := by
    rw [Measure.map_apply measurable_datasetToEuclidean hsetPlus, hprePlus]
  have hmapPlus : (P.map datasetToEuclidean).real
      {x | F x - ∫ y, F y ∂ν > t} =
      P.real {D | fittedLoss (T n) L D z -
        meanFittedLoss μ (T n) L z (hSt.mean_integrable z) > t} := by
    exact congrArg ENNReal.toReal hmassPlus
  have hmeasurePlus : P.real {D | fittedLoss (T n) L D z -
      meanFittedLoss μ (T n) L z (hSt.mean_integrable z) > t} =
      ν.real {x | F x - ∫ y, F y ∂ν > t} := by
    calc
      _ = (P.map datasetToEuclidean).real {x | F x - ∫ y, F y ∂ν > t} := hmapPlus.symm
      _ = ν.real {x | F x - ∫ y, F y ∂ν > t} :=
        (congrArg (fun q : Measure (EuclideanSpace ℝ (DatasetCoordinate k m (n+1))) =>
          q.real {x | F x - ∫ y, F y ∂ν > t}) hnu).symm
  have hpreMinus : datasetToEuclidean ⁻¹' {x | ∫ y, F y ∂ν - F x > t} =
      {D | meanFittedLoss μ (T n) L z
        (hSt.mean_integrable z) - fittedLoss (T n) L D z > t} := by
    ext D
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    simp [F, hcenter]
  have hmassMinus : (P.map datasetToEuclidean) {x | ∫ y, F y ∂ν - F x > t} =
      P {D | meanFittedLoss μ (T n) L z
        (hSt.mean_integrable z) - fittedLoss (T n) L D z > t} := by
    rw [Measure.map_apply measurable_datasetToEuclidean hsetMinus, hpreMinus]
  have hmapMinus : (P.map datasetToEuclidean).real
      {x | ∫ y, F y ∂ν - F x > t} =
      P.real {D | meanFittedLoss μ (T n) L z
        (hSt.mean_integrable z) - fittedLoss (T n) L D z > t} := by
    exact congrArg ENNReal.toReal hmassMinus
  have hmeasureMinus : P.real {D | meanFittedLoss μ (T n) L z
      (hSt.mean_integrable z) - fittedLoss (T n) L D z > t} =
      ν.real {x | ∫ y, F y ∂ν - F x > t} := by
    calc
      _ = (P.map datasetToEuclidean).real {x | ∫ y, F y ∂ν - F x > t} := hmapMinus.symm
      _ = ν.real {x | ∫ y, F y ∂ν - F x > t} :=
        (congrArg (fun q : Measure (EuclideanSpace ℝ (DatasetCoordinate k m (n+1))) =>
          q.real {x | ∫ y, F y ∂ν - F x > t}) hnu).symm
  have htheta : (if b = 0 then
      (if C * a ^ 2 = 0 then 0 else Real.exp (-(t ^ 2 / (2 * C * a ^ 2))))
    else thetaRate C M₂ hC hM₂ (n+1) (by omega) t ht a b ha hb) ≤
      thetaRate C M₂ hC hM₂ (n+1) (by omega) t ht a b ha hb := by
    by_cases hb0 : b = 0
    · simp only [hb0]
      exact sharp_gaussian_le_theta_deleted C M₂ hC hM₂ (n+1) (by omega) t ht a ha
    · simp only [if_neg hb0, le_rfl]
  have hM2eq' : (∫ x : EuclideanSpace ℝ (ObservationCoordinate k m), ‖x‖ ^ 2
      ∂(μ.map observationToEuclidean)) = M₂ := by
    simpa [μE, M₂] using hM2eq
  have hsrc' :
      ν.real {x | F x - ∫ y, F y ∂ν > t} ≤
        (if b = 0 then
          (if C * a ^ 2 = 0 then 0 else Real.exp (-(t ^ 2 / (2 * C * a ^ 2))))
         else thetaRate C M₂ hC hM₂ (n+1) (by omega) t ht a b ha hb) ∧
      ν.real {x | ∫ y, F y ∂ν - F x > t} ≤
        (if b = 0 then
          (if C * a ^ 2 = 0 then 0 else Real.exp (-(t ^ 2 / (2 * C * a ^ 2))))
         else thetaRate C M₂ hC hM₂ (n+1) (by omega) t ht a b ha hb) := by
    simpa [ν, datasetLawOfObservation, DatasetCoordinate, C, M₂, a, b,
      observationLogSobolevConstant, hM2eq', thetaRate] using hsrc
  constructor
  · rw [hmeasurePlus]
    exact hsrc'.1.trans htheta
  · rw [hmeasureMinus]
    exact hsrc'.2.trans htheta


theorem standing_I1_mixed_growth_mixture_tail_positive_constant_via_source_corollary
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)
    (hCpos : 0 < (observationLogSobolevConstant μ).toReal)
    (t : ℝ) (ht : 0 < t) :
    let P := Measure.pi fun _ : Fin (n+2) => μ
    let I₁ := fun D : Dataset (Observation k m) (n+2) =>
      (∑ i : Fin (n+2), meanFittedLoss μ (T n) L (D i)
        (hSt.mean_integrable (D i))) / (n+2:ℝ) - looEstimate (T n) L D
    let C := (observationLogSobolevConstant μ).toReal
    let M₂ := ∫ y, observationNormSq y ∂μ
    let hM₂ := integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun y => LOOConcentration.observationNormSq_nonneg y)
    let rate := fun z => LOOConcentration.thetaRate C M₂ hCpos hM₂
      (n + 1) (by omega) t ht (δ₁ (n + 1) z) (δ₂ (n + 1) z)
      (hSt.stable.delta₁_nonneg n z) (hSt.stable.delta₂_nonneg n z)
    P.real {D | I₁ D > t} ≤ (n+2:ℝ) * ∫ z, rate z ∂μ ∧
      P.real {D | -I₁ D > t} ≤ (n+2:ℝ) * ∫ z, rate z ∂μ := by
  let P : Measure (Dataset (Observation k m) (n+2)) :=
    Measure.pi fun _ : Fin (n+2) => μ
  let PTrain : Measure (Dataset (Observation k m) (n+1)) :=
    Measure.pi fun _ : Fin (n+1) => μ
  let C : ℝ := (observationLogSobolevConstant μ).toReal
  let M₂ : ℝ := ∫ y, observationNormSq y ∂μ
  have hC : 0 < C := hCpos
  have hM₂ : 0 ≤ M₂ := integral_nonneg_of_ae
    (Filter.Eventually.of_forall fun y => LOOConcentration.observationNormSq_nonneg y)
  let rate : Observation k m → ℝ := fun z =>
    LOOConcentration.thetaRate C M₂ hC hM₂ (n+1) (by omega) t ht
      (δ₁ (n+1) z) (δ₂ (n+1) z)
      (hSt.stable.delta₁_nonneg n z) (hSt.stable.delta₂_nonneg n z)
  let I₁ : Dataset (Observation k m) (n+2) → ℝ := fun D =>
    (∑ i : Fin (n+2), meanFittedLoss μ (T n) L (D i)
      (hSt.mean_integrable (D i))) / (n+2:ℝ) - looEstimate (T n) L D
  let Y : Fin (n+2) → Dataset (Observation k m) (n+2) → ℝ := fun i D =>
    meanFittedLoss μ (T n) L (D i) (hSt.mean_integrable (D i)) -
      fittedLoss (T n) L (deleteAt D i) (D i)
  have hrate_nonneg (z : Observation k m) : 0 ≤ rate z :=
    LOOConcentration.thetaRate_nonneg C M₂ hC hM₂ (n+1) (by omega) t ht
      (δ₁ (n+1) z) (δ₂ (n+1) z)
      (hSt.stable.delta₁_nonneg n z) (hSt.stable.delta₂_nonneg n z)
  have hrateInt : Integrable rate μ := by
    dsimp [rate]
    exact LOOConcentration.integrable_thetaRate_of_integrable_coefficients
      hSt.delta₁_deleted_integrable hSt.delta₂_deleted_integrable
      C M₂ hC hM₂ (n+1) (by omega) t ht
      (fun z => hSt.stable.delta₁_nonneg n z)
      (fun z => hSt.stable.delta₂_nonneg n z)
  have hmeanMeas : Measurable (fun z : Observation k m =>
      meanFittedLoss μ (T n) L z (hSt.mean_integrable z)) := by
    let f : EuclideanSpace ℝ (ObservationCoordinate k m) → ℝ := fun x =>
      meanFittedLoss μ (T n) L (observationOfEuclidean x)
        (hSt.mean_integrable (observationOfEuclidean x))
    have hf : Continuous f := hSt.mean_locallyLipschitz.continuous
    have heq : (fun z : Observation k m =>
        meanFittedLoss μ (T n) L z (hSt.mean_integrable z)) =
        fun z => f (observationToEuclidean z) := by
      funext z
      simp [f]
    rw [heq]
    exact hf.measurable.comp measurable_observationToEuclidean
  have hfitMeas : Measurable
      (fun p : Dataset (Observation k m) (n+1) × Observation k m =>
        fittedLoss (T n) L p.1 p.2) := hSt.stable.measurable_loss n
  let X : Dataset (Observation k m) (n+1) × Observation k m → ℝ := fun p =>
    meanFittedLoss μ (T n) L p.2 (hSt.mean_integrable p.2) - fittedLoss (T n) L p.1 p.2
  have hXmeas : Measurable X := hmeanMeas.comp measurable_snd |>.sub hfitMeas
  have hsection := standing_deleted_loss_tails_via_source_corollary
    μ T L δ₁ δ₂ δ₃ c d hSt t ht
  have hcond : ∀ᵐ z ∂μ,
      PTrain.real {D | X (D,z) > t} ≤ rate z ∧
      PTrain.real {D | -X (D,z) > t} ≤ rate z := by
    filter_upwards [hsection] with z htails
    have hrateEq := thetaRate_eq_historical_of_pos C M₂ hC hM₂
      (n+1) (by omega) t ht (δ₁ (n+1) z) (δ₂ (n+1) z)
      (hSt.stable.delta₁_nonneg n z) (hSt.stable.delta₂_nonneg n z)
    constructor
    · simpa [X, rate, C, M₂, PTrain, hrateEq] using htails.2
    · simpa [X, rate, C, M₂, PTrain, hrateEq, neg_sub] using htails.1
  let Splus : Set (Dataset (Observation k m) (n+1) × Observation k m) :=
    {p | X p > t}
  let Sminus : Set (Dataset (Observation k m) (n+1) × Observation k m) :=
    {p | -X p > t}
  have hSplus : MeasurableSet Splus := measurableSet_Ioi.preimage hXmeas
  have hSminus : MeasurableSet Sminus := measurableSet_Ioi.preimage hXmeas.neg
  have hproduct (S : Set (Dataset (Observation k m) (n+1) × Observation k m))
      (hS : MeasurableSet S) :
      (PTrain.prod μ) S = ∫⁻ z, PTrain ((fun D => (D,z)) ⁻¹' S) ∂μ :=
    Measure.prod_apply_symm hS
  have hsectionPlus : ∀ z, PTrain ((fun D => (D,z)) ⁻¹' Splus) =
      PTrain {D | X (D,z) > t} := by intro z; rfl
  have hsectionMinus : ∀ z, PTrain ((fun D => (D,z)) ⁻¹' Sminus) =
      PTrain {D | -X (D,z) > t} := by intro z; rfl
  have hqPlus : ∀ᵐ z ∂μ,
      PTrain ((fun D => (D,z)) ⁻¹' Splus) ≤ ENNReal.ofReal (rate z) := by
    filter_upwards [hcond] with z hz
    have hfinite : PTrain {D | X (D,z) > t} ≠ ⊤ := measure_ne_top _ _
    have hreal : (PTrain {D | X (D,z) > t}).toReal ≤ rate z := by
      simpa only [Measure.real_def] using hz.1
    rw [hsectionPlus z, ← ENNReal.ofReal_toReal hfinite]
    exact ENNReal.ofReal_le_ofReal hreal
  have hqMinus : ∀ᵐ z ∂μ,
      PTrain ((fun D => (D,z)) ⁻¹' Sminus) ≤ ENNReal.ofReal (rate z) := by
    filter_upwards [hcond] with z hz
    have hfinite : PTrain {D | -X (D,z) > t} ≠ ⊤ := measure_ne_top _ _
    have hreal : (PTrain {D | -X (D,z) > t}).toReal ≤ rate z := by
      simpa only [Measure.real_def] using hz.2
    rw [hsectionMinus z, ← ENNReal.ofReal_toReal hfinite]
    exact ENNReal.ofReal_le_ofReal hreal
  have hlintegral : ∫⁻ z, ENNReal.ofReal (rate z) ∂μ =
      ENNReal.ofReal (∫ z, rate z ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal hrateInt
      (Filter.Eventually.of_forall fun z => hrate_nonneg _)).symm
  have hmixPlus : (PTrain.prod μ) Splus ≤ ENNReal.ofReal (∫ z, rate z ∂μ) := by
    rw [hproduct Splus hSplus]
    exact (lintegral_mono_ae hqPlus).trans_eq hlintegral
  have hmixMinus : (PTrain.prod μ) Sminus ≤ ENNReal.ofReal (∫ z, rate z ∂μ) := by
    rw [hproduct Sminus hSminus]
    exact (lintegral_mono_ae hqMinus).trans_eq hlintegral
  have hYiPlus (i : Fin (n+2)) :
      P.real {D | Y i D > t} ≤ ∫ z, rate z ∂μ := by
    have hmap := deleted_tail_integral μ i Splus hSplus
    have hEq : {D | Y i D > t} =
        (fun D : Dataset (Observation k m) (n+2) => (deleteAt D i,D i)) ⁻¹' Splus := by
      ext D
      simp [Y, Splus, X]
    rw [Measure.real_def, hEq, hmap]
    have hnonneg : 0 ≤ ∫ z, rate z ∂μ := integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun z => hrate_nonneg _)
    exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hmixPlus |>.trans_eq
      (ENNReal.toReal_ofReal hnonneg)
  have hYiMinus (i : Fin (n+2)) :
      P.real {D | -Y i D > t} ≤ ∫ z, rate z ∂μ := by
    have hmap := deleted_tail_integral μ i Sminus hSminus
    have hEq : {D | -Y i D > t} =
        (fun D : Dataset (Observation k m) (n+2) => (deleteAt D i,D i)) ⁻¹' Sminus := by
      ext D
      simp [Y, Sminus, X]
    rw [Measure.real_def, hEq, hmap]
    have hnonneg : 0 ≤ ∫ z, rate z ∂μ := integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun z => hrate_nonneg _)
    exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hmixMinus |>.trans_eq
      (ENNReal.toReal_ofReal hnonneg)
  have hI1eq (D : Dataset (Observation k m) (n+2)) :
      I₁ D = (∑ i : Fin (n+2), Y i D) / (n+2:ℝ) := by
    simp [I₁, Y, looEstimate, fittedLoss]
    ring_nf
  have hN : 0 < (n+2:ℝ) := by positivity
  have hsubset : {D | I₁ D > t} ⊆ ⋃ i : Fin (n+2), {D | Y i D > t} := by
    intro D hD
    by_contra hnone
    have hcoord : ∀ i, Y i D ≤ t := by
      intro i
      exact le_of_not_gt (fun hh => hnone (Set.mem_iUnion.mpr ⟨i, hh⟩))
    have hsum : (∑ i : Fin (n+2), Y i D) ≤ (n+2:ℝ)*t := by
      calc
        _ ≤ ∑ _i : Fin (n+2), t := Finset.sum_le_sum fun i hi => hcoord i
        _ = (n+2:ℝ)*t := by simp
    have hsum' : (∑ i : Fin (n+2), Y i D) ≤ t*(n+2:ℝ) := by
      simpa [mul_comm] using hsum
    change I₁ D > t at hD
    rw [hI1eq] at hD
    have hdiv : (∑ i : Fin (n+2), Y i D)/(n+2:ℝ) ≤ t :=
      (div_le_iff₀ hN).2 hsum'
    linarith
  have hsubsetNeg : {D | -I₁ D > t} ⊆ ⋃ i : Fin (n+2), {D | -Y i D > t} := by
    intro D hD
    by_contra hnone
    have hcoord : ∀ i, -Y i D ≤ t := by
      intro i
      exact le_of_not_gt (fun hh => hnone (Set.mem_iUnion.mpr ⟨i, hh⟩))
    have hsum : (∑ i : Fin (n+2), -Y i D) ≤ (n+2:ℝ)*t := by
      calc
        _ ≤ ∑ _i : Fin (n+2), t := Finset.sum_le_sum fun i hi => hcoord i
        _ = (n+2:ℝ)*t := by simp
    have hsum' : (∑ i : Fin (n+2), -Y i D) ≤ t*(n+2:ℝ) := by
      simpa [mul_comm] using hsum
    have hNegEq : -I₁ D = (∑ i : Fin (n+2), -Y i D)/(n+2:ℝ) := by
      rw [hI1eq, Finset.sum_neg_distrib, neg_div]
    change -I₁ D > t at hD
    rw [hNegEq] at hD
    have hdiv : (∑ i : Fin (n+2), -Y i D)/(n+2:ℝ) ≤ t :=
      (div_le_iff₀ hN).2 hsum'
    linarith
  have hsumPlus : ∑ i : Fin (n+2), P.real {D | Y i D > t} ≤
      (n+2:ℝ) * ∫ z, rate z ∂μ := by
    calc
      _ ≤ ∑ _i : Fin (n+2), ∫ z, rate z ∂μ := Finset.sum_le_sum fun i hi => hYiPlus i
      _ = (n+2:ℝ) * ∫ z, rate z ∂μ := by simp
  have hsumMinus : ∑ i : Fin (n+2), P.real {D | -Y i D > t} ≤
      (n+2:ℝ) * ∫ z, rate z ∂μ := by
    calc
      _ ≤ ∑ _i : Fin (n+2), ∫ z, rate z ∂μ := Finset.sum_le_sum fun i hi => hYiMinus i
      _ = (n+2:ℝ) * ∫ z, rate z ∂μ := by simp
  change P.real {D | I₁ D > t} ≤ (n+2:ℝ) * ∫ z, rate z ∂μ ∧
      P.real {D | -I₁ D > t} ≤ (n+2:ℝ) * ∫ z, rate z ∂μ
  refine ⟨?_, ?_⟩
  · calc
      P.real {D | I₁ D > t} ≤ P.real (⋃ i : Fin (n+2), {D | Y i D > t}) := measureReal_mono hsubset
      _ ≤ ∑ i : Fin (n+2), P.real {D | Y i D > t} := measureReal_iUnion_fintype_le _
      _ ≤ (n+2:ℝ) * ∫ z, rate z ∂μ := hsumPlus
  · calc
      P.real {D | -I₁ D > t} ≤ P.real (⋃ i : Fin (n+2), {D | -Y i D > t}) := measureReal_mono hsubsetNeg
      _ ≤ ∑ i : Fin (n+2), P.real {D | -Y i D > t} := measureReal_iUnion_fintype_le _
      _ ≤ (n+2:ℝ) * ∫ z, rate z ∂μ := hsumMinus



theorem standing_I1_mixed_growth_mixture_tail_via_source_corollary
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)
    (t : ℝ) (ht : 0 < t) :
    let P := Measure.pi fun _ : Fin (n + 2) => μ
    let I₁ := fun D : Dataset (Observation k m) (n + 2) =>
      (∑ i : Fin (n + 2), meanFittedLoss μ (T n) L (D i)
        (hSt.mean_integrable (D i))) / (n + 2 : ℝ) - LOOConcentration.looEstimate (T n) L D
    let C := (observationLogSobolevConstant μ).toReal
    let M₂ := ∫ y, observationNormSq y ∂μ
    let hM₂ := integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun y => LOOConcentration.observationNormSq_nonneg y)
    let rate := fun z => thetaRate C M₂ ENNReal.toReal_nonneg hM₂
      (n + 1) (by omega) t ht (δ₁ (n + 1) z) (δ₂ (n + 1) z)
      (hSt.stable.delta₁_nonneg n z) (hSt.stable.delta₂_nonneg n z)
    P.real {D | I₁ D > t} ≤ (n + 2 : ℝ) * ∫ z, rate z ∂μ ∧
      P.real {D | -I₁ D > t} ≤ (n + 2 : ℝ) * ∫ z, rate z ∂μ := by
  let P : Measure (Dataset (Observation k m) (n + 2)) :=
    Measure.pi fun _ : Fin (n + 2) => μ
  let I₁ : Dataset (Observation k m) (n + 2) → ℝ := fun D =>
    (∑ i : Fin (n + 2), meanFittedLoss μ (T n) L (D i)
      (hSt.mean_integrable (D i))) / (n + 2 : ℝ) - LOOConcentration.looEstimate (T n) L D
  let C : ℝ := (observationLogSobolevConstant μ).toReal
  let M₂ : ℝ := ∫ y, observationNormSq y ∂μ
  have hM₂ : 0 ≤ M₂ := integral_nonneg_of_ae
    (Filter.Eventually.of_forall fun y => LOOConcentration.observationNormSq_nonneg y)
  let rate : Observation k m → ℝ := fun z => thetaRate C M₂ ENNReal.toReal_nonneg hM₂
      (n + 1) (by omega) t ht (δ₁ (n + 1) z) (δ₂ (n + 1) z)
      (hSt.stable.delta₁_nonneg n z) (hSt.stable.delta₂_nonneg n z)
  by_cases hCzero : observationLogSobolevConstant μ = 0
  · have hzero := standing_I1_zero_lsi_endpoint μ T L δ₁ δ₂ δ₃ c d hSt hCzero t ht
    constructor
    · simpa [P, I₁, rate, C, M₂, hCzero, thetaRate, standingI1, standingV]
        using le_of_eq hzero.1
    · simpa [P, I₁, rate, C, M₂, hCzero, thetaRate, standingI1, standingV]
        using le_of_eq hzero.2
  · have hCpos : 0 < C := by
      have hCnonneg : 0 ≤ C := ENNReal.toReal_nonneg
      by_contra hnot
      have hC0 : C = 0 := le_antisymm (le_of_not_gt hnot) hCnonneg
      have hLCzero : observationLogSobolevConstant μ = 0 ∨
          observationLogSobolevConstant μ = ⊤ :=
        (ENNReal.toReal_eq_zero_iff _).mp (by simpa [C] using hC0)
      rcases hLCzero with hz | hinf
      · exact (hCzero hz).elim
      · exact hSt.lsi.ne hinf
    have hpos := standing_I1_mixed_growth_mixture_tail_positive_constant_via_source_corollary
      μ T L δ₁ δ₂ δ₃ c d hSt hCpos t ht
    have hrateEq (z : Observation k m) : rate z =
        LOOConcentration.thetaRate C M₂ hCpos hM₂ (n + 1) (by omega) t ht
          (δ₁ (n + 1) z) (δ₂ (n + 1) z)
          (hSt.stable.delta₁_nonneg n z) (hSt.stable.delta₂_nonneg n z) := by
      dsimp [rate]
      exact thetaRate_eq_historical_of_pos C M₂ hCpos hM₂ (n + 1) (by omega)
        t ht (δ₁ (n + 1) z) (δ₂ (n + 1) z)
        (hSt.stable.delta₁_nonneg n z) (hSt.stable.delta₂_nonneg n z)
    have hrateIntEq : (∫ z, rate z ∂μ) =
        ∫ z, LOOConcentration.thetaRate C M₂ hCpos hM₂ (n + 1) (by omega) t ht
          (δ₁ (n + 1) z) (δ₂ (n + 1) z)
          (hSt.stable.delta₁_nonneg n z) (hSt.stable.delta₂_nonneg n z) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hrateEq
    have hposOld :
        P.real {D | I₁ D > t} ≤ (n + 2 : ℝ) *
            ∫ z, LOOConcentration.thetaRate C M₂ hCpos hM₂ (n + 1) (by omega)
              t ht (δ₁ (n + 1) z) (δ₂ (n + 1) z)
              (hSt.stable.delta₁_nonneg n z) (hSt.stable.delta₂_nonneg n z) ∂μ ∧
          P.real {D | -I₁ D > t} ≤ (n + 2 : ℝ) *
            ∫ z, LOOConcentration.thetaRate C M₂ hCpos hM₂ (n + 1) (by omega)
              t ht (δ₁ (n + 1) z) (δ₂ (n + 1) z)
              (hSt.stable.delta₁_nonneg n z) (hSt.stable.delta₂_nonneg n z) ∂μ := by
      simpa [P, I₁, C, M₂, standingI1, standingV] using hpos
    constructor
    · calc
        P.real {D | I₁ D > t} ≤ (n + 2 : ℝ) *
            ∫ z, LOOConcentration.thetaRate C M₂ hCpos hM₂ (n + 1) (by omega)
              t ht (δ₁ (n + 1) z) (δ₂ (n + 1) z)
              (hSt.stable.delta₁_nonneg n z) (hSt.stable.delta₂_nonneg n z) ∂μ := hposOld.1
        _ = (n + 2 : ℝ) * ∫ z, rate z ∂μ := by rw [← hrateIntEq]
    · calc
        P.real {D | -I₁ D > t} ≤ (n + 2 : ℝ) *
            ∫ z, LOOConcentration.thetaRate C M₂ hCpos hM₂ (n + 1) (by omega)
              t ht (δ₁ (n + 1) z) (δ₂ (n + 1) z)
              (hSt.stable.delta₁_nonneg n z) (hSt.stable.delta₂_nonneg n z) ∂μ := hposOld.2
        _ = (n + 2 : ℝ) * ∫ z, rate z ∂μ := by rw [← hrateIntEq]



end LOOConcentration.Revision
