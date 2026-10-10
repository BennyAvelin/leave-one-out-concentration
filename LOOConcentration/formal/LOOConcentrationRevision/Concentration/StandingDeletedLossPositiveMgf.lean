import LOOConcentrationRevision.Concentration.StandingDeletedLossSubGaussian
import LOOConcentrationRevision.Concentration.Chernoff
import LOOConcentration.Frozen.Foundations.LooEstimate
import LOOConcentration.Probability.DeletedTransport
import LOOConcentration.Results.MainRateIntegrability
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic
import LOOConcentrationRevision.Concentration.SourceProductMgfAllSizes
import LOOConcentrationRevision.Probability.ProductLawTransport
import LOOConcentrationRevision.Probability.ProductSecondMoment
import LOOConcentrationRevision.Frozen.Definitions.DatasetOfEuclidean
import LOOConcentrationRevision.Frozen.Definitions.ObservationOfEuclidean
import LOOConcentrationRevision.Frozen.Definitions.ObservationLogSobolevConstant
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Revision
open MeasureTheory
open scoped Gradient

/-- The actual deleted fitted loss has the source positive-growth MGF bound,
centered at its literal source mean. The positive-growth window is quantified
only on the source parameter domain. -/
theorem standing_deleted_loss_centered_exp_log_bound
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (loss : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T loss δ₁ δ₂ δ₃ c d) :
    ∀ᵐ z ∂μ, 0 < δ₂ (n + 1) z →
      ∀ s : ℝ,
        |s| ≤ 1 / (4 * (observationLogSobolevConstant μ).toReal *
          δ₂ (n + 1) z) →
        Integrable
          (fun D : Dataset (Observation k m) (n + 1) =>
            Real.exp (s * (fittedLoss (T n) loss D z -
              meanFittedLoss μ (T n) loss z (hSt.mean_integrable z))))
          (Measure.pi fun _ : Fin (n + 1) => μ) ∧
        (∫ D : Dataset (Observation k m) (n + 1),
          Real.exp (s * (fittedLoss (T n) loss D z -
            meanFittedLoss μ (T n) loss z (hSt.mean_integrable z)))
          ∂Measure.pi fun _ : Fin (n + 1) => μ) ≤
          Real.exp ((2 * (observationLogSobolevConstant μ).toReal *
            ((δ₁ (n + 1) z)^2 + 2 * (δ₂ (n + 1) z)^2 *
              ((n + 1 : ℕ) : ℝ) * (∫ y, observationNormSq y ∂μ))) * s^2) ∧
        Real.log (∫ D : Dataset (Observation k m) (n + 1),
          Real.exp (s * (fittedLoss (T n) loss D z -
            meanFittedLoss μ (T n) loss z (hSt.mean_integrable z)))
          ∂Measure.pi fun _ : Fin (n + 1) => μ) ≤
          (2 * (observationLogSobolevConstant μ).toReal *
            ((δ₁ (n + 1) z)^2 + 2 * (δ₂ (n + 1) z)^2 *
              ((n + 1 : ℕ) : ℝ) * (∫ y, observationNormSq y ∂μ))) * s^2 := by
  filter_upwards [hSt.stable.locallyLipschitz_loss n,
    hSt.stable.gradient_loss n] with z hloc hgrad
  intro hb s hcut
  let P : Measure (Dataset (Observation k m) (n + 1)) :=
    Measure.pi fun _ : Fin (n + 1) => μ
  let ν := datasetLawOfObservation (r := n + 1) μ
  let F : EuclideanSpace ℝ (DatasetCoordinate k m (n + 1)) → ℝ :=
    fun x => fittedLoss (T n) loss (datasetOfEuclidean x) z
  let a : NNReal := ⟨δ₁ (n + 1) z, hSt.stable.delta₁_nonneg n z⟩
  let b : NNReal := ⟨δ₂ (n + 1) z, hSt.stable.delta₂_nonneg n z⟩
  let C : ℝ := (observationLogSobolevConstant μ).toReal
  let μE := μ.map observationToEuclidean
  have : IsProbabilityMeasure μE :=
    Measure.isProbabilityMeasure_map measurable_observationToEuclidean.aemeasurable
  have ha : (a : ℝ) = δ₁ (n + 1) z := rfl
  have hbCoe : (b : ℝ) = δ₂ (n + 1) z := rfl
  have hC : 0 ≤ C := by dsimp [C]; exact ENNReal.toReal_nonneg
  have hLC : logSobolevConstant μE ≤ ENNReal.ofReal C := by
    change logSobolevConstant (μ.map observationToEuclidean) ≤
      ENNReal.ofReal ((observationLogSobolevConstant μ).toReal)
    rw [ENNReal.ofReal_toReal hSt.lsi.ne]
    rfl
  have hM2 : Integrable
      (fun x : EuclideanSpace ℝ (ObservationCoordinate k m) => ‖x‖ ^ 2)
      μE := by
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
  have hlocF : LocallyLipschitz F := by
    simpa only [F] using hloc
  have hgradF :
      ∀ᵐ x ∂(volume : Measure
        (EuclideanSpace ℝ (DatasetCoordinate k m (n + 1)))),
        DifferentiableAt ℝ F x ∧
          ‖gradient F x‖ ≤ (a : ℝ) + (b : ℝ) * ‖x‖ := by
    filter_upwards [hgrad] with x hx
    have hx' : DifferentiableAt ℝ F x ∧
        ‖gradient F x‖ ≤ δ₁ (n + 1) z + δ₂ (n + 1) z * ‖x‖ := by
      simpa only [F] using hx
    rw [← ha, ← hbCoe] at hx'
    exact hx'
  have hbpos : 0 < (b : ℝ) := by
    rw [hbCoe]
    exact hb
  have hcut' : |s| ≤ 1 / (4 * C * (b : ℝ)) := by
    simpa only [C, hbCoe] using hcut
  have hsource :=
    source_product_centered_mgf_positive_growth_all_sizes
      (ι := ObservationCoordinate k m) (r := n + 1)
      μE C hC hLC hM2 F hlocF a b hbpos
      (by simpa only [DatasetCoordinate] using hgradF) s hcut'
  have hνSource : euclideanProductLaw (κ := Fin (n + 1)) μE = ν := by
    dsimp [ν, datasetLawOfObservation, μE]
    exact euclideanProductLaw_observation_map_eq_datasetLaw μ
  dsimp only at hsource
  rw [hνSource] at hsource
  have hM2Integral :
      (∫ x : EuclideanSpace ℝ (ObservationCoordinate k m),
        ‖x‖ ^ 2 ∂μE) =
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
  have hmean :
      (∫ D, F (datasetToEuclidean D) ∂P) =
        meanFittedLoss μ (T n) loss z (hSt.mean_integrable z) := by
    rw [meanFittedLoss]
    apply integral_congr_ae
    filter_upwards [] with D
    simp only [F, datasetOfEuclidean_datasetToEuclidean]
  have hmapMean : (∫ x, F x ∂ν) = ∫ D, F (datasetToEuclidean D) ∂P := by
    rw [show ν = P.map datasetToEuclidean by rfl]
    exact integral_map measurable_datasetToEuclidean.aemeasurable
      hlocF.continuous.aestronglyMeasurable
  have hcenter :
      (∫ x, F x ∂ν) =
        meanFittedLoss μ (T n) loss z (hSt.mean_integrable z) :=
    hmapMean.trans hmean
  let G : EuclideanSpace ℝ (DatasetCoordinate k m (n + 1)) → ℝ :=
    fun x => Real.exp (s * (F x - ∫ y, F y ∂ν))
  have hGcont : Continuous G := by
    dsimp [G]
    exact Real.continuous_exp.comp
      (continuous_const.mul (hlocF.continuous.sub continuous_const))
  have hGIntcomp : Integrable (fun D => G (datasetToEuclidean D)) P :=
    (integrable_map_measure hGcont.aestronglyMeasurable
      measurable_datasetToEuclidean.aemeasurable).1 hsource.2.1
  have hGrep :
      (fun D => G (datasetToEuclidean D)) =ᵐ[P]
        (fun D => Real.exp (s * (fittedLoss (T n) loss D z -
          meanFittedLoss μ (T n) loss z (hSt.mean_integrable z)))) := by
    filter_upwards [] with D
    dsimp [G]
    rw [show F (datasetToEuclidean D) = fittedLoss (T n) loss D z by
      simp [F, datasetOfEuclidean_datasetToEuclidean], hcenter]
  have hGInt : Integrable
      (fun D => Real.exp (s * (fittedLoss (T n) loss D z -
        meanFittedLoss μ (T n) loss z (hSt.mean_integrable z)))) P :=
    hGIntcomp.congr hGrep
  have hIntegralMap : (∫ x, G x ∂ν) = ∫ D, G (datasetToEuclidean D) ∂P := by
    rw [show ν = P.map datasetToEuclidean by rfl]
    exact integral_map measurable_datasetToEuclidean.aemeasurable
      hGcont.measurable.aestronglyMeasurable
  have hExpBound :
      (∫ D, Real.exp (s * (fittedLoss (T n) loss D z -
        meanFittedLoss μ (T n) loss z (hSt.mean_integrable z))) ∂P) ≤
        Real.exp ((2 * C * ((a : ℝ)^2 + 2 * (b : ℝ)^2 *
          ((n + 1 : ℕ) : ℝ) * (∫ x, ‖x‖ ^ 2 ∂(μ.map observationToEuclidean))) *
          s^2)) := by
    calc
      _ = ∫ D, G (datasetToEuclidean D) ∂P := integral_congr_ae hGrep.symm
      _ = ∫ x, G x ∂ν := hIntegralMap.symm
      _ ≤ _ := by exact hsource.2.2.1
  have hLogBound :
      Real.log (∫ D, Real.exp (s * (fittedLoss (T n) loss D z -
        meanFittedLoss μ (T n) loss z (hSt.mean_integrable z))) ∂P) ≤
        (2 * C * ((a : ℝ)^2 + 2 * (b : ℝ)^2 *
          ((n + 1 : ℕ) : ℝ) * (∫ x, ‖x‖ ^ 2 ∂(μ.map observationToEuclidean))) *
          s^2) := by
    rw [show (∫ D, Real.exp (s * (fittedLoss (T n) loss D z -
      meanFittedLoss μ (T n) loss z (hSt.mean_integrable z))) ∂P) =
      ∫ x, G x ∂ν by
        calc
          _ = ∫ D, G (datasetToEuclidean D) ∂P := integral_congr_ae hGrep.symm
          _ = ∫ x, G x ∂ν := hIntegralMap.symm]
    exact hsource.2.2.2
  refine ⟨hGInt, ?_, ?_⟩
  · simpa only [C, ha, hbCoe, μE, hM2Integral] using hExpBound
  · simpa only [C, ha, hbCoe, μE, hM2Integral] using hLogBound

/-- The positive-growth MGF producer feeds the exact conditional two-sided
Chernoff bound used by the source `I₁` mixture/Fubini consumer. -/
theorem standing_deleted_loss_I1_section_tail_of_positive_growth
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (loss : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T loss δ₁ δ₂ δ₃ c d)
    (hC : 0 < (observationLogSobolevConstant μ).toReal)
    (t : ℝ) (ht : 0 < t) :
    ∀ᵐ z ∂μ, 0 < δ₂ (n + 1) z →
      let P : Measure (Dataset (Observation k m) (n + 1)) :=
        Measure.pi fun _ : Fin (n + 1) => μ
      let C : ℝ := (observationLogSobolevConstant μ).toReal
      let M₂ : ℝ := ∫ y, observationNormSq y ∂μ
      let a : ℝ := δ₁ (n + 1) z
      let b : ℝ := δ₂ (n + 1) z
      let θ := thetaRate C M₂ hC.le (integral_nonneg_of_ae
        (Filter.Eventually.of_forall fun y => LOOConcentration.observationNormSq_nonneg y))
        (n + 1) (by omega) t ht a b
        (hSt.stable.delta₁_nonneg n z) (hSt.stable.delta₂_nonneg n z)
      P.real {D | fittedLoss (T n) loss D z -
        meanFittedLoss μ (T n) loss z (hSt.mean_integrable z) > t} ≤ θ ∧
      P.real {D | meanFittedLoss μ (T n) loss z
        (hSt.mean_integrable z) - fittedLoss (T n) loss D z > t} ≤ θ := by
  filter_upwards [standing_deleted_loss_centered_exp_log_bound
    μ T loss δ₁ δ₂ δ₃ c d hSt] with z hsource
  intro hb
  let P : Measure (Dataset (Observation k m) (n + 1)) :=
    Measure.pi fun _ : Fin (n + 1) => μ
  let C : ℝ := (observationLogSobolevConstant μ).toReal
  let M₂ : ℝ := ∫ y, observationNormSq y ∂μ
  let a : ℝ := δ₁ (n + 1) z
  let b : ℝ := δ₂ (n + 1) z
  let F : Dataset (Observation k m) (n + 1) → ℝ :=
    fun D => fittedLoss (T n) loss D z
  have ha : 0 ≤ a := by dsimp [a]; exact hSt.stable.delta₁_nonneg n z
  have hb0 : 0 ≤ b := by dsimp [b]; exact hSt.stable.delta₂_nonneg n z
  have hM₂ : 0 ≤ M₂ := by
    dsimp [M₂]
    exact integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun y => LOOConcentration.observationNormSq_nonneg y)
  have hmean : (∫ D, F D ∂P) =
      meanFittedLoss μ (T n) loss z (hSt.mean_integrable z) := rfl
  have hgaussian : b = 0 → ∀ s : ℝ,
      Integrable (fun D => Real.exp (s * (F D - ∫ E, F E ∂P))) P ∧
        (∫ D, Real.exp (s * (F D - ∫ E, F E ∂P)) ∂P) ≤
          Real.exp ((C * a ^ 2 / 2) * s ^ 2) := by
    intro hbzero
    have hbpos : 0 < b := by dsimp [b]; exact hb
    rw [hbzero] at hbpos
    norm_num at hbpos
  have hcutoff : 0 < b → ∀ s : ℝ, |s| ≤ 1 / (4 * C * b) →
      Integrable (fun D => Real.exp (s * (F D - ∫ E, F E ∂P))) P ∧
        (∫ D, Real.exp (s * (F D - ∫ E, F E ∂P)) ∂P) ≤
          Real.exp ((2 * C * (a ^ 2 + 2 * b ^ 2 *
            ((n + 1 : ℕ) : ℝ) * M₂)) * s ^ 2) := by
    intro hbpos s hs
    have h := hsource hbpos s hs
    constructor
    · simpa [F, P, hmean] using h.1
    · simpa only [F, P, hmean, C, M₂, a, b, Nat.cast_add, Nat.cast_one] using h.2.1
  have htails := chernoff_revision_thetaRate_of_quadraticMGF
    P F C M₂ hC hM₂ (n + 1) (by omega) t ht a b ha hb0
    hgaussian hcutoff
  simpa [P, F, C, M₂, a, b, hmean] using htails

#print axioms standing_deleted_loss_centered_exp_log_bound
#print axioms standing_deleted_loss_I1_section_tail_of_positive_growth

/-- The positive-growth conditional MGF feeds the actual finite-union and Fubini
assembly for the source `I₁` tails. -/
theorem standing_I1_positive_growth_mixture_tail
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)
    (hCpos : 0 < (observationLogSobolevConstant μ).toReal)
    (hpositive : ∀ᵐ z ∂μ, 0 < δ₂ (n+1) z)
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
  have hsection := standing_deleted_loss_I1_section_tail_of_positive_growth
    μ T L δ₁ δ₂ δ₃ c d hSt hCpos t ht
  have hcond : ∀ᵐ z ∂μ,
      PTrain.real {D | X (D,z) > t} ≤ rate z ∧
      PTrain.real {D | -X (D,z) > t} ≤ rate z := by
    filter_upwards [hsection, hpositive] with z htails hpos
    have hrateEq := thetaRate_eq_historical_of_pos C M₂ hC hM₂
      (n+1) (by omega) t ht (δ₁ (n+1) z) (δ₂ (n+1) z)
      (hSt.stable.delta₁_nonneg n z) (hSt.stable.delta₂_nonneg n z)
    have htails := htails hpos
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

#print axioms standing_I1_positive_growth_mixture_tail

end LOOConcentration.Revision
