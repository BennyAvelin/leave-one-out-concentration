import LOOConcentrationRevision.Concentration.Chernoff
import LOOConcentration.Frozen.Foundations.LooEstimate
import LOOConcentration.Probability.DeletedTransport
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic
import LOOConcentrationRevision.Concentration.SourceProductMgfAllSizes
import LOOConcentrationRevision.Probability.ProductLawTransport
import LOOConcentrationRevision.Probability.ProductSecondMoment
import LOOConcentrationRevision.Frozen.Definitions.DatasetOfEuclidean
import LOOConcentrationRevision.Frozen.Definitions.ObservationOfEuclidean
import LOOConcentrationRevision.Frozen.Definitions.ObservationLogSobolevConstant
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import LOOConcentrationRevision.Results.StandingLossDecomposition

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

/-- Derivation from the source concentration estimates. -/
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
theorem standing_deleted_loss_centered_exp_log_bound_zero
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (loss : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T loss δ₁ δ₂ δ₃ c d) :
    ∀ᵐ z ∂μ, δ₂ (n + 1) z = 0 →
      ∀ s : ℝ,
        Integrable
          (fun D : Dataset (Observation k m) (n + 1) =>
            Real.exp (s * (fittedLoss (T n) loss D z -
              meanFittedLoss μ (T n) loss z (hSt.mean_integrable z))))
          (Measure.pi fun _ : Fin (n + 1) => μ) ∧
        (∫ D : Dataset (Observation k m) (n + 1),
          Real.exp (s * (fittedLoss (T n) loss D z -
            meanFittedLoss μ (T n) loss z (hSt.mean_integrable z)))
          ∂Measure.pi fun _ : Fin (n + 1) => μ) ≤
          Real.exp ((((observationLogSobolevConstant μ).toReal *
            (δ₁ (n + 1) z)^2) / 2) * s^2) ∧
        Real.log (∫ D : Dataset (Observation k m) (n + 1),
          Real.exp (s * (fittedLoss (T n) loss D z -
            meanFittedLoss μ (T n) loss z (hSt.mean_integrable z)))
          ∂Measure.pi fun _ : Fin (n + 1) => μ) ≤
          (((observationLogSobolevConstant μ).toReal *
            (δ₁ (n + 1) z)^2) / 2) * s^2 := by
  filter_upwards [hSt.stable.locallyLipschitz_loss n,
    hSt.stable.gradient_loss n] with z hloc hgrad
  intro hzero s
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
  have hbZero : (b : ℝ) = 0 := by rw [hbCoe, hzero]
  have hgradF0 :
      ∀ᵐ x ∂(volume : Measure
        (EuclideanSpace ℝ (DatasetCoordinate k m (n + 1)))),
        DifferentiableAt ℝ F x ∧ ‖gradient F x‖ ≤ (a : ℝ) := by
    filter_upwards [hgradF] with x hx
    refine ⟨hx.1, ?_⟩
    rw [hbZero] at hx
    simpa only [zero_mul, add_zero] using hx.2
  have hsource := source_product_centered_mgf_bounded_gradient_all_sizes
      (ι := ObservationCoordinate k m) (r := n + 1)
      μE C hC hLC hM2 F hlocF a
      (by simpa only [DatasetCoordinate] using hgradF0) s
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
        Real.exp (((C * (a : ℝ)^2 / 2) * s^2)) := by
    calc
      _ = ∫ D, G (datasetToEuclidean D) ∂P := integral_congr_ae hGrep.symm
      _ = ∫ x, G x ∂ν := hIntegralMap.symm
      _ ≤ _ := by exact hsource.2.2.1
  have hLogBound :
      Real.log (∫ D, Real.exp (s * (fittedLoss (T n) loss D z -
        meanFittedLoss μ (T n) loss z (hSt.mean_integrable z))) ∂P) ≤
        ((C * (a : ℝ)^2 / 2) * s^2) := by
    rw [show (∫ D, Real.exp (s * (fittedLoss (T n) loss D z -
      meanFittedLoss μ (T n) loss z (hSt.mean_integrable z))) ∂P) =
      ∫ x, G x ∂ν by
        calc
          _ = ∫ D, G (datasetToEuclidean D) ∂P := integral_congr_ae hGrep.symm
          _ = ∫ x, G x ∂ν := hIntegralMap.symm]
    exact hsource.2.2.2
  refine ⟨hGInt, ?_, ?_⟩
  · simpa only [C, ha] using hExpBound
  · simpa only [C, ha] using hLogBound

end LOOConcentration.Revision
