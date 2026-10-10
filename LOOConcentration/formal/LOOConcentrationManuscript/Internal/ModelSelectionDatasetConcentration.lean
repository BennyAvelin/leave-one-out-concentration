import LOOConcentrationRevision.Results.SourceProductThetaTails
import LOOConcentrationRevision.Concentration.SourceProductMgfAllSizes
import LOOConcentrationRevision.Probability.ProductLawTransport
import LOOConcentrationRevision.Probability.ProductSecondMoment
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

private theorem original_observation_euclidean_moment
    {k m : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (hM₂ : Integrable observationNormSq μ) :
    Integrable
      (fun x : EuclideanSpace ℝ (ObservationCoordinate k m) => ‖x‖ ^ 2)
        (μ.map observationToEuclidean) ∧
    (∫ x : EuclideanSpace ℝ (ObservationCoordinate k m), ‖x‖ ^ 2
      ∂(μ.map observationToEuclidean)) = ∫ y, observationNormSq y ∂μ := by
  have hcomp : Integrable
      (fun y : Observation k m => ‖observationToEuclidean y‖ ^ 2) μ := by
    convert hM₂ using 1
    funext y
    calc
      ‖observationToEuclidean y‖ ^ 2 = observationNorm y ^ 2 := by
        rw [observationNorm_eq_euclidean]
      _ = observationNormSq y := observationNorm_sq y
  refine ⟨(integrable_map_measure (continuous_norm.pow 2).aestronglyMeasurable
    measurable_observationToEuclidean.aemeasurable).2 hcomp, ?_⟩
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

private theorem original_observation_euclidean_lsi
    {k m : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure (μ.map observationToEuclidean)]
    (hfinite : observationLogSobolevConstant μ ≠ ⊤) :
    logSobolevConstant (μ.map observationToEuclidean) ≤
      ENNReal.ofReal (observationLogSobolevConstant μ).toReal := by
  let : IsProbabilityMeasure (μ.map observationToEuclidean) :=
    Measure.isProbabilityMeasure_map measurable_observationToEuclidean.aemeasurable
  rw [ENNReal.ofReal_toReal hfinite]
  rfl

/-- Original-dataset transfer of the source quadratic-gradient tails for an
arbitrary real-valued function. The mean, event, law, LSI constant, and raw
second moment are those of the original observation product. -/
theorem original_dataset_signed_centered_tails
    {k m r : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (hr : 1 ≤ r) (G : Dataset (Observation k m) r → ℝ)
    (hfinite : observationLogSobolevConstant μ ≠ ⊤)
    (hM₂ : Integrable observationNormSq μ)
    (hloc : LocallyLipschitz (fun x : EuclideanSpace ℝ
      (DatasetCoordinate k m r) => G (datasetOfEuclidean x)))
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hgrad : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ
      (DatasetCoordinate k m r))),
        DifferentiableAt ℝ (fun x : EuclideanSpace ℝ
          (DatasetCoordinate k m r) => G (datasetOfEuclidean x)) x ∧
        ‖gradient (fun x : EuclideanSpace ℝ
          (DatasetCoordinate k m r) => G (datasetOfEuclidean x)) x‖ ≤ a + b * ‖x‖)
    (t : ℝ) (ht : 0 < t) :
    let P : Measure (Dataset (Observation k m) r) := Measure.pi fun _ : Fin r => μ
    let C : ℝ := (observationLogSobolevConstant μ).toReal
    let M₂ : ℝ := ∫ y, observationNormSq y ∂μ
    let θ := thetaRate C M₂ ENNReal.toReal_nonneg
      (integral_nonneg observationNormSq_nonneg) r hr t ht a b ha hb
    P.real {D | G D - ∫ D', G D' ∂P > t} ≤
        (if b = 0 then
          (if C * a ^ 2 = 0 then 0 else Real.exp (-(t ^ 2 / (2 * C * a ^ 2))))
         else θ) ∧
      P.real {D | ∫ D', G D' ∂P - G D > t} ≤
        (if b = 0 then
          (if C * a ^ 2 = 0 then 0 else Real.exp (-(t ^ 2 / (2 * C * a ^ 2))))
         else θ) := by
  dsimp only
  let P : Measure (Dataset (Observation k m) r) := Measure.pi fun _ : Fin r => μ
  let μE : Measure (EuclideanSpace ℝ (ObservationCoordinate k m)) :=
    μ.map observationToEuclidean
  let C : ℝ := (observationLogSobolevConstant μ).toReal
  let M₂ : ℝ := ∫ y, observationNormSq y ∂μ
  let F : EuclideanSpace ℝ (DatasetCoordinate k m r) → ℝ :=
    fun x => G (datasetOfEuclidean x)
  let : IsProbabilityMeasure μE :=
    Measure.isProbabilityMeasure_map measurable_observationToEuclidean.aemeasurable
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hCeq : (logSobolevConstant μE).toReal = C := by
    change (observationLogSobolevConstant μ).toReal = C
    rfl
  have hLC : logSobolevConstant μE ≠ ⊤ := by
    change logSobolevConstant (μ.map observationToEuclidean) ≠ ⊤
    change observationLogSobolevConstant μ ≠ ⊤ at hfinite
    exact hfinite
  have hM₂parts := original_observation_euclidean_moment μ hM₂
  have hM₂E : Integrable
      (fun x : EuclideanSpace ℝ (ObservationCoordinate k m) => ‖x‖ ^ 2) μE := by
    exact hM₂parts.1
  have hM₂eq : (∫ x : EuclideanSpace ℝ (ObservationCoordinate k m), ‖x‖ ^ 2
      ∂μE) = M₂ := by
    exact hM₂parts.2
  have hν : euclideanProductLaw (κ := Fin r) μE = P.map datasetToEuclidean := by
    change euclideanProductLaw (κ := Fin r) (μ.map observationToEuclidean) =
      datasetLawOfObservation (r := r) μ
    exact euclideanProductLaw_observation_map_eq_datasetLaw μ
  have hsrc := source_product_theta_tails (ι := ObservationCoordinate k m)
    (r := r) hr μE hLC hM₂E F hloc a b ha hb
    (by simpa only [DatasetCoordinate] using hgrad) t ht
  dsimp only at hsrc
  rw [hν] at hsrc
  have hsrc' := by simpa only [hCeq, hM₂eq] using hsrc
  have hcenter : (∫ x, F x ∂(P.map datasetToEuclidean)) = ∫ D, G D ∂P := by
    calc
      _ = ∫ D, F (datasetToEuclidean D) ∂P :=
        integral_map measurable_datasetToEuclidean.aemeasurable
          hloc.continuous.aestronglyMeasurable
      _ = ∫ D, G D ∂P := by
        apply integral_congr_ae
        filter_upwards with D
        simp [F]
  have hsetPlus : MeasurableSet {x | F x -
      ∫ y, F y ∂(P.map datasetToEuclidean) > t} :=
    measurableSet_Ioi.preimage (hloc.continuous.sub continuous_const).measurable
  have hprePlus : datasetToEuclidean ⁻¹' {x | F x -
      ∫ y, F y ∂(P.map datasetToEuclidean) > t} =
      {D | G D - ∫ D', G D' ∂P > t} := by
    ext D
    simp [F, hcenter]
  have hmassPlus : (P.map datasetToEuclidean)
      {x | F x - ∫ y, F y ∂(P.map datasetToEuclidean) > t} =
      P {D | G D - ∫ D', G D' ∂P > t} := by
    rw [Measure.map_apply measurable_datasetToEuclidean hsetPlus, hprePlus]
  have hprobPlus : P.real {D | G D - ∫ D', G D' ∂P > t} =
      (P.map datasetToEuclidean).real
        {x | F x - ∫ y, F y ∂(P.map datasetToEuclidean) > t} :=
    (congrArg ENNReal.toReal hmassPlus).symm
  have hsetMinus : MeasurableSet {x | ∫ y, F y ∂(P.map datasetToEuclidean) -
      F x > t} :=
    measurableSet_Ioi.preimage (continuous_const.sub hloc.continuous).measurable
  have hpreMinus : datasetToEuclidean ⁻¹' {x | ∫ y, F y ∂(P.map datasetToEuclidean) -
      F x > t} = {D | ∫ D', G D' ∂P - G D > t} := by
    ext D
    simp [F, hcenter]
  have hmassMinus : (P.map datasetToEuclidean)
      {x | ∫ y, F y ∂(P.map datasetToEuclidean) - F x > t} =
      P {D | ∫ D', G D' ∂P - G D > t} := by
    rw [Measure.map_apply measurable_datasetToEuclidean hsetMinus, hpreMinus]
  have hprobMinus : P.real {D | ∫ D', G D' ∂P - G D > t} =
      (P.map datasetToEuclidean).real
        {x | ∫ y, F y ∂(P.map datasetToEuclidean) - F x > t} :=
    (congrArg ENNReal.toReal hmassMinus).symm
  exact ⟨hprobPlus.trans_le hsrc'.1, hprobMinus.trans_le hsrc'.2⟩

/-- Original-dataset bounded-gradient centered MGF, with the sharp proxy
`(observationLogSobolevConstant μ).toReal * a^2`, for every real parameter. -/
theorem original_dataset_signed_centered_mgf_bounded_gradient
    {k m r : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (G : Dataset (Observation k m) r → ℝ)
    (hfinite : observationLogSobolevConstant μ ≠ ⊤)
    (hM₂ : Integrable observationNormSq μ)
    (hloc : LocallyLipschitz (fun x : EuclideanSpace ℝ
      (DatasetCoordinate k m r) => G (datasetOfEuclidean x)))
    (a : ℝ) (ha : 0 ≤ a)
    (hgrad : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ
      (DatasetCoordinate k m r))),
        DifferentiableAt ℝ (fun x : EuclideanSpace ℝ
          (DatasetCoordinate k m r) => G (datasetOfEuclidean x)) x ∧
        ‖gradient (fun x : EuclideanSpace ℝ
          (DatasetCoordinate k m r) => G (datasetOfEuclidean x)) x‖ ≤ a)
    (s : ℝ) :
    let P : Measure (Dataset (Observation k m) r) := Measure.pi fun _ : Fin r => μ
    let C : ℝ := (observationLogSobolevConstant μ).toReal
    Integrable G P ∧
    Integrable (fun D => Real.exp (s * (G D - ∫ D', G D' ∂P))) P ∧
    (∫ D, Real.exp (s * (G D - ∫ D', G D' ∂P)) ∂P) ≤
      Real.exp ((C * a ^ 2 / 2) * s ^ 2) ∧
    Real.log (∫ D, Real.exp (s * (G D - ∫ D', G D' ∂P)) ∂P) ≤
      (C * a ^ 2 / 2) * s ^ 2 := by
  dsimp only
  let P : Measure (Dataset (Observation k m) r) := Measure.pi fun _ : Fin r => μ
  let μE : Measure (EuclideanSpace ℝ (ObservationCoordinate k m)) :=
    μ.map observationToEuclidean
  let C : ℝ := (observationLogSobolevConstant μ).toReal
  let F : EuclideanSpace ℝ (DatasetCoordinate k m r) → ℝ :=
    fun x => G (datasetOfEuclidean x)
  let aN : NNReal := ⟨a, ha⟩
  have hcoeA : (aN : ℝ) = a := rfl
  let : IsProbabilityMeasure μE :=
    Measure.isProbabilityMeasure_map measurable_observationToEuclidean.aemeasurable
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hCeq : (logSobolevConstant μE).toReal = C := by
    change (observationLogSobolevConstant μ).toReal = C
    rfl
  have hLC : logSobolevConstant μE ≤ ENNReal.ofReal C := by
    exact original_observation_euclidean_lsi μ hfinite
  have hM₂parts := original_observation_euclidean_moment μ hM₂
  have hM₂E : Integrable
      (fun x : EuclideanSpace ℝ (ObservationCoordinate k m) => ‖x‖ ^ 2) μE :=
    hM₂parts.1
  have hM₂eq : (∫ x : EuclideanSpace ℝ (ObservationCoordinate k m), ‖x‖ ^ 2
      ∂μE) = ∫ y, observationNormSq y ∂μ := hM₂parts.2
  have hν : euclideanProductLaw (κ := Fin r) μE = P.map datasetToEuclidean := by
    change euclideanProductLaw (κ := Fin r) (μ.map observationToEuclidean) =
      datasetLawOfObservation (r := r) μ
    exact euclideanProductLaw_observation_map_eq_datasetLaw μ
  have hgradF : ∀ᵐ x ∂(volume : Measure
      (EuclideanSpace ℝ (Fin r × ObservationCoordinate k m))),
      DifferentiableAt ℝ F x ∧ ‖gradient F x‖ ≤ (aN : ℝ) := by
    filter_upwards [hgrad] with x hx
    simpa only [F, DatasetCoordinate, hcoeA] using hx
  have hsrc := source_product_centered_mgf_bounded_gradient_all_sizes
    (ι := ObservationCoordinate k m) (r := r) μE C hC hLC hM₂E F hloc aN
    (by simpa only [DatasetCoordinate] using hgradF) s
  dsimp only at hsrc
  rw [hν] at hsrc
  have hsrc' := by simpa only [hcoeA] using hsrc
  have hcenter : (∫ x, F x ∂(P.map datasetToEuclidean)) = ∫ D, G D ∂P := by
    calc
      _ = ∫ D, F (datasetToEuclidean D) ∂P :=
        integral_map measurable_datasetToEuclidean.aemeasurable
          hloc.continuous.aestronglyMeasurable
      _ = ∫ D, G D ∂P := by
        apply integral_congr_ae
        filter_upwards with D
        simp [F]
  have hFcomp : (fun D : Dataset (Observation k m) r => F (datasetToEuclidean D)) =ᵐ[P]
      G := by
    filter_upwards with D
    simp [F]
  have hGint : Integrable G P := by
    have hcomp : Integrable
        (fun D : Dataset (Observation k m) r => F (datasetToEuclidean D)) P :=
      (integrable_map_measure hloc.continuous.aestronglyMeasurable
        measurable_datasetToEuclidean.aemeasurable).1 hsrc'.1
    exact hcomp.congr hFcomp
  let H : EuclideanSpace ℝ (DatasetCoordinate k m r) → ℝ :=
    fun x => Real.exp (s * (F x - ∫ y, F y ∂(P.map datasetToEuclidean)))
  have hHcont : Continuous H := by
    dsimp [H]
    exact Real.continuous_exp.comp
      (continuous_const.mul (hloc.continuous.sub continuous_const))
  have hHrep : (fun D : Dataset (Observation k m) r =>
      Real.exp (s * (G D - ∫ D', G D' ∂P))) =ᵐ[P]
      fun D => H (datasetToEuclidean D) := by
    filter_upwards with D
    simp [H, F, hcenter]
  have hExpInt : Integrable
      (fun D : Dataset (Observation k m) r =>
        Real.exp (s * (G D - ∫ D', G D' ∂P))) P := by
    have hcomp : Integrable
        (fun D : Dataset (Observation k m) r => H (datasetToEuclidean D)) P :=
      (integrable_map_measure hHcont.aestronglyMeasurable
        measurable_datasetToEuclidean.aemeasurable).1 hsrc'.2.1
    exact hcomp.congr hHrep.symm
  have hIntegralMap : (∫ x, H x ∂(P.map datasetToEuclidean)) =
      ∫ D, H (datasetToEuclidean D) ∂P :=
    integral_map measurable_datasetToEuclidean.aemeasurable
      hHcont.aestronglyMeasurable
  have hIntegralEq :
      (∫ D, Real.exp (s * (G D - ∫ D', G D' ∂P)) ∂P) =
        ∫ x, H x ∂(P.map datasetToEuclidean) := by
    calc
      _ = ∫ D, H (datasetToEuclidean D) ∂P := integral_congr_ae hHrep
      _ = _ := hIntegralMap.symm
  have hExpBound :
      (∫ D, Real.exp (s * (G D - ∫ D', G D' ∂P)) ∂P) ≤
        Real.exp ((C * a ^ 2 / 2) * s ^ 2) := by
    rw [hIntegralEq]
    exact hsrc'.2.2.1
  have hLogBound :
      Real.log (∫ D, Real.exp (s * (G D - ∫ D', G D' ∂P)) ∂P) ≤
        (C * a ^ 2 / 2) * s ^ 2 := by
    rw [hIntegralEq]
    exact hsrc'.2.2.2
  exact ⟨hGint, hExpInt, hExpBound, hLogBound⟩

/-- Original-dataset positive-growth centered MGF, retaining the exact native
constant, raw second moment, cutoff, and exponent. -/
theorem original_dataset_signed_centered_mgf_positive_growth
    {k m r : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (G : Dataset (Observation k m) r → ℝ)
    (hfinite : observationLogSobolevConstant μ ≠ ⊤)
    (hM₂ : Integrable observationNormSq μ)
    (hloc : LocallyLipschitz (fun x : EuclideanSpace ℝ
      (DatasetCoordinate k m r) => G (datasetOfEuclidean x)))
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hbpos : 0 < b)
    (hgrad : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ
      (DatasetCoordinate k m r))),
        DifferentiableAt ℝ (fun x : EuclideanSpace ℝ
          (DatasetCoordinate k m r) => G (datasetOfEuclidean x)) x ∧
        ‖gradient (fun x : EuclideanSpace ℝ
          (DatasetCoordinate k m r) => G (datasetOfEuclidean x)) x‖ ≤ a + b * ‖x‖)
    (s : ℝ) (hcut : |s| ≤ 1 /
      (4 * (observationLogSobolevConstant μ).toReal * b)) :
    let P : Measure (Dataset (Observation k m) r) := Measure.pi fun _ : Fin r => μ
    let C : ℝ := (observationLogSobolevConstant μ).toReal
    let M₂ : ℝ := ∫ y, observationNormSq y ∂μ
    Integrable G P ∧
    Integrable (fun D => Real.exp (s * (G D - ∫ D', G D' ∂P))) P ∧
    (∫ D, Real.exp (s * (G D - ∫ D', G D' ∂P)) ∂P) ≤
      Real.exp ((2 * C * (a ^ 2 + 2 * b ^ 2 * (r : ℝ) * M₂)) * s ^ 2) ∧
    Real.log (∫ D, Real.exp (s * (G D - ∫ D', G D' ∂P)) ∂P) ≤
      (2 * C * (a ^ 2 + 2 * b ^ 2 * (r : ℝ) * M₂)) * s ^ 2 := by
  dsimp only
  let P : Measure (Dataset (Observation k m) r) := Measure.pi fun _ : Fin r => μ
  let μE : Measure (EuclideanSpace ℝ (ObservationCoordinate k m)) :=
    μ.map observationToEuclidean
  let C : ℝ := (observationLogSobolevConstant μ).toReal
  let M₂ : ℝ := ∫ y, observationNormSq y ∂μ
  let F : EuclideanSpace ℝ (DatasetCoordinate k m r) → ℝ :=
    fun x => G (datasetOfEuclidean x)
  let aN : NNReal := ⟨a, ha⟩
  let bN : NNReal := ⟨b, hb⟩
  have hcoeA : (aN : ℝ) = a := rfl
  have hcoeB : (bN : ℝ) = b := rfl
  let : IsProbabilityMeasure μE :=
    Measure.isProbabilityMeasure_map measurable_observationToEuclidean.aemeasurable
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hCeq : (logSobolevConstant μE).toReal = C := by
    change (observationLogSobolevConstant μ).toReal = C
    rfl
  have hLC : logSobolevConstant μE ≤ ENNReal.ofReal C := by
    exact original_observation_euclidean_lsi μ hfinite
  have hM₂parts := original_observation_euclidean_moment μ hM₂
  have hM₂E : Integrable
      (fun x : EuclideanSpace ℝ (ObservationCoordinate k m) => ‖x‖ ^ 2) μE :=
    hM₂parts.1
  have hM₂eq : (∫ x : EuclideanSpace ℝ (ObservationCoordinate k m), ‖x‖ ^ 2
      ∂μE) = M₂ := hM₂parts.2
  have hν : euclideanProductLaw (κ := Fin r) μE = P.map datasetToEuclidean := by
    change euclideanProductLaw (κ := Fin r) (μ.map observationToEuclidean) =
      datasetLawOfObservation (r := r) μ
    exact euclideanProductLaw_observation_map_eq_datasetLaw μ
  have hgradF : ∀ᵐ x ∂(volume : Measure
      (EuclideanSpace ℝ (Fin r × ObservationCoordinate k m))),
      DifferentiableAt ℝ F x ∧
        ‖gradient F x‖ ≤ (aN : ℝ) + (bN : ℝ) * ‖x‖ := by
    filter_upwards [hgrad] with x hx
    simpa only [F, DatasetCoordinate, hcoeA, hcoeB] using hx
  have hbN : 0 < (bN : ℝ) := by
    rw [hcoeB]
    exact hbpos
  have hcutN : |s| ≤ 1 / (4 * C * (bN : ℝ)) := by
    simpa only [C, hcoeB] using hcut
  have hsrc := source_product_centered_mgf_positive_growth_all_sizes
    (ι := ObservationCoordinate k m) (r := r) μE C hC hLC hM₂E F hloc
    aN bN hbN (by simpa only [DatasetCoordinate] using hgradF) s hcutN
  dsimp only at hsrc
  rw [hν] at hsrc
  have hsrc' := by simpa only [hcoeA, hcoeB, hM₂eq] using hsrc
  have hcenter : (∫ x, F x ∂(P.map datasetToEuclidean)) = ∫ D, G D ∂P := by
    calc
      _ = ∫ D, F (datasetToEuclidean D) ∂P :=
        integral_map measurable_datasetToEuclidean.aemeasurable
          hloc.continuous.aestronglyMeasurable
      _ = ∫ D, G D ∂P := by
        apply integral_congr_ae
        filter_upwards with D
        simp [F]
  have hFcomp : (fun D : Dataset (Observation k m) r => F (datasetToEuclidean D)) =ᵐ[P]
      G := by
    filter_upwards with D
    simp [F]
  have hGint : Integrable G P := by
    have hcomp : Integrable
        (fun D : Dataset (Observation k m) r => F (datasetToEuclidean D)) P :=
      (integrable_map_measure hloc.continuous.aestronglyMeasurable
        measurable_datasetToEuclidean.aemeasurable).1 hsrc'.1
    exact hcomp.congr hFcomp
  let H : EuclideanSpace ℝ (DatasetCoordinate k m r) → ℝ :=
    fun x => Real.exp (s * (F x - ∫ y, F y ∂(P.map datasetToEuclidean)))
  have hHcont : Continuous H := by
    dsimp [H]
    exact Real.continuous_exp.comp
      (continuous_const.mul (hloc.continuous.sub continuous_const))
  have hHrep : (fun D : Dataset (Observation k m) r =>
      Real.exp (s * (G D - ∫ D', G D' ∂P))) =ᵐ[P]
      fun D => H (datasetToEuclidean D) := by
    filter_upwards with D
    simp [H, F, hcenter]
  have hExpInt : Integrable
      (fun D : Dataset (Observation k m) r =>
        Real.exp (s * (G D - ∫ D', G D' ∂P))) P := by
    have hcomp : Integrable
        (fun D : Dataset (Observation k m) r => H (datasetToEuclidean D)) P :=
      (integrable_map_measure hHcont.aestronglyMeasurable
        measurable_datasetToEuclidean.aemeasurable).1 hsrc'.2.1
    exact hcomp.congr hHrep.symm
  have hIntegralMap : (∫ x, H x ∂(P.map datasetToEuclidean)) =
      ∫ D, H (datasetToEuclidean D) ∂P :=
    integral_map measurable_datasetToEuclidean.aemeasurable
      hHcont.aestronglyMeasurable
  have hIntegralEq :
      (∫ D, Real.exp (s * (G D - ∫ D', G D' ∂P)) ∂P) =
        ∫ x, H x ∂(P.map datasetToEuclidean) := by
    calc
      _ = ∫ D, H (datasetToEuclidean D) ∂P := integral_congr_ae hHrep
      _ = _ := hIntegralMap.symm
  have hExpBound :
      (∫ D, Real.exp (s * (G D - ∫ D', G D' ∂P)) ∂P) ≤
        Real.exp ((2 * C * (a ^ 2 + 2 * b ^ 2 * (r : ℝ) * M₂)) * s ^ 2) := by
    rw [hIntegralEq]
    exact hsrc'.2.2.1
  have hLogBound :
      Real.log (∫ D, Real.exp (s * (G D - ∫ D', G D' ∂P)) ∂P) ≤
        (2 * C * (a ^ 2 + 2 * b ^ 2 * (r : ℝ) * M₂)) * s ^ 2 := by
    rw [hIntegralEq]
    exact hsrc'.2.2.2
  exact ⟨hGint, hExpInt, hExpBound, hLogBound⟩

end LOOConcentration.Revision
