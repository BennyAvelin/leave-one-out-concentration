import LOOConcentrationRevision.Results.SourceProductThetaTails
import LOOConcentrationRevision.Concentration.ExpectedRiskGradientConsumer
import LOOConcentrationRevision.Frozen.Definitions.LooRiskL1_characterization
import LOOConcentration.Results.Decomposition
import LOOConcentration.Probability.ProductConditionalRisk
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

private theorem sharp_gaussian_le_theta_I3
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
  simp only [if_neg hCa, thetaRate, if_neg hC0,
    zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_mul, add_zero,
    if_neg (ne_of_gt ha2)]
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  apply div_le_div_of_nonneg_left (sq_nonneg t) (by positivity)
  nlinarith [mul_pos hCp ha2]

/-- The actual full-fit conditional risk's strict centered tails, supplied by
    the frozen source quadratic-gradient corollary on Euclidean samples. -/
theorem standing_conditional_risk_theta_tails_all_dimensions
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)
    (t : ℝ) (ht : 0 < t) :
    let P := Measure.pi fun _ : Fin (n + 2) => μ
    let H := looRiskL1 μ (T (n + 1)) L (hSt.stable.integrable_full n)
    let Hmean := ∫ D, H D ∂P
    let C := (observationLogSobolevConstant μ).toReal
    let M₂ := ∫ z, observationNormSq z ∂μ
    let a := ∫ z, δ₁ (n + 2) z ∂μ
    let b := ∫ z, δ₂ (n + 2) z ∂μ
    let θ := thetaRate C M₂ ENNReal.toReal_nonneg
      (integral_nonneg_of_ae (ae_of_all _ fun z => observationNormSq_nonneg z))
      (n + 2) (by omega) t ht a b
      (integral_nonneg fun z => hSt.stable.delta₁_nonneg (n + 1) z)
      (integral_nonneg fun z => hSt.stable.delta₂_nonneg (n + 1) z)
    P.real {D | H D - Hmean > t} ≤ θ ∧
      P.real {D | Hmean - H D > t} ≤ θ := by
  dsimp only
  let P : Measure (Dataset (Observation k m) (n + 2)) := Measure.pi fun _ => μ
  let ν := datasetLawOfObservation (r := n + 2) μ
  let hf := hSt.stable.integrable_full n
  let H : Dataset (Observation k m) (n + 2) → ℝ := fun D =>
    looRiskL1 μ (T (n + 1)) L hf D
  let Hmean : ℝ := ∫ D, H D ∂P
  let C : ℝ := (observationLogSobolevConstant μ).toReal
  let M₂ : ℝ := ∫ z, observationNormSq z ∂μ
  let a : ℝ := ∫ z, δ₁ (n + 2) z ∂μ
  let b : ℝ := ∫ z, δ₂ (n + 2) z ∂μ
  let θ := thetaRate C M₂ ENNReal.toReal_nonneg
      (integral_nonneg_of_ae (ae_of_all _ fun z => observationNormSq_nonneg z))
      (n + 2) (by omega) t ht a b
      (integral_nonneg fun z => hSt.stable.delta₁_nonneg (n + 1) z)
      (integral_nonneg fun z => hSt.stable.delta₂_nonneg (n + 1) z)
  let F : EuclideanSpace ℝ (DatasetCoordinate k m (n + 2)) → ℝ := fun x =>
    ∫ z, fittedLoss (T (n + 1)) L (datasetOfEuclidean x) z ∂μ
  let μE : Measure (EuclideanSpace ℝ (ObservationCoordinate k m)) :=
    μ.map observationToEuclidean
  let : IsProbabilityMeasure μE :=
    Measure.isProbabilityMeasure_map measurable_observationToEuclidean.aemeasurable
  let νE := euclideanProductLaw (κ := Fin (n + 2)) μE
  have hν : ν = P.map datasetToEuclidean := rfl
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hM₂ : 0 ≤ M₂ := by
    dsimp [M₂]
    exact integral_nonneg_of_ae (ae_of_all _ fun z => observationNormSq_nonneg z)
  have ha : 0 ≤ a := by
    dsimp [a]
    exact integral_nonneg fun z => hSt.stable.delta₁_nonneg (n + 1) z
  have hb : 0 ≤ b := by
    dsimp [b]
    exact integral_nonneg fun z => hSt.stable.delta₂_nonneg (n + 1) z
  have hcomp : Integrable
      (fun z : Observation k m => ‖observationToEuclidean z‖ ^ 2) μ := by
    convert hSt.second_moment using 1
    funext z
    calc
      ‖observationToEuclidean z‖ ^ 2 = observationNorm z ^ 2 := by
        rw [observationNorm_eq_euclidean]
      _ = observationNormSq z := observationNorm_sq z
  have hM2 : Integrable
      (fun x : EuclideanSpace ℝ (ObservationCoordinate k m) => ‖x‖ ^ 2) μE :=
    (integrable_map_measure (continuous_norm.pow 2).aestronglyMeasurable
      measurable_observationToEuclidean.aemeasurable).2 hcomp
  have hM2eq : (∫ x : EuclideanSpace ℝ (ObservationCoordinate k m), ‖x‖ ^ 2 ∂μE) = M₂ := by
    change (∫ x : EuclideanSpace ℝ (ObservationCoordinate k m), ‖x‖ ^ 2
      ∂(μ.map observationToEuclidean)) = _
    have hnorm : Continuous
        (fun x : EuclideanSpace ℝ (ObservationCoordinate k m) => ‖x‖ ^ 2) :=
      continuous_norm.pow 2
    rw [integral_map measurable_observationToEuclidean.aemeasurable
      hnorm.aestronglyMeasurable]
    congr 1
    funext z
    rw [← observationNorm_eq_euclidean, observationNorm_sq]
  have hsource := standing_expected_full_loss_gradient
    (n := n) μ T L δ₁ δ₂ δ₃ c d hSt
  have hlocal : LocallyLipschitz F := by simpa only [F] using hsource.2.1
  have hFmeas : Measurable F := hlocal.continuous.measurable
  have hsrc := source_product_theta_tails (n + 2) (by omega) μE
    hSt.lsi.ne hM2 F hlocal a b ha hb hsource.2.2 t ht
  have hsrc' :
      ν.real {x | F x - ∫ y, F y ∂ν > t} ≤
          (if b = 0 then
            (if C * a ^ 2 = 0 then 0 else Real.exp (-(t ^ 2 / (2 * C * a ^ 2))))
           else θ) ∧
      ν.real {x | ∫ y, F y ∂ν - F x > t} ≤
          (if b = 0 then
            (if C * a ^ 2 = 0 then 0 else Real.exp (-(t ^ 2 / (2 * C * a ^ 2))))
           else θ) := by
    dsimp only at hsrc
    simpa [ν, νE, μE, F, DatasetCoordinate, C, M₂, a, b, θ,
      observationLogSobolevConstant, hM2eq,
      euclideanProductLaw_observation_map_eq_datasetLaw μ,
      Nat.cast_add, Nat.cast_ofNat] using hsrc
  have hsharp :
      (if b = 0 then
        (if C * a ^ 2 = 0 then 0 else Real.exp (-(t ^ 2 / (2 * C * a ^ 2))))
       else θ) ≤ θ := by
    by_cases hb0 : b = 0
    · simpa [hb0, θ] using
        (sharp_gaussian_le_theta_I3 C M₂ hC hM₂ (n + 2) (by omega) t ht a ha)
    · simp only [if_neg hb0, le_rfl]
  have hchar := looRiskL1_characterization μ (T (n + 1)) L hf
  have hcond := LOOConcentration.condExp_fst_prod_eq_integral_test_of_integrable
    P μ (fun p : Dataset (Observation k m) (n + 2) × Observation k m =>
      fittedLoss (T (n + 1)) L p.1 p.2) hf
  have hpair : (fun p : Dataset (Observation k m) (n + 2) × Observation k m => H p.1) =ᵐ[
      P.prod μ] (fun p => ∫ z, fittedLoss (T (n + 1)) L p.1 z ∂μ) := hchar.symm.trans hcond
  have hsections : ∀ᵐ D ∂P,
      (fun z => H D) =ᵐ[μ]
        (fun _ : Observation k m => ∫ z, fittedLoss (T (n + 1)) L D z ∂μ) :=
    Measure.ae_ae_of_ae_prod hpair
  have hrep : H =ᵐ[P] fun D => F (datasetToEuclidean D) := by
    filter_upwards [hsections] with D hD
    have hi : (∫ z, H D ∂μ) =
        ∫ z, (∫ w, fittedLoss (T (n + 1)) L D w ∂μ) ∂μ := integral_congr_ae hD
    have hpoint : H D = ∫ w, fittedLoss (T (n + 1)) L D w ∂μ := by
      simpa using hi
    simpa [F, datasetOfEuclidean_datasetToEuclidean] using hpoint
  have hmeanF : (∫ x, F x ∂ν) = ∫ D, F (datasetToEuclidean D) ∂P := by
    rw [hν]
    exact integral_map measurable_datasetToEuclidean.aemeasurable
      hFmeas.aestronglyMeasurable
  have hmeanH : Hmean = ∫ x, F x ∂ν := by
    dsimp [Hmean]
    exact (integral_congr_ae hrep).trans hmeanF.symm
  have hcenter : (fun D => H D - Hmean) =ᵐ[P]
      fun D => F (datasetToEuclidean D) - ∫ x, F x ∂ν := by
    filter_upwards [hrep] with D hD
    rw [hD, hmeanH]
  have hcenterNeg : (fun D => Hmean - H D) =ᵐ[P]
      fun D => ∫ x, F x ∂ν - F (datasetToEuclidean D) := by
    filter_upwards [hcenter] with D hD
    linarith
  have hupperMap : P.real {D | H D - Hmean > t} =
      ν.real {x | F x - ∫ y, F y ∂ν > t} := by
    calc
      _ = P.real {D | F (datasetToEuclidean D) - ∫ y, F y ∂ν > t} :=
        measureReal_congr (by
          filter_upwards [hcenter] with D hD
          exact propext (by
            change H D - Hmean > t ↔ F (datasetToEuclidean D) - ∫ y, F y ∂ν > t
            rw [hD]))
      _ = (P.map datasetToEuclidean).real {x | F x - ∫ y, F y ∂ν > t} := by
        unfold Measure.real
        have hmap : (P.map datasetToEuclidean) {x | F x - ∫ y, F y ∂ν > t} =
            P {D | F (datasetToEuclidean D) - ∫ y, F y ∂ν > t} := by
          change (P.map datasetToEuclidean)
              ((fun x => F x - ∫ y, F y ∂ν) ⁻¹' Set.Ioi t) = _
          calc
            _ = P (datasetToEuclidean ⁻¹'
                ((fun x => F x - ∫ y, F y ∂ν) ⁻¹' Set.Ioi t)) :=
              Measure.map_apply measurable_datasetToEuclidean
                (measurableSet_Ioi.preimage (hFmeas.sub measurable_const))
            _ = P {D | F (datasetToEuclidean D) - ∫ y, F y ∂ν > t} := by
              rfl
        exact congrArg ENNReal.toReal hmap.symm
      _ = ν.real {x | F x - ∫ y, F y ∂ν > t} := by
        exact (congrArg (fun q : Measure _ => q.real
          {x | F x - ∫ y, F y ∂ν > t}) hν).symm
  have hlowerMap : P.real {D | Hmean - H D > t} =
      ν.real {x | ∫ y, F y ∂ν - F x > t} := by
    calc
      _ = P.real {D | ∫ y, F y ∂ν - F (datasetToEuclidean D) > t} :=
        measureReal_congr (by
          filter_upwards [hcenterNeg] with D hD
          exact propext (by
            change Hmean - H D > t ↔ ∫ y, F y ∂ν - F (datasetToEuclidean D) > t
            rw [hD]))
      _ = (P.map datasetToEuclidean).real {x | ∫ y, F y ∂ν - F x > t} := by
        unfold Measure.real
        have hmap : (P.map datasetToEuclidean) {x | ∫ y, F y ∂ν - F x > t} =
            P {D | ∫ y, F y ∂ν - F (datasetToEuclidean D) > t} := by
          change (P.map datasetToEuclidean)
              ((fun x => (∫ y, F y ∂ν) - F x) ⁻¹' Set.Ioi t) = _
          calc
            _ = P (datasetToEuclidean ⁻¹'
                ((fun x => (∫ y, F y ∂ν) - F x) ⁻¹' Set.Ioi t)) :=
              Measure.map_apply measurable_datasetToEuclidean
                (measurableSet_Ioi.preimage (measurable_const.sub hFmeas))
            _ = P {D | ∫ y, F y ∂ν - F (datasetToEuclidean D) > t} := by
              rfl
        exact congrArg ENNReal.toReal hmap.symm
      _ = ν.real {x | ∫ y, F y ∂ν - F x > t} := by
        exact (congrArg (fun q : Measure _ => q.real
          {x | ∫ y, F y ∂ν - F x > t}) hν).symm
  have hHtails : P.real {D | H D - Hmean > t} ≤ θ ∧
      P.real {D | Hmean - H D > t} ≤ θ := by
    exact ⟨hupperMap ▸ hsrc'.1.trans hsharp, hlowerMap ▸ hsrc'.2.trans hsharp⟩
  exact hHtails

end LOOConcentration.Revision
