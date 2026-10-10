import LOOConcentrationManuscript.Internal.ModelSelectionSignedI1Mixture
import LOOConcentration.Frozen.Foundations.FittedLoss
import LOOConcentration.Frozen.Foundations.LooEstimate
import LOOConcentrationRevision.Geometry.CoordinateTransport
import LOOConcentration.Geometry.SmoothObservationSlope
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal

open MeasureTheory
open LOOConcentration
open LOOConcentration.Revision
open scoped ENNReal Gradient

private theorem signedI1_gaussianRate_aestronglyMeasurable
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (C t : ℝ) (a : Ω → ℝ) (ha : AEStronglyMeasurable a μ) :
    AEStronglyMeasurable
      (fun z => if C * a z ^ 2 = 0 then 0 else
        Real.exp (-(t ^ 2 / (2 * C * a z ^ 2)))) μ := by
  let g : ℝ → ℝ := fun s =>
    if C * s ^ 2 = 0 then 0 else Real.exp (-(t ^ 2 / (2 * C * s ^ 2)))
  have hg : Measurable g := by
    dsimp [g]
    have hzero : MeasurableSet {s : ℝ | C * s ^ 2 = 0} := by
      exact measurableSet_eq_fun (by fun_prop) measurable_const
    have hexp : Measurable (fun s : ℝ => Real.exp (-(t ^ 2 / (2 * C * s ^ 2)))) := by
      fun_prop
    exact Measurable.ite hzero measurable_const hexp
  exact (hg.comp_aemeasurable ha.aemeasurable).aestronglyMeasurable

private theorem signedI1_gaussianRate_bounds
    (C t a : ℝ) (hC : 0 ≤ C) :
    0 ≤ (if C * a ^ 2 = 0 then 0 else Real.exp (-(t ^ 2 / (2 * C * a ^ 2)))) ∧
      (if C * a ^ 2 = 0 then 0 else Real.exp (-(t ^ 2 / (2 * C * a ^ 2)))) ≤ 1 := by
  by_cases hzero : C * a ^ 2 = 0
  · simp [hzero]
  · have hden : 0 < 2 * C * a ^ 2 := by
      have hprod : 0 < C * a ^ 2 := lt_of_le_of_ne
        (mul_nonneg hC (sq_nonneg a)) (Ne.symm hzero)
      calc
        0 < 2 * (C * a ^ 2) := mul_pos (by norm_num) hprod
        _ = 2 * C * a ^ 2 := by ring
    have hexp : 0 ≤ Real.exp (-(t ^ 2 / (2 * C * a ^ 2))) := Real.exp_nonneg _
    have hexp' : Real.exp (-(t ^ 2 / (2 * C * a ^ 2))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact neg_nonpos.mpr (div_nonneg (sq_nonneg t) hden.le)
    simp [hzero, hexp, hexp']

private theorem modelSelection_signed_short_pointwise_mixture
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (F : Dataset (Observation k m) (n + 1) × Observation k m → ℝ)
    (hfinite : observationLogSobolevConstant μ ≠ ⊤)
    (hM₂ : Integrable observationNormSq μ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ)
    (hδ₁_nonneg : ∀ z, 0 ≤ δ₁ (n + 1) z)
    (hδ₂_nonneg : ∀ z, 0 ≤ δ₂ (n + 1) z)
    (hloc : ∀ᵐ z ∂μ, LocallyLipschitz (fun x : EuclideanSpace ℝ
      (DatasetCoordinate k m (n + 1)) => F (datasetOfEuclidean x, z)))
    (hgrad : ∀ᵐ z ∂μ, ∀ᵐ x ∂(volume : Measure
      (EuclideanSpace ℝ (DatasetCoordinate k m (n + 1)))),
        DifferentiableAt ℝ (fun y : EuclideanSpace ℝ
          (DatasetCoordinate k m (n + 1)) => F (datasetOfEuclidean y, z)) x ∧
        ‖gradient (fun y : EuclideanSpace ℝ
          (DatasetCoordinate k m (n + 1)) => F (datasetOfEuclidean y, z)) x‖ ≤
          δ₁ (n + 1) z + δ₂ (n + 1) z * ‖x‖)
    (t : ℝ) (ht : 0 < t) :
    ∀ᵐ z ∂μ,
      let Q : Measure (Dataset (Observation k m) (n + 1)) :=
        Measure.pi fun _ : Fin (n + 1) => μ
      let C : ℝ := (observationLogSobolevConstant μ).toReal
      let M₂ : ℝ := ∫ y, observationNormSq y ∂μ
      let a : ℝ := δ₁ (n + 1) z
      let b : ℝ := δ₂ (n + 1) z
      Q.real {D | F (D, z) - ∫ D', F (D', z) ∂Q > t} ≤
          (if b = 0 then
            (if C * a ^ 2 = 0 then 0 else Real.exp (-(t ^ 2 / (2 * C * a ^ 2))))
           else Revision.thetaRate C M₂ ENNReal.toReal_nonneg
             (integral_nonneg observationNormSq_nonneg) (n + 1) (by omega)
             t ht a b (hδ₁_nonneg z) (hδ₂_nonneg z)) ∧
      Q.real {D | ∫ D', F (D', z) ∂Q - F (D, z) > t} ≤
          (if b = 0 then
            (if C * a ^ 2 = 0 then 0 else Real.exp (-(t ^ 2 / (2 * C * a ^ 2))))
           else Revision.thetaRate C M₂ ENNReal.toReal_nonneg
             (integral_nonneg observationNormSq_nonneg) (n + 1) (by omega)
             t ht a b (hδ₁_nonneg z) (hδ₂_nonneg z)) := by
  filter_upwards [hloc, hgrad] with z hlocZ hgradZ
  let Q : Measure (Dataset (Observation k m) (n + 1)) :=
    Measure.pi fun _ : Fin (n + 1) => μ
  let C : ℝ := (observationLogSobolevConstant μ).toReal
  let M₂ : ℝ := ∫ y, observationNormSq y ∂μ
  let a : ℝ := δ₁ (n + 1) z
  let b : ℝ := δ₂ (n + 1) z
  let G : Dataset (Observation k m) (n + 1) → ℝ := fun D => F (D, z)
  have hlocG : LocallyLipschitz (fun x : EuclideanSpace ℝ
      (DatasetCoordinate k m (n + 1)) => G (datasetOfEuclidean x)) := by
    simpa only [G] using hlocZ
  have ha : 0 ≤ a := by exact hδ₁_nonneg z
  have hb : 0 ≤ b := by exact hδ₂_nonneg z
  have hgradG : ∀ᵐ x ∂(volume : Measure
      (EuclideanSpace ℝ (DatasetCoordinate k m (n + 1)))),
      DifferentiableAt ℝ (fun y : EuclideanSpace ℝ
        (DatasetCoordinate k m (n + 1)) => G (datasetOfEuclidean y)) x ∧
      ‖gradient (fun y : EuclideanSpace ℝ
        (DatasetCoordinate k m (n + 1)) => G (datasetOfEuclidean y)) x‖ ≤ a + b * ‖x‖ := by
    filter_upwards [hgradZ] with x hx
    simpa only [G, a, b] using hx
  have htails := original_dataset_signed_centered_tails μ (by omega) G
    hfinite hM₂ hlocG a b ha hb hgradG t ht
  dsimp only at htails
  have hcenter : (∫ D, G D ∂Q) = ∫ D', F (D', z) ∂Q := by
    rfl
  constructor
  · simpa only [G, Q, C, M₂, a, b, hcenter] using htails.1
  · simpa only [G, Q, C, M₂, a, b, hcenter] using htails.2

private theorem signedI1_rate_integrable
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (rate : Ω → ℝ) (hrate : AEStronglyMeasurable rate μ)
    (hrateNonneg : ∀ z, 0 ≤ rate z) (hrateLeOne : ∀ z, rate z ≤ 1) :
    Integrable rate μ := by
  refine (integrable_const (1 : ℝ)).mono' hrate ?_
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (hrateNonneg z)]
  exact hrateLeOne z

/-- The actual signed short-sample model-selection I₁ has the source theta
mixture bound in both directions. All concentration inputs concern the actual
signed fitted-loss difference at the original short sample size n+1. -/
theorem modelSelection_signed_i1_theta_mixture
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T₀ T₁ : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (hfinite : observationLogSobolevConstant μ ≠ ⊤)
    (hM₂ : Integrable observationNormSq μ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ)
    (hSignedMeas : Measurable (fun p : Dataset (Observation k m) (n + 1) × Observation k m =>
      fittedLoss (T₀ n) L p.1 p.2 - fittedLoss (T₁ n) L p.1 p.2))
    (hSignedIntegrable : Integrable
      (fun p : Dataset (Observation k m) (n + 1) × Observation k m =>
        fittedLoss (T₀ n) L p.1 p.2 - fittedLoss (T₁ n) L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 1) => μ).prod μ))
    (hδ₁_nonneg : ∀ z, 0 ≤ δ₁ (n + 1) z)
    (hδ₂_nonneg : ∀ z, 0 ≤ δ₂ (n + 1) z)
    (hδ₁_int : Integrable (fun z => δ₁ (n + 1) z) μ)
    (hδ₂_int : Integrable (fun z => δ₂ (n + 1) z) μ)
    (hloc : ∀ᵐ z ∂μ, LocallyLipschitz (fun x : EuclideanSpace ℝ
      (DatasetCoordinate k m (n + 1)) =>
        fittedLoss (T₀ n) L (datasetOfEuclidean x) z -
          fittedLoss (T₁ n) L (datasetOfEuclidean x) z))
    (hgrad : ∀ᵐ z ∂μ, ∀ᵐ x ∂(volume : Measure
      (EuclideanSpace ℝ (DatasetCoordinate k m (n + 1)))),
        DifferentiableAt ℝ (fun y : EuclideanSpace ℝ
          (DatasetCoordinate k m (n + 1)) =>
            fittedLoss (T₀ n) L (datasetOfEuclidean y) z -
              fittedLoss (T₁ n) L (datasetOfEuclidean y) z) x ∧
        ‖gradient (fun y : EuclideanSpace ℝ
          (DatasetCoordinate k m (n + 1)) =>
            fittedLoss (T₀ n) L (datasetOfEuclidean y) z -
              fittedLoss (T₁ n) L (datasetOfEuclidean y) z) x‖ ≤
          δ₁ (n + 1) z + δ₂ (n + 1) z * ‖x‖)
    (hExpectedQueryMeanLocallyLipschitz : LocallyLipschitz
      (fun x : EuclideanSpace ℝ (ObservationCoordinate k m) =>
        ∫ D : Dataset (Observation k m) (n + 1),
          (fittedLoss (T₀ n) L D (observationOfEuclidean x) -
            fittedLoss (T₁ n) L D (observationOfEuclidean x)) ∂
              (Measure.pi fun _ : Fin (n + 1) => μ)))
    (t : ℝ) (ht : 0 < t) :
    let P : Measure (Dataset (Observation k m) (n + 2)) :=
      Measure.pi fun _ : Fin (n + 2) => μ
    let Q : Measure (Dataset (Observation k m) (n + 1)) :=
      Measure.pi fun _ : Fin (n + 1) => μ
    let F : Dataset (Observation k m) (n + 1) × Observation k m → ℝ := fun p =>
      fittedLoss (T₀ n) L p.1 p.2 - fittedLoss (T₁ n) L p.1 p.2
    let f : Observation k m → ℝ := fun z => ∫ D, F (D, z) ∂Q
    let I₁ : Dataset (Observation k m) (n + 2) → ℝ := fun D =>
      (∑ i : Fin (n + 2), f (D i)) / (n + 2 : ℝ) -
        (looEstimate (T₀ n) L D - looEstimate (T₁ n) L D)
    let C : ℝ := (observationLogSobolevConstant μ).toReal
    let M₂ : ℝ := ∫ z, observationNormSq z ∂μ
    P.real {D | I₁ D > t} ≤ (n + 2 : ℝ) * ∫ z,
        Revision.thetaRate C M₂ ENNReal.toReal_nonneg
          (integral_nonneg observationNormSq_nonneg) (n + 1) (by omega)
          t ht (δ₁ (n + 1) z) (δ₂ (n + 1) z)
          (hδ₁_nonneg z) (hδ₂_nonneg z) ∂μ ∧
      P.real {D | -I₁ D > t} ≤ (n + 2 : ℝ) * ∫ z,
        Revision.thetaRate C M₂ ENNReal.toReal_nonneg
          (integral_nonneg observationNormSq_nonneg) (n + 1) (by omega)
          t ht (δ₁ (n + 1) z) (δ₂ (n + 1) z)
          (hδ₁_nonneg z) (hδ₂_nonneg z) ∂μ := by
  dsimp only
  let P : Measure (Dataset (Observation k m) (n + 2)) :=
    Measure.pi fun _ : Fin (n + 2) => μ
  let Q : Measure (Dataset (Observation k m) (n + 1)) :=
    Measure.pi fun _ : Fin (n + 1) => μ
  let F : Dataset (Observation k m) (n + 1) × Observation k m → ℝ := fun p =>
    fittedLoss (T₀ n) L p.1 p.2 - fittedLoss (T₁ n) L p.1 p.2
  let f : Observation k m → ℝ := fun z => ∫ D, F (D, z) ∂Q
  let I₁ : Dataset (Observation k m) (n + 2) → ℝ := fun D =>
    (∑ i : Fin (n + 2), f (D i)) / (n + 2 : ℝ) -
      (looEstimate (T₀ n) L D - looEstimate (T₁ n) L D)
  let C : ℝ := (observationLogSobolevConstant μ).toReal
  let M₂ : ℝ := ∫ z, observationNormSq z ∂μ
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hM₂nonneg : 0 ≤ M₂ := by
    dsimp [M₂]
    exact integral_nonneg observationNormSq_nonneg
  have hFmeas : Measurable F := by simpa only [F] using hSignedMeas
  have hFint : Integrable F (Q.prod μ) := by
    simpa only [F, Q] using hSignedIntegrable
  let meanEuclidean : EuclideanSpace ℝ (ObservationCoordinate k m) → ℝ := fun x =>
    ∫ D, F (D, observationOfEuclidean x) ∂Q
  have hmeanContinuous : Continuous meanEuclidean := by
    exact hExpectedQueryMeanLocallyLipschitz.continuous
  have hmeanMeas : Measurable f := by
    have heq : f = fun z => meanEuclidean (observationToEuclidean z) := by
      funext z
      simp [f, meanEuclidean, F, observationOfEuclidean_observationToEuclidean]
    rw [heq]
    exact hmeanContinuous.measurable.comp
      LOOConcentration.observationCoordinateContinuousLinearEquiv.continuous.measurable
  let theta : Observation k m → ℝ := fun z =>
    Revision.thetaRate C M₂ hC hM₂nonneg (n + 1) (by omega) t ht
      (δ₁ (n + 1) z) (δ₂ (n + 1) z) (hδ₁_nonneg z) (hδ₂_nonneg z)
  have hthetaAesm : AEStronglyMeasurable theta μ := by
    simpa only [theta] using signedI1_thetaRate_aestronglyMeasurable μ C M₂ hC hM₂nonneg
      (n + 1) (by omega) t ht (fun z => δ₁ (n + 1) z) (fun z => δ₂ (n + 1) z)
      hδ₁_int.aestronglyMeasurable hδ₂_int.aestronglyMeasurable
      (fun z => hδ₁_nonneg z) (fun z => hδ₂_nonneg z)
  have hthetaBounds (z : Observation k m) : 0 ≤ theta z ∧ theta z ≤ 1 := by
    simpa only [theta] using signedI1_thetaRate_bounds C M₂ hC hM₂nonneg
      (n + 1) (by omega) t ht (δ₁ (n + 1) z) (δ₂ (n + 1) z)
      (hδ₁_nonneg z) (hδ₂_nonneg z)
  have hthetaInt : Integrable theta μ :=
    signedI1_rate_integrable μ theta hthetaAesm (fun z => (hthetaBounds z).1)
      (fun z => (hthetaBounds z).2)
  have hpoint := modelSelection_signed_short_pointwise_mixture μ F hfinite hM₂
    δ₁ δ₂ hδ₁_nonneg hδ₂_nonneg hloc hgrad t ht
  have hpointTheta : ∀ᵐ z ∂μ,
      Q.real {D | f z - F (D, z) > t} ≤ theta z ∧
      Q.real {D | F (D, z) - f z > t} ≤ theta z := by
    filter_upwards [hpoint] with z hz
    dsimp only [Q, C, M₂] at hz
    rcases hz with ⟨hplus, hminus⟩
    have hbound :
        (if δ₂ (n + 1) z = 0 then
          (if C * (δ₁ (n + 1) z) ^ 2 = 0 then 0 else
            Real.exp (-(t ^ 2 / (2 * C * (δ₁ (n + 1) z) ^ 2))))
         else theta z) ≤ theta z := by
      by_cases hb : δ₂ (n + 1) z = 0
      · rw [if_pos hb]
        have hgauss := signedI1_gaussian_le_thetaRate C M₂ hC hM₂nonneg
          (n + 1) (by omega) t ht (δ₁ (n + 1) z) (hδ₁_nonneg z)
        simpa only [theta, hb] using hgauss
      · rw [if_neg hb]
    have hplus' : Q.real {D | f z - F (D, z) > t} ≤ theta z := by
      simpa only [f] using hminus.trans hbound
    have hminus' : Q.real {D | F (D, z) - f z > t} ≤ theta z := by
      simpa only [f] using hplus.trans hbound
    exact ⟨hplus', hminus'⟩
  have hcore := signedI1_two_sided_mixture_of_pointwise μ F hFmeas hFint
    hmeanMeas theta hthetaInt (fun z => (hthetaBounds z).1) t hpointTheta
  have hloo (D : Dataset (Observation k m) (n + 2)) :
      looEstimate (T₀ n) L D - looEstimate (T₁ n) L D =
        (∑ i : Fin (n + 2), F (deleteAt D i, D i)) / (n + 2 : ℝ) := by
    simp only [looEstimate, fittedLoss, F]
    rw [Finset.sum_sub_distrib, sub_div]
  have hIeq (D : Dataset (Observation k m) (n + 2)) :
      I₁ D = (∑ i : Fin (n + 2), f (D i)) / (n + 2 : ℝ) -
        (∑ i : Fin (n + 2), F (deleteAt D i, D i)) / (n + 2 : ℝ) := by
    dsimp [I₁]
    rw [hloo]
  have hplus : P.real {D | I₁ D > t} ≤ (n + 2 : ℝ) * ∫ z, theta z ∂μ := by
    have hcorePlus := hcore.2.1
    simpa only [I₁, hIeq, Q, P, f, F] using hcorePlus
  have hminus : P.real {D | -I₁ D > t} ≤ (n + 2 : ℝ) * ∫ z, theta z ∂μ := by
    have hcoreMinus := hcore.2.2
    simpa only [I₁, hIeq, Q, P, f, F] using hcoreMinus
  exact ⟨hplus, hminus⟩

/-- When the source growth coefficient vanishes everywhere, the actual signed
short-sample model-selection I₁ has the sharp Gaussian mixture in both
directions. -/
theorem modelSelection_signed_i1_gaussian_zero_growth_mixture
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T₀ T₁ : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (hfinite : observationLogSobolevConstant μ ≠ ⊤)
    (hM₂ : Integrable observationNormSq μ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ)
    (hSignedMeas : Measurable (fun p : Dataset (Observation k m) (n + 1) × Observation k m =>
      fittedLoss (T₀ n) L p.1 p.2 - fittedLoss (T₁ n) L p.1 p.2))
    (hSignedIntegrable : Integrable
      (fun p : Dataset (Observation k m) (n + 1) × Observation k m =>
        fittedLoss (T₀ n) L p.1 p.2 - fittedLoss (T₁ n) L p.1 p.2)
      ((Measure.pi fun _ : Fin (n + 1) => μ).prod μ))
    (hδ₁_nonneg : ∀ z, 0 ≤ δ₁ (n + 1) z)
    (hδ₂_zero : ∀ z, δ₂ (n + 1) z = 0)
    (hδ₁_int : Integrable (fun z => δ₁ (n + 1) z) μ)
    (hloc : ∀ᵐ z ∂μ, LocallyLipschitz (fun x : EuclideanSpace ℝ
      (DatasetCoordinate k m (n + 1)) =>
        fittedLoss (T₀ n) L (datasetOfEuclidean x) z -
          fittedLoss (T₁ n) L (datasetOfEuclidean x) z))
    (hgrad : ∀ᵐ z ∂μ, ∀ᵐ x ∂(volume : Measure
      (EuclideanSpace ℝ (DatasetCoordinate k m (n + 1)))),
        DifferentiableAt ℝ (fun y : EuclideanSpace ℝ
          (DatasetCoordinate k m (n + 1)) =>
            fittedLoss (T₀ n) L (datasetOfEuclidean y) z -
              fittedLoss (T₁ n) L (datasetOfEuclidean y) z) x ∧
        ‖gradient (fun y : EuclideanSpace ℝ
          (DatasetCoordinate k m (n + 1)) =>
            fittedLoss (T₀ n) L (datasetOfEuclidean y) z -
              fittedLoss (T₁ n) L (datasetOfEuclidean y) z) x‖ ≤
          δ₁ (n + 1) z + δ₂ (n + 1) z * ‖x‖)
    (hExpectedQueryMeanLocallyLipschitz : LocallyLipschitz
      (fun x : EuclideanSpace ℝ (ObservationCoordinate k m) =>
        ∫ D : Dataset (Observation k m) (n + 1),
          (fittedLoss (T₀ n) L D (observationOfEuclidean x) -
            fittedLoss (T₁ n) L D (observationOfEuclidean x)) ∂
              (Measure.pi fun _ : Fin (n + 1) => μ)))
    (t : ℝ) (ht : 0 < t) :
    let P : Measure (Dataset (Observation k m) (n + 2)) :=
      Measure.pi fun _ : Fin (n + 2) => μ
    let Q : Measure (Dataset (Observation k m) (n + 1)) :=
      Measure.pi fun _ : Fin (n + 1) => μ
    let F : Dataset (Observation k m) (n + 1) × Observation k m → ℝ := fun p =>
      fittedLoss (T₀ n) L p.1 p.2 - fittedLoss (T₁ n) L p.1 p.2
    let f : Observation k m → ℝ := fun z => ∫ D, F (D, z) ∂Q
    let I₁ : Dataset (Observation k m) (n + 2) → ℝ := fun D =>
      (∑ i : Fin (n + 2), f (D i)) / (n + 2 : ℝ) -
        (looEstimate (T₀ n) L D - looEstimate (T₁ n) L D)
    let C : ℝ := (observationLogSobolevConstant μ).toReal
    P.real {D | I₁ D > t} ≤ (n + 2 : ℝ) * ∫ z,
        (if C * (δ₁ (n + 1) z) ^ 2 = 0 then 0 else
          Real.exp (-(t ^ 2 / (2 * C * (δ₁ (n + 1) z) ^ 2)))) ∂μ ∧
      P.real {D | -I₁ D > t} ≤ (n + 2 : ℝ) * ∫ z,
        (if C * (δ₁ (n + 1) z) ^ 2 = 0 then 0 else
          Real.exp (-(t ^ 2 / (2 * C * (δ₁ (n + 1) z) ^ 2)))) ∂μ := by
  dsimp only
  let P : Measure (Dataset (Observation k m) (n + 2)) :=
    Measure.pi fun _ : Fin (n + 2) => μ
  let Q : Measure (Dataset (Observation k m) (n + 1)) :=
    Measure.pi fun _ : Fin (n + 1) => μ
  let F : Dataset (Observation k m) (n + 1) × Observation k m → ℝ := fun p =>
    fittedLoss (T₀ n) L p.1 p.2 - fittedLoss (T₁ n) L p.1 p.2
  let f : Observation k m → ℝ := fun z => ∫ D, F (D, z) ∂Q
  let I₁ : Dataset (Observation k m) (n + 2) → ℝ := fun D =>
    (∑ i : Fin (n + 2), f (D i)) / (n + 2 : ℝ) -
      (looEstimate (T₀ n) L D - looEstimate (T₁ n) L D)
  let C : ℝ := (observationLogSobolevConstant μ).toReal
  let M₂ : ℝ := ∫ z, observationNormSq z ∂μ
  let gaussianRate : Observation k m → ℝ := fun z =>
    if C * (δ₁ (n + 1) z) ^ 2 = 0 then 0 else
      Real.exp (-(t ^ 2 / (2 * C * (δ₁ (n + 1) z) ^ 2)))
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hM₂nonneg : 0 ≤ M₂ := by
    dsimp [M₂]
    exact integral_nonneg observationNormSq_nonneg
  have hFmeas : Measurable F := by simpa only [F] using hSignedMeas
  have hFint : Integrable F (Q.prod μ) := by
    simpa only [F, Q] using hSignedIntegrable
  let meanEuclidean : EuclideanSpace ℝ (ObservationCoordinate k m) → ℝ := fun x =>
    ∫ D, F (D, observationOfEuclidean x) ∂Q
  have hmeanContinuous : Continuous meanEuclidean :=
    hExpectedQueryMeanLocallyLipschitz.continuous
  have hmeanMeas : Measurable f := by
    have heq : f = fun z => meanEuclidean (observationToEuclidean z) := by
      funext z
      simp [f, meanEuclidean, F, observationOfEuclidean_observationToEuclidean]
    rw [heq]
    exact hmeanContinuous.measurable.comp
      LOOConcentration.observationCoordinateContinuousLinearEquiv.continuous.measurable
  have hgaussianAesm : AEStronglyMeasurable gaussianRate μ := by
    simpa only [gaussianRate] using signedI1_gaussianRate_aestronglyMeasurable μ C t
      (fun z => δ₁ (n + 1) z) hδ₁_int.aestronglyMeasurable
  have hgaussianBounds (z : Observation k m) : 0 ≤ gaussianRate z ∧
      gaussianRate z ≤ 1 := by
    simpa only [gaussianRate] using signedI1_gaussianRate_bounds C t
      (δ₁ (n + 1) z) hC
  have hgaussianInt : Integrable gaussianRate μ :=
    signedI1_rate_integrable μ gaussianRate hgaussianAesm
      (fun z => (hgaussianBounds z).1) (fun z => (hgaussianBounds z).2)
  have hδ₂_nonneg : ∀ z, 0 ≤ δ₂ (n + 1) z := by
    intro z
    rw [hδ₂_zero z]
  have hpoint := modelSelection_signed_short_pointwise_mixture μ F hfinite hM₂
    δ₁ δ₂ hδ₁_nonneg hδ₂_nonneg hloc hgrad t ht
  have hpointGaussian : ∀ᵐ z ∂μ,
      Q.real {D | f z - F (D, z) > t} ≤ gaussianRate z ∧
      Q.real {D | F (D, z) - f z > t} ≤ gaussianRate z := by
    filter_upwards [hpoint] with z hz
    have hfirst : Q.real {D | f z - F (D, z) > t} ≤ gaussianRate z := by
      simpa only [Q, f, C, M₂, hδ₂_zero z, if_true, gaussianRate] using hz.2
    have hsecond : Q.real {D | F (D, z) - f z > t} ≤ gaussianRate z := by
      simpa only [Q, f, C, M₂, hδ₂_zero z, if_true, gaussianRate] using hz.1
    exact ⟨hfirst, hsecond⟩
  have hcore := signedI1_two_sided_mixture_of_pointwise μ F hFmeas hFint
    hmeanMeas gaussianRate hgaussianInt (fun z => (hgaussianBounds z).1) t hpointGaussian
  have hloo (D : Dataset (Observation k m) (n + 2)) :
      looEstimate (T₀ n) L D - looEstimate (T₁ n) L D =
        (∑ i : Fin (n + 2), F (deleteAt D i, D i)) / (n + 2 : ℝ) := by
    simp only [looEstimate, fittedLoss, F]
    rw [Finset.sum_sub_distrib, sub_div]
  have hIeq (D : Dataset (Observation k m) (n + 2)) :
      I₁ D = (∑ i : Fin (n + 2), f (D i)) / (n + 2 : ℝ) -
        (∑ i : Fin (n + 2), F (deleteAt D i, D i)) / (n + 2 : ℝ) := by
    dsimp [I₁]
    rw [hloo]
  have hplus : P.real {D | I₁ D > t} ≤ (n + 2 : ℝ) * ∫ z, gaussianRate z ∂μ := by
    have hcorePlus := hcore.2.1
    simpa only [I₁, hIeq, Q, P, f, F] using hcorePlus
  have hminus : P.real {D | -I₁ D > t} ≤ (n + 2 : ℝ) * ∫ z, gaussianRate z ∂μ := by
    have hcoreMinus := hcore.2.2
    simpa only [I₁, hIeq, Q, P, f, F] using hcoreMinus
  simpa only [gaussianRate] using And.intro hplus hminus

end LOOConcentration.Manuscript.Internal
