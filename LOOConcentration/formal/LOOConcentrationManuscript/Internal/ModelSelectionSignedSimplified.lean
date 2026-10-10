import LOOConcentrationManuscript.Internal.ModelSelectionSignedI1Mixture
import LOOConcentrationManuscript.Internal.ModelSelectionSignedI1MixtureConsumer
import LOOConcentrationManuscript.Internal.ModelSelectionSignedI1UniformMgfConsumer
import LOOConcentrationManuscript.Internal.ModelSelectionSignedShortCenteringConsumer
import LOOConcentrationManuscript.Internal.ModelSelectionSignedActualTailSplit
import LOOConcentrationManuscript.Internal.ModelSelectionSignedRiskConcentration
import LOOConcentrationManuscript.Internal.ModelSelectionSignedValidationConcentrationConsumer
import LOOConcentration.Concentration.SubGaussianSum
import LOOConcentrationRevision.FunctionalInequalities.Rademacher
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal

open MeasureTheory Filter
open LOOConcentration
open LOOConcentration.Revision
open scoped Gradient

private theorem signed_simplified_query_local_bridge
    {k m : ℕ} (f : Observation k m → ℝ)
    (h : LocallyLipschitz (fun x : EuclideanSpace ℝ (ObservationCoordinate k m) =>
      f (Revision.observationOfEuclidean x))) : LocallyLipschitz f := by
  have he : LocallyLipschitz
      (observationToEuclidean : Observation k m → EuclideanSpace ℝ (ObservationCoordinate k m)) :=
    observationCoordinateContinuousLinearEquiv.toContinuousLinearMap.lipschitz.locallyLipschitz
  have hh := h.comp he
  convert hh using 1
  funext z
  simp only [Function.comp_apply, observationOfEuclidean_observationToEuclidean]

private theorem signed_simplified_gaussian_rate_aestronglyMeasurable
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (C t : ℝ) (a : Ω → ℝ) (ha : AEStronglyMeasurable a μ) :
    AEStronglyMeasurable
      (fun z => if C * a z ^ 2 = 0 then 0 else
        Real.exp (-(t ^ 2 / (2 * C * a z ^ 2)))) μ := by
  let g : ℝ → ℝ := fun s =>
    if C * s ^ 2 = 0 then 0 else Real.exp (-(t ^ 2 / (2 * C * s ^ 2)))
  have hg : Measurable g := by
    dsimp [g]
    have hzero : MeasurableSet {s : ℝ | C * s ^ 2 = 0} :=
      measurableSet_eq_fun (by fun_prop) measurable_const
    have hexp : Measurable (fun s : ℝ => Real.exp (-(t ^ 2 / (2 * C * s ^ 2)))) := by
      fun_prop
    exact Measurable.ite hzero measurable_const hexp
  exact (hg.comp_aemeasurable ha.aemeasurable).aestronglyMeasurable

private theorem signed_simplified_gaussian_rate_bounds
    (C t a : ℝ) (hC : 0 ≤ C) :
    0 ≤ (if C * a ^ 2 = 0 then 0 else Real.exp (-(t ^ 2 / (2 * C * a ^ 2)))) ∧
      (if C * a ^ 2 = 0 then 0 else Real.exp (-(t ^ 2 / (2 * C * a ^ 2)))) ≤ 1 := by
  by_cases hzero : C * a ^ 2 = 0
  · simp [hzero]
  · have hden : 0 < 2 * C * a ^ 2 := by
      have hprod : 0 < C * a ^ 2 := lt_of_le_of_ne
        (mul_nonneg hC (sq_nonneg a)) (Ne.symm hzero)
      nlinarith
    have hexp : 0 ≤ Real.exp (-(t ^ 2 / (2 * C * a ^ 2))) := Real.exp_nonneg _
    have hexp' : Real.exp (-(t ^ 2 / (2 * C * a ^ 2))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact neg_nonpos.mpr (div_nonneg (sq_nonneg t) hden.le)
    simp [hzero, hexp, hexp']

private theorem signed_simplified_rate_integrable
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (rate : Ω → ℝ) (hrate : AEStronglyMeasurable rate μ)
    (hrateNonneg : ∀ z, 0 ≤ rate z) (hrateLeOne : ∀ z, rate z ≤ 1) :
    Integrable rate μ := by
  refine (integrable_const (1 : ℝ)).mono' hrate ?_
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (hrateNonneg z)]
  exact hrateLeOne z

private theorem signed_simplified_measureReal_mono_ae
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {s t : Set α} (hst : ∀ᵐ x ∂μ, x ∈ s → x ∈ t) :
    μ.real s ≤ μ.real t := by
  rw [Measure.real, Measure.real]
  exact ENNReal.toReal_mono (by finiteness) (measure_mono_ae hst)

private theorem signed_simplified_strict_tail_of_hasSubgaussianMGF
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hX : ProbabilityTheory.HasSubgaussianMGF X (NNReal.mk K hK) P)
    {t : ℝ} (ht : 0 < t) :
    P.real {x | X x > t} ≤
      (if K = 0 then 0 else Real.exp (-(t ^ 2 / (2 * K)))) := by
  by_cases hK0 : K = 0
  · have hzero : ProbabilityTheory.HasSubgaussianMGF X 0 P := by
      simpa [hK0] using hX
    have hae : X =ᵐ[P] 0 := hzero.ae_eq_zero_of_hasSubgaussianMGF_zero
    have hsub : ∀ᵐ x ∂P, x ∈ {x | X x > t} → x ∈ (∅ : Set Ω) := by
      filter_upwards [hae] with x hx hxt
      rw [hx] at hxt
      exact (not_lt_of_ge ht.le hxt).elim
    simpa [hK0] using signed_simplified_measureReal_mono_ae hsub
  · have htail := hX.measure_ge_le (show 0 ≤ t by linarith)
    have hstrict : {x | X x > t} ⊆ {x | t ≤ X x} := by
      intro x hx
      change t < X x at hx
      exact le_of_lt hx
    have hreal : (NNReal.mk K hK : ℝ) = K := rfl
    have hexp : Real.exp (-t ^ 2 / (2 * (NNReal.mk K hK : ℝ))) =
        Real.exp (-(t ^ 2 / (2 * K))) := by
      congr 1
      rw [hreal]
      ring
    calc
      P.real {x | X x > t} ≤ P.real {x | t ≤ X x} := measureReal_mono hstrict
      _ ≤ Real.exp (-t ^ 2 / (2 * (NNReal.mk K hK : ℝ))) := htail
      _ = Real.exp (-(t ^ 2 / (2 * K))) := hexp
      _ = if K = 0 then 0 else Real.exp (-(t ^ 2 / (2 * K))) := by rw [if_neg hK0]

section ActualSignedSimplified

variable {k m n : ℕ}
variable (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
variable (T₀ T₁ : ∀ r : ℕ, Estimator k m (r + 1))
variable (L : Responses m → Responses m → ℝ)
variable (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℝ)
variable (hδ₃_nonneg : 0 ≤ δ₃)
variable (hFullMeas : Measurable (fun p : Dataset (Observation k m) (n + 2) ×
  Observation k m => fittedLoss (T₀ (n + 1)) L p.1 p.2 -
    fittedLoss (T₁ (n + 1)) L p.1 p.2))
variable (hδ₁_full_nonneg : ∀ z, 0 ≤ δ₁ (n + 2) z)
variable (hδ₂_full_nonneg : ∀ z, 0 ≤ δ₂ (n + 2) z)
variable (hδ₁_full_int : Integrable (fun z => δ₁ (n + 2) z) μ)
variable (hδ₂_full_int : Integrable (fun z => δ₂ (n + 2) z) μ)
variable (hzero : Integrable (fun z =>
  fittedLoss (T₀ (n + 1)) L (0 : Dataset (Observation k m) (n + 2)) z -
    fittedLoss (T₁ (n + 1)) L (0 : Dataset (Observation k m) (n + 2)) z) μ)
variable (hFullLoc : ∀ᵐ z ∂μ, LocallyLipschitz (fun x : EuclideanSpace ℝ
  (DatasetCoordinate k m (n + 2)) =>
    fittedLoss (T₀ (n + 1)) L (Revision.datasetOfEuclidean x) z -
      fittedLoss (T₁ (n + 1)) L (Revision.datasetOfEuclidean x) z))
variable (hFullGrad : ∀ᵐ z ∂μ, ∀ᵐ x ∂(volume : Measure
  (EuclideanSpace ℝ (DatasetCoordinate k m (n + 2)))),
  DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (DatasetCoordinate k m (n + 2)) =>
    fittedLoss (T₀ (n + 1)) L (Revision.datasetOfEuclidean y) z -
      fittedLoss (T₁ (n + 1)) L (Revision.datasetOfEuclidean y) z) x ∧
  ‖gradient (fun y : EuclideanSpace ℝ (DatasetCoordinate k m (n + 2)) =>
    fittedLoss (T₀ (n + 1)) L (Revision.datasetOfEuclidean y) z -
      fittedLoss (T₁ (n + 1)) L (Revision.datasetOfEuclidean y) z) x‖ ≤
    δ₁ (n + 2) z + δ₂ (n + 2) z * ‖x‖)
variable (hfinite : observationLogSobolevConstant μ ≠ ⊤)
variable (hM₂ : Integrable observationNormSq μ)
variable (hf₀ : Integrable (fun p : Dataset (Observation k m) (n + 2) ×
  Observation k m => fittedLoss (T₀ (n + 1)) L p.1 p.2)
  ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ))
variable (hf₁ : Integrable (fun p : Dataset (Observation k m) (n + 2) ×
  Observation k m => fittedLoss (T₁ (n + 1)) L p.1 p.2)
  ((Measure.pi fun _ : Fin (n + 2) => μ).prod μ))
variable (hShortMeas : Measurable (fun p : Dataset (Observation k m) (n + 1) ×
  Observation k m => fittedLoss (T₀ n) L p.1 p.2 - fittedLoss (T₁ n) L p.1 p.2))
variable (hδ₁_short_nonneg : ∀ z, 0 ≤ δ₁ (n + 1) z)
variable (hδ₂_short_nonneg : ∀ z, 0 ≤ δ₂ (n + 1) z)
variable (hδ₁_short_int : Integrable (fun z => δ₁ (n + 1) z) μ)
variable (hδ₂_short_int : Integrable (fun z => δ₂ (n + 1) z) μ)
variable (hShortLoc : ∀ᵐ z ∂μ, LocallyLipschitz (fun x : EuclideanSpace ℝ
  (DatasetCoordinate k m (n + 1)) =>
    fittedLoss (T₀ n) L (datasetOfEuclidean x) z - fittedLoss (T₁ n) L (datasetOfEuclidean x) z))
variable (hShortGrad : ∀ᵐ z ∂μ, ∀ᵐ x ∂(volume : Measure
  (EuclideanSpace ℝ (DatasetCoordinate k m (n + 1)))),
  DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (DatasetCoordinate k m (n + 1)) =>
    fittedLoss (T₀ n) L (datasetOfEuclidean y) z - fittedLoss (T₁ n) L (datasetOfEuclidean y) z) x ∧
  ‖gradient (fun y : EuclideanSpace ℝ (DatasetCoordinate k m (n + 1)) =>
    fittedLoss (T₀ n) L (datasetOfEuclidean y) z - fittedLoss (T₁ n) L (datasetOfEuclidean y) z) x‖ ≤
    δ₁ (n + 1) z + δ₂ (n + 1) z * ‖x‖)
variable (hHeld : ∀ i : Fin (n + 2),
  Integrable (fun D : Dataset (Observation k m) (n + 2) =>
    fittedLoss (T₀ n) L (deleteAt D i) (D i) -
      fittedLoss (T₁ n) L (deleteAt D i) (D i))
    (Measure.pi fun _ : Fin (n + 2) => μ))
variable (hBias : ∀ i : Fin (n + 2),
  |(∫ D : Dataset (Observation k m) (n + 2),
      (fittedLoss (T₀ n) L (deleteAt D i) (D i) -
        fittedLoss (T₁ n) L (deleteAt D i) (D i))
      ∂Measure.pi fun _ : Fin (n + 2) => μ) -
    (∫ p : Dataset (Observation k m) (n + 2) × Observation k m,
      (fittedLoss (T₀ (n + 1)) L p.1 p.2 -
        fittedLoss (T₁ (n + 1)) L p.1 p.2)
      ∂(Measure.pi fun _ : Fin (n + 2) => μ).prod μ)| ≤ δ₃)
variable (hQueryInt : ∀ z : Observation k m,
  Integrable (fun D : Dataset (Observation k m) (n + 1) =>
    fittedLoss (T₀ n) L D z - fittedLoss (T₁ n) L D z)
    (Measure.pi fun _ : Fin (n + 1) => μ))
variable (c : ℝ) (hc : 0 ≤ c)
variable (hQueryLip : LipschitzWith (NNReal.mk c hc)
  (modelSelectionSignedExpectedMeanQuery μ T₀ T₁ L hQueryInt))
variable (hδ₂_short_zero : ∀ z, δ₂ (n + 1) z = 0)
variable (hδ₂_full_zero : ∀ z, δ₂ (n + 2) z = 0)

include μ T₀ T₁ L δ₁ δ₂ δ₃ hδ₃_nonneg hFullMeas hδ₁_full_nonneg hδ₂_full_nonneg
  hδ₁_full_int hδ₂_full_int hzero hFullLoc hFullGrad hfinite hM₂ hf₀ hf₁ hShortMeas
  hδ₁_short_nonneg hδ₁_short_int hShortLoc hShortGrad
  hHeld hBias hQueryInt c hc hQueryLip hδ₂_short_zero hδ₂_full_zero

/-- The two strict tails for the actual signed model-selection error, with the
sharp nonuniform Gaussian mixture and the two sharp full-sample Gaussian terms.
Every zero variance term is zero by definition. -/
theorem modelSelection_actual_signed_simplified_nonuniform_tails
    (ε : ℝ) (hε : 3 * δ₃ < ε) :
    let P : Measure (Dataset (Observation k m) (n + 2)) := Measure.pi fun _ : Fin (n + 2) => μ
    let R : Dataset (Observation k m) (n + 2) → ℝ := fun D =>
      Revision.looRiskL1 μ (T₀ (n + 1)) L hf₀ D - Revision.looRiskL1 μ (T₁ (n + 1)) L hf₁ D
    let E : Dataset (Observation k m) (n + 2) → ℝ := fun D =>
      looEstimate (T₀ n) L D - looEstimate (T₁ n) L D
    let C := (observationLogSobolevConstant μ).toReal
    let t := (ε - δ₃) / 3
    let gaussian : ℝ → ℝ := fun v =>
      if v = 0 then 0 else Real.exp (-(t ^ 2 / (2 * v)))
    P.real {D | R D - E D > ε} ≤
        (n + 2 : ℝ) * ∫ z, gaussian (C * (δ₁ (n + 1) z) ^ 2) ∂μ +
          gaussian (C * (c / Real.sqrt (n + 2 : ℝ)) ^ 2) +
            gaussian (C * (∫ z, δ₁ (n + 2) z ∂μ) ^ 2) ∧
      P.real {D | E D - R D > ε} ≤
        (n + 2 : ℝ) * ∫ z, gaussian (C * (δ₁ (n + 1) z) ^ 2) ∂μ +
          gaussian (C * (c / Real.sqrt (n + 2 : ℝ)) ^ 2) +
            gaussian (C * (∫ z, δ₁ (n + 2) z ∂μ) ^ 2) := by
  dsimp only
  let P : Measure (Dataset (Observation k m) (n + 2)) := Measure.pi fun _ => μ
  let Q : Measure (Dataset (Observation k m) (n + 1)) := Measure.pi fun _ => μ
  let F : Dataset (Observation k m) (n + 1) × Observation k m → ℝ := fun p =>
    fittedLoss (T₀ n) L p.1 p.2 - fittedLoss (T₁ n) L p.1 p.2
  let f : Observation k m → ℝ := fun z => ∫ D, F (D, z) ∂Q
  let V : Dataset (Observation k m) (n + 2) → ℝ := fun D =>
    (∑ i : Fin (n + 2), f (D i)) / (n + 2 : ℝ)
  let E : Dataset (Observation k m) (n + 2) → ℝ := fun D =>
    looEstimate (T₀ n) L D - looEstimate (T₁ n) L D
  let R : Dataset (Observation k m) (n + 2) → ℝ := fun D =>
    Revision.looRiskL1 μ (T₀ (n + 1)) L hf₀ D - Revision.looRiskL1 μ (T₁ (n + 1)) L hf₁ D
  let I₁ : Dataset (Observation k m) (n + 2) → ℝ := fun D => V D - E D
  let I₂ : Dataset (Observation k m) (n + 2) → ℝ := fun D => (∫ E, V E ∂P) - V D
  let I₃ : Dataset (Observation k m) (n + 2) → ℝ := fun D => R D - ∫ E, R E ∂P
  let C : ℝ := (observationLogSobolevConstant μ).toReal
  let t : ℝ := (ε - δ₃) / 3
  let gaussian : ℝ → ℝ := fun v => if v = 0 then 0 else Real.exp (-(t ^ 2 / (2 * v)))
  have ht : 0 < t := by dsimp [t]; linarith
  have hShort := modelSelection_actual_signed_short_centering μ T₀ T₁ L hShortMeas hHeld
  have hQueryLoc : LocallyLipschitz (modelSelectionSignedExpectedMeanQuery μ T₀ T₁ L hQueryInt) :=
    hQueryLip.locallyLipschitz
  have hMeanLoc : LocallyLipschitz (modelSelectionSignedExpectedMean μ T₀ T₁ L hQueryInt) :=
    signed_simplified_query_local_bridge
      (modelSelectionSignedExpectedMean μ T₀ T₁ L hQueryInt) hQueryLoc
  have hMeanMeas : Measurable (fun z => ∫ D, F (D, z) ∂Q) := by
    have hcont : Continuous (modelSelectionSignedExpectedMean μ T₀ T₁ L hQueryInt) :=
      hMeanLoc.continuous
    change Measurable (modelSelectionSignedExpectedMean μ T₀ T₁ L hQueryInt)
    exact hcont.measurable
  have hRateMeas : AEStronglyMeasurable
      (fun z => gaussian (C * (δ₁ (n + 1) z) ^ 2)) μ := by
    simpa only [gaussian, mul_assoc] using
      signed_simplified_gaussian_rate_aestronglyMeasurable μ C t
        (δ₁ (n + 1)) hδ₁_short_int.aestronglyMeasurable
  have hRateBounds (z : Observation k m) :
      0 ≤ gaussian (C * (δ₁ (n + 1) z) ^ 2) ∧
        gaussian (C * (δ₁ (n + 1) z) ^ 2) ≤ 1 := by
    simpa only [gaussian, mul_assoc] using signed_simplified_gaussian_rate_bounds C t
      (δ₁ (n + 1) z) ENNReal.toReal_nonneg
  have hRateInt : Integrable (fun z => gaussian (C * (δ₁ (n + 1) z) ^ 2)) μ :=
    signed_simplified_rate_integrable μ _ hRateMeas
      (fun z => (hRateBounds z).1) (fun z => (hRateBounds z).2)
  have hPoint : ∀ᵐ z ∂μ,
      Q.real {D | (∫ D', F (D', z) ∂Q) - F (D, z) > t} ≤
        gaussian (C * (δ₁ (n + 1) z) ^ 2) ∧
      Q.real {D | F (D, z) - (∫ D', F (D', z) ∂Q) > t} ≤
        gaussian (C * (δ₁ (n + 1) z) ^ 2) := by
    filter_upwards [hShortLoc, hShortGrad] with z hlocz hgradz
    let G : Dataset (Observation k m) (n + 1) → ℝ := fun D => F (D, z)
    have hlocG : LocallyLipschitz (fun x : EuclideanSpace ℝ
        (DatasetCoordinate k m (n + 1)) => G (datasetOfEuclidean x)) := by
      simpa only [G, F] using hlocz
    have hgradG : ∀ᵐ x ∂(volume : Measure
        (EuclideanSpace ℝ (DatasetCoordinate k m (n + 1)))),
        DifferentiableAt ℝ (fun y : EuclideanSpace ℝ
          (DatasetCoordinate k m (n + 1)) => G (datasetOfEuclidean y)) x ∧
        ‖gradient (fun y : EuclideanSpace ℝ
          (DatasetCoordinate k m (n + 1)) => G (datasetOfEuclidean y)) x‖ ≤
          δ₁ (n + 1) z := by
      filter_upwards [hgradz] with x hx
      refine ⟨?_, ?_⟩
      · simpa only [G, F] using hx.1
      · simpa only [G, F, hδ₂_short_zero z, zero_mul, add_zero] using hx.2
    have htails := Revision.original_dataset_signed_centered_tails μ (by omega) G
      hfinite hM₂ hlocG (δ₁ (n + 1) z) 0 (hδ₁_short_nonneg z) le_rfl
      (by simpa only [zero_mul, add_zero] using hgradG) t ht
    dsimp only at htails
    constructor
    · simpa only [G, F, Q, C, zero_mul, add_zero, if_true, gaussian, mul_assoc] using htails.2
    · simpa only [G, F, Q, C, zero_mul, add_zero, if_true, gaussian, mul_assoc] using htails.1
  have hI₁mix := signedI1_two_sided_mixture_of_pointwise μ F
    (by simpa only [F] using hShortMeas) (by simpa only [F, Q] using hShort.1)
    hMeanMeas (fun z => gaussian (C * (δ₁ (n + 1) z) ^ 2)) hRateInt
    (fun z => (hRateBounds z).1) t hPoint
  have hI₁eq (D : Dataset (Observation k m) (n + 2)) :
      I₁ D = (∑ i : Fin (n + 2), ∫ D', F (D', D i) ∂Q) / (n + 2 : ℝ) -
        (∑ i : Fin (n + 2), F (deleteAt D i, D i)) / (n + 2 : ℝ) := by
    dsimp only [I₁, V, f, E, F, Q]
    simp only [looEstimate, fittedLoss, Finset.sum_sub_distrib, sub_div]
  dsimp only at hI₁mix
  have hI₁plus : P.real {D | I₁ D > t} ≤
      (n + 2 : ℝ) * ∫ z, gaussian (C * (δ₁ (n + 1) z) ^ 2) ∂μ := by
    have hevent : {D | I₁ D > t} = {D | (∑ i : Fin (n + 2),
        ∫ D', F (D', D i) ∂Q) / (n + 2 : ℝ) -
          (∑ i : Fin (n + 2), F (deleteAt D i, D i)) / (n + 2 : ℝ) > t} := by
      ext D
      simp only [Set.mem_ofPred_eq, hI₁eq]
    rw [hevent]
    exact hI₁mix.2.1
  have hI₁minus : P.real {D | -I₁ D > t} ≤
      (n + 2 : ℝ) * ∫ z, gaussian (C * (δ₁ (n + 1) z) ^ 2) ∂μ := by
    have hevent : {D | -I₁ D > t} = {D | -((∑ i : Fin (n + 2),
        ∫ D', F (D', D i) ∂Q) / (n + 2 : ℝ) -
          (∑ i : Fin (n + 2), F (deleteAt D i, D i)) / (n + 2 : ℝ)) > t} := by
      ext D
      simp only [Set.mem_ofPred_eq, hI₁eq]
    rw [hevent]
    exact hI₁mix.2.2
  have hQueryGrad : ∀ᵐ x ∂(volume : Measure
      (EuclideanSpace ℝ (ObservationCoordinate k m))),
      DifferentiableAt ℝ (modelSelectionSignedExpectedMeanQuery μ T₀ T₁ L hQueryInt) x ∧
      ‖gradient (modelSelectionSignedExpectedMeanQuery μ T₀ T₁ L hQueryInt) x‖ ≤ c := by
    have h := Revision.lipschitzWith_ae_differentiableAt_gradient_norm_le hQueryLip
    simpa only [NNReal.coe_mk] using h
  have hQueryGrad0 : ∀ᵐ x ∂(volume : Measure
      (EuclideanSpace ℝ (ObservationCoordinate k m))),
      DifferentiableAt ℝ (modelSelectionSignedExpectedMeanQuery μ T₀ T₁ L hQueryInt) x ∧
      ‖gradient (modelSelectionSignedExpectedMeanQuery μ T₀ T₁ L hQueryInt) x‖ ≤ c + 0 * ‖x‖ := by
    filter_upwards [hQueryGrad] with x hx
    exact ⟨hx.1, by simpa only [zero_mul, add_zero] using hx.2⟩
  have hI₂tails := modelSelection_signed_validation_average_centered_tails
    μ T₀ T₁ L hQueryInt c 0 hc le_rfl hfinite hM₂ hQueryLoc hQueryGrad0 t ht
  have hVG (D : Dataset (Observation k m) (n + 2)) :
      modelSelectionSignedExpectedValidationAverage μ T₀ T₁ L hQueryInt D = V D := by
    dsimp only [modelSelectionSignedExpectedValidationAverage, originalQueryValidationAverage,
      modelSelectionSignedExpectedMean, V, f, Q, F]
    rw [div_eq_mul_inv]
    simp only [Nat.cast_add, Nat.cast_ofNat]
    ring
  dsimp only at hI₂tails
  simp only [hVG] at hI₂tails
  have hI₂plus : P.real {D | I₂ D > t} ≤
      gaussian (C * (c / Real.sqrt (n + 2 : ℝ)) ^ 2) := by
    simpa only [I₂, P, C, gaussian, zero_div, if_pos rfl, if_true, ← mul_assoc] using hI₂tails.2
  have hI₂minus : P.real {D | -I₂ D > t} ≤
      gaussian (C * (c / Real.sqrt (n + 2 : ℝ)) ^ 2) := by
    simpa only [I₂, P, C, gaussian, zero_div, if_pos rfl, if_true, neg_sub, ← mul_assoc] using hI₂tails.1
  have hδ₂fullZeroAE : ∀ᵐ z ∂μ, δ₂ (n + 2) z = 0 :=
    Filter.Eventually.of_forall hδ₂_full_zero
  have hδ₂fullIntegral : (∫ z, δ₂ (n + 2) z ∂μ) = 0 :=
    (integral_congr_ae hδ₂fullZeroAE).trans (integral_zero _ _)
  have hI₃tails := modelSelection_actual_signed_risk_centered_tails μ T₀ T₁ L δ₁ δ₂
    hFullMeas hδ₁_full_nonneg hδ₂_full_nonneg hδ₁_full_int hδ₂_full_int hzero
    hFullLoc hFullGrad hfinite hM₂ hf₀ hf₁ t ht
  dsimp only at hI₃tails
  have hI₃plus : P.real {D | I₃ D > t} ≤
      gaussian (C * (∫ z, δ₁ (n + 2) z ∂μ) ^ 2) := by
    simpa only [I₃, R, P, C, gaussian, hδ₂fullIntegral, if_pos rfl, if_true, zero_mul, add_zero,
      ← mul_assoc] using hI₃tails.1
  have hI₃minus : P.real {D | -I₃ D > t} ≤
      gaussian (C * (∫ z, δ₁ (n + 2) z ∂μ) ^ 2) := by
    simpa only [I₃, R, P, C, gaussian, hδ₂fullIntegral, if_pos rfl, if_true, neg_sub, zero_mul, add_zero,
      ← mul_assoc] using hI₃tails.2
  have hSplit := modelSelection_actual_signed_main_and_simplified_tail_split
    μ T₀ T₁ L hf₀ hf₁ hShortMeas hHeld δ₃ hBias ε
  dsimp only at hSplit
  constructor
  · exact hSplit.2.1.trans (add_le_add (add_le_add hI₁plus hI₂plus) hI₃plus)
  · exact hSplit.2.2.trans (add_le_add (add_le_add hI₁minus hI₂minus) hI₃minus)

omit hδ₁_short_nonneg hδ₁_short_int in
/-- Uniform two-sided and absolute tails for the actual signed model-selection
error. The three centered terms are combined by Hölder under their common
product law; no independence between them is assumed. -/
lemma modelSelection_actual_signed_simplified_uniform_tails
    (a : NNReal) (ha : ∀ᵐ z ∂μ, δ₁ (n + 1) z ≤ (a : ℝ))
    (t : ℝ) (ht : 0 < t) :
    let P : Measure (Dataset (Observation k m) (n + 2)) := Measure.pi fun _ : Fin (n + 2) => μ
    let R : Dataset (Observation k m) (n + 2) → ℝ := fun D =>
      Revision.looRiskL1 μ (T₀ (n + 1)) L hf₀ D - Revision.looRiskL1 μ (T₁ (n + 1)) L hf₁ D
    let E : Dataset (Observation k m) (n + 2) → ℝ := fun D =>
      looEstimate (T₀ n) L D - looEstimate (T₁ n) L D
    let C := (observationLogSobolevConstant μ).toReal
    let b := (a : ℝ) + c / Real.sqrt (n + 2 : ℝ) + ∫ z, δ₁ (n + 2) z ∂μ
    let K := C * b ^ 2
    let gaussian := if K = 0 then 0 else Real.exp (-(t ^ 2 / (2 * K)))
    P.real {D | R D - E D > δ₃ + t} ≤ gaussian ∧
      P.real {D | E D - R D > δ₃ + t} ≤ gaussian ∧
        P.real {D | |R D - E D| > δ₃ + t} ≤ 2 * gaussian := by
  dsimp only
  let P : Measure (Dataset (Observation k m) (n + 2)) := Measure.pi fun _ : Fin (n + 2) => μ
  let Q : Measure (Dataset (Observation k m) (n + 1)) := Measure.pi fun _ : Fin (n + 1) => μ
  let F : Dataset (Observation k m) (n + 1) × Observation k m → ℝ := fun p =>
    fittedLoss (T₀ n) L p.1 p.2 - fittedLoss (T₁ n) L p.1 p.2
  let f : Observation k m → ℝ := fun z => ∫ D, F (D, z) ∂Q
  let V : Dataset (Observation k m) (n + 2) → ℝ := fun D =>
    (∑ i : Fin (n + 2), f (D i)) / (n + 2 : ℝ)
  let E : Dataset (Observation k m) (n + 2) → ℝ := fun D =>
    looEstimate (T₀ n) L D - looEstimate (T₁ n) L D
  let R : Dataset (Observation k m) (n + 2) → ℝ := fun D =>
    Revision.looRiskL1 μ (T₀ (n + 1)) L hf₀ D - Revision.looRiskL1 μ (T₁ (n + 1)) L hf₁ D
  let I₁ : Dataset (Observation k m) (n + 2) → ℝ := fun D => V D - E D
  let I₂ : Dataset (Observation k m) (n + 2) → ℝ := fun D => (∫ D', V D' ∂P) - V D
  let I₃ : Dataset (Observation k m) (n + 2) → ℝ := fun D => R D - ∫ D', R D' ∂P
  let bias : ℝ := (∫ D, R D ∂P) - ∫ D, V D ∂P
  let C : ℝ := (observationLogSobolevConstant μ).toReal
  let s₂ : NNReal := ⟨c / Real.sqrt (n + 2 : ℝ), div_nonneg hc (Real.sqrt_nonneg _)⟩
  let s₃ : NNReal := ⟨∫ z, δ₁ (n + 2) z ∂μ, integral_nonneg hδ₁_full_nonneg⟩
  let Cnn : NNReal := ⟨C, ENNReal.toReal_nonneg⟩
  let scales : NNReal := a + s₂ + s₃
  let b : ℝ := (a : ℝ) + c / Real.sqrt (n + 2 : ℝ) + ∫ z, δ₁ (n + 2) z ∂μ
  let K : ℝ := C * b ^ 2
  let gaussian : ℝ := if K = 0 then 0 else Real.exp (-(t ^ 2 / (2 * K)))
  have hShort := modelSelection_actual_signed_short_centering μ T₀ T₁ L hShortMeas hHeld
  have hQueryLoc : LocallyLipschitz (modelSelectionSignedExpectedMeanQuery μ T₀ T₁ L hQueryInt) :=
    hQueryLip.locallyLipschitz
  have hMeanLoc : LocallyLipschitz (modelSelectionSignedExpectedMean μ T₀ T₁ L hQueryInt) :=
    signed_simplified_query_local_bridge
      (modelSelectionSignedExpectedMean μ T₀ T₁ L hQueryInt) hQueryLip.locallyLipschitz
  have hQueryGrad : ∀ᵐ x ∂(volume : Measure
      (EuclideanSpace ℝ (ObservationCoordinate k m))),
      DifferentiableAt ℝ (modelSelectionSignedExpectedMeanQuery μ T₀ T₁ L hQueryInt) x ∧
      ‖gradient (modelSelectionSignedExpectedMeanQuery μ T₀ T₁ L hQueryInt) x‖ ≤ c := by
    have h := Revision.lipschitzWith_ae_differentiableAt_gradient_norm_le hQueryLip
    simpa only [NNReal.coe_mk] using h
  have hQueryGrad0 : ∀ᵐ x ∂(volume : Measure
      (EuclideanSpace ℝ (ObservationCoordinate k m))),
      DifferentiableAt ℝ (modelSelectionSignedExpectedMeanQuery μ T₀ T₁ L hQueryInt) x ∧
      ‖gradient (modelSelectionSignedExpectedMeanQuery μ T₀ T₁ L hQueryInt) x‖ ≤ c + 0 * ‖x‖ := by
    filter_upwards [hQueryGrad] with x hx
    exact ⟨hx.1, by simpa only [zero_mul, add_zero] using hx.2⟩
  have hShortI1Eq (D : Dataset (Observation k m) (n + 2)) :
      I₁ D = (∑ i : Fin (n + 2),
        (f (D i) - F (deleteAt D i, D i))) / (n + 2 : ℝ) := by
    dsimp only [I₁, V, f, E, F, Q]
    simp only [looEstimate, fittedLoss, Finset.sum_sub_distrib, sub_div]
  let I₁alt : Dataset (Observation k m) (n + 2) → ℝ := fun D =>
    (∑ i : Fin (n + 2), (f (D i) - F (deleteAt D i, D i))) / (n + 2 : ℝ)
  have hShortI1Eq' (D : Dataset (Observation k m) (n + 2)) : I₁ D = I₁alt D := by
    simpa only [I₁alt] using hShortI1Eq D
  have hMeanMeas : Measurable (fun z => ∫ D, F (D, z) ∂Q) := by
    have hcont : Continuous (modelSelectionSignedExpectedMean μ T₀ T₁ L hQueryInt) :=
      hMeanLoc.continuous
    change Measurable (modelSelectionSignedExpectedMean μ T₀ T₁ L hQueryInt)
    exact hcont.measurable
  have hI₁raw (s : ℝ) := modelSelection_actual_signed_i1_bounded_consumer
    μ T₀ T₁ L δ₁ δ₂ hfinite hM₂ (by simpa only [F] using hShortMeas)
    (by simpa only [F, Q] using hShort.1) hMeanLoc hShortLoc
    (by
      filter_upwards [hShortGrad] with z hz
      filter_upwards [hz] with x hx
      exact ⟨hx.1, by simpa only [F, hδ₂_short_zero z, zero_mul, add_zero] using hx.2⟩)
    (a : ℝ) a.property ha (Filter.Eventually.of_forall hδ₂_short_zero) s
  have hI₁raw' (s : ℝ) :
      Integrable (fun D => Real.exp (s * I₁alt D)) P ∧
        (∫ D, Real.exp (s * I₁alt D) ∂P) ≤
          Real.exp ((C * (a : ℝ) ^ 2 / 2) * s ^ 2) := by
    simpa only [P, Q, F, f, I₁alt, Nat.cast_add, Nat.cast_ofNat] using hI₁raw s
  have hI₁mgfAlt : ProbabilityTheory.HasSubgaussianMGF I₁alt
      (NNReal.mk (C * (a : ℝ) ^ 2) (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))) P := by
    constructor
    · intro s
      exact (hI₁raw' s).1
    · intro s
      change (∫ D, Real.exp (s * I₁alt D) ∂P) ≤
        Real.exp ((C * (a : ℝ) ^ 2) * s ^ 2 / 2)
      have hcoef : (C * (a : ℝ) ^ 2 / 2) * s ^ 2 =
          (C * (a : ℝ) ^ 2) * s ^ 2 / 2 := by ring
      exact (hI₁raw' s).2.trans_eq (congrArg Real.exp hcoef)
  have hI₁proxy :
      LOOConcentration.Concentration.subGaussianProxy Cnn a =
        NNReal.mk (C * (a : ℝ) ^ 2)
          (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)) := by
    apply NNReal.coe_injective
    rw [LOOConcentration.Concentration.coe_subGaussianProxy]
    change C * (a : ℝ) ^ 2 = C * (a : ℝ) ^ 2
    rfl
  have hI₁mgf : ProbabilityTheory.HasSubgaussianMGF I₁
      (LOOConcentration.Concentration.subGaussianProxy Cnn a) P := by
    have h := hI₁mgfAlt.congr (Filter.Eventually.of_forall fun D => (hShortI1Eq' D).symm)
    simpa only [hI₁proxy] using h
  have hVG (D : Dataset (Observation k m) (n + 2)) :
      modelSelectionSignedExpectedValidationAverage μ T₀ T₁ L hQueryInt D = V D := by
    dsimp only [modelSelectionSignedExpectedValidationAverage, originalQueryValidationAverage,
      modelSelectionSignedExpectedMean, V, f, Q, F]
    rw [div_eq_mul_inv]
    simp only [Nat.cast_add, Nat.cast_ofNat]
    ring
  have hVal := modelSelection_signed_validation_average_hasSubgaussianMGF_of_zero_growth
    μ T₀ T₁ L hQueryInt c 0 hc le_rfl rfl hfinite hM₂ hQueryLoc hQueryGrad0
  have hVal' : ProbabilityTheory.HasSubgaussianMGF
      (fun D => V D - ∫ D', V D' ∂P)
      (NNReal.mk (C * (c / Real.sqrt (n + 2 : ℝ)) ^ 2)
        (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))) P := by
    have hmean : (∫ D, modelSelectionSignedExpectedValidationAverage μ T₀ T₁ L hQueryInt D ∂P) =
        ∫ D, V D ∂P := integral_congr_ae (Filter.Eventually.of_forall hVG)
    have hcenter :
        (fun D => modelSelectionSignedExpectedValidationAverage μ T₀ T₁ L hQueryInt D -
          ∫ D', modelSelectionSignedExpectedValidationAverage μ T₀ T₁ L hQueryInt D' ∂P) =ᵐ[P]
        (fun D => V D - ∫ D', V D' ∂P) := by
      filter_upwards [Filter.Eventually.of_forall hVG] with D hD
      rw [hD, hmean]
    exact hVal.congr hcenter
  have hI₂mgf := hVal'.neg
  have hδ₂fullZeroAE : ∀ᵐ z ∂μ, δ₂ (n + 2) z = 0 :=
    Filter.Eventually.of_forall hδ₂_full_zero
  have hI₃mgf := modelSelection_actual_signed_risk_hasSubgaussianMGF
    μ T₀ T₁ L δ₁ δ₂ hFullMeas hδ₁_full_nonneg hδ₂_full_nonneg
    hδ₁_full_int hδ₂_full_int hzero hFullLoc hFullGrad hfinite hM₂ hf₀ hf₁ hδ₂fullZeroAE
  have hI₂proxy :
      LOOConcentration.Concentration.subGaussianProxy Cnn s₂ =
        NNReal.mk (C * (c / Real.sqrt (n + 2 : ℝ)) ^ 2)
          (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)) := by
    apply NNReal.coe_injective
    rw [LOOConcentration.Concentration.coe_subGaussianProxy]
    change C * (c / Real.sqrt (n + 2 : ℝ)) ^ 2 =
      C * (c / Real.sqrt (n + 2 : ℝ)) ^ 2
    rfl
  have hI₂mgf' : ProbabilityTheory.HasSubgaussianMGF I₂
      (LOOConcentration.Concentration.subGaussianProxy Cnn s₂) P := by
    have hmean : (∫ D, V D ∂P) - ∫ D, V D ∂P = 0 := by ring
    have hcenter : (fun D => -(V D - ∫ D', V D' ∂P)) =ᵐ[P] I₂ := by
      filter_upwards with D
      simp only [I₂]
      ring
    have hneg := hI₂mgf.congr hcenter
    simpa only [hI₂proxy, I₂] using hneg
  have hI₃proxy :
      LOOConcentration.Concentration.subGaussianProxy Cnn s₃ =
        NNReal.mk (C * (∫ z, δ₁ (n + 2) z ∂μ) ^ 2)
          (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)) := by
    apply NNReal.coe_injective
    rw [LOOConcentration.Concentration.coe_subGaussianProxy]
    change C * (∫ z, δ₁ (n + 2) z ∂μ) ^ 2 =
      C * (∫ z, δ₁ (n + 2) z ∂μ) ^ 2
    rfl
  have hI₃mgf' : ProbabilityTheory.HasSubgaussianMGF I₃
      (LOOConcentration.Concentration.subGaussianProxy Cnn s₃) P := by
    simpa only [I₃, R, P, C, hI₃proxy] using hI₃mgf
  have hDec := modelSelection_actual_signed_bias_decomposition μ T₀ T₁ L
    hf₀ hf₁ hShortMeas hHeld δ₃ hBias
  dsimp only [P, Q, F, f, V, E, R] at hDec
  rcases hDec with ⟨hRInt, hEInt, hVInt, hI₁Int, hI₂Int, hI₃Int,
    hI₁mean, hI₂mean, hI₃mean, hBiasBound, hDecomp, hDecompNeg⟩
  change |bias| ≤ δ₃ at hBiasBound
  have hBiasBounds := abs_le.mp hBiasBound
  have hC1 : LOOConcentration.Concentration.CenteredSubGaussianMGF P Cnn a I₁ :=
    ⟨hI₁Int, hI₁mean, hI₁mgf⟩
  have hC2 : LOOConcentration.Concentration.CenteredSubGaussianMGF P Cnn s₂ I₂ :=
    ⟨hI₂Int, hI₂mean, hI₂mgf'⟩
  have hC3 : LOOConcentration.Concentration.CenteredSubGaussianMGF P Cnn s₃ I₃ :=
    ⟨hI₃Int, hI₃mean, hI₃mgf'⟩
  have hSum := LOOConcentration.Concentration.centeredSubGaussianMGF_three_add hC1 hC2 hC3
  have hProxyEq :
      (LOOConcentration.Concentration.subGaussianProxy Cnn scales : ℝ) = K := by
    rw [LOOConcentration.Concentration.coe_subGaussianProxy]
    change C * ((a : ℝ) + c / Real.sqrt (n + 2 : ℝ) +
      ∫ z, δ₁ (n + 2) z ∂μ) ^ 2 = K
    rfl
  have hProxy : LOOConcentration.Concentration.subGaussianProxy Cnn scales =
      NNReal.mk K (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg b)) := by
    apply NNReal.coe_injective
    simpa only [NNReal.coe_mk] using hProxyEq
  let S : Dataset (Observation k m) (n + 2) → ℝ := fun D => (I₁ D + I₂ D) + I₃ D
  have hSumMGF : ProbabilityTheory.HasSubgaussianMGF S
      (NNReal.mk K (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg b))) P := by
    convert hSum.mgf using 1
    exact hProxy.symm
  have hSumNegMGF := hSumMGF.neg
  have hTailPlus := signed_simplified_strict_tail_of_hasSubgaussianMGF
    (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg b)) hSumMGF ht
  have hTailMinus := signed_simplified_strict_tail_of_hasSubgaussianMGF
    (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg b)) hSumNegMGF ht
  have hTailMinus' : P.real {D | -S D > t} ≤ gaussian := by
    change P.real {x | (-S) x > t} ≤
      (if C * b ^ 2 = 0 then 0 else Real.exp (-(t ^ 2 / (2 * (C * b ^ 2)))))
    exact hTailMinus
  have hEventPlus : {D | R D - E D > δ₃ + t} ⊆
      {D | S D > t} := by
    intro D hD
    change R D - E D > δ₃ + t at hD
    have hh := hDecomp D
    change R D - E D = S D + bias at hh
    change S D > t
    linarith [hBiasBounds.2]
  have hEventMinus : {D | E D - R D > δ₃ + t} ⊆
      {D | -S D > t} := by
    intro D hD
    change E D - R D > δ₃ + t at hD
    have hh₀ := hDecompNeg D
    change E D - R D = -I₁ D + -I₂ D + -I₃ D - bias at hh₀
    have hh : E D - R D = -S D - bias := by
      rw [hh₀]
      simp only [S]
      ring
    change -S D > t
    linarith [hh, hBiasBounds.1]
  have hPlus : P.real {D | R D - E D > δ₃ + t} ≤ gaussian := by
    calc
      P.real {D | R D - E D > δ₃ + t} ≤
          P.real {D | S D > t} := measureReal_mono hEventPlus
      _ ≤ gaussian := by
        change P.real {x | S x > t} ≤
          (if C * b ^ 2 = 0 then 0 else Real.exp (-(t ^ 2 / (2 * (C * b ^ 2)))))
        exact hTailPlus
  have hMinus : P.real {D | E D - R D > δ₃ + t} ≤ gaussian := by
    calc
      P.real {D | E D - R D > δ₃ + t} ≤
          P.real {D | -S D > t} := measureReal_mono hEventMinus
      _ ≤ gaussian := hTailMinus'
  have hAbsSubset : {D | |R D - E D| > δ₃ + t} ⊆
      {D | R D - E D > δ₃ + t} ∪ {D | E D - R D > δ₃ + t} := by
    intro D hD
    change |R D - E D| > δ₃ + t at hD
    by_cases hp : R D - E D > δ₃ + t
    · exact Set.mem_union_left _ hp
    · have hle : R D - E D ≤ δ₃ + t := le_of_not_gt hp
      have hbound : 0 ≤ δ₃ + t := by linarith
      have hnonneg : ¬ 0 ≤ R D - E D := by
        intro hpos
        rw [abs_of_nonneg hpos] at hD
        linarith
      have hneg : R D - E D ≤ 0 := le_of_not_ge hnonneg
      have habsneg := hD
      rw [abs_of_nonpos hneg] at habsneg
      have hn : E D - R D > δ₃ + t := by linarith
      exact Set.mem_union_right _ hn
  have hAbs : P.real {D | |R D - E D| > δ₃ + t} ≤ 2 * gaussian := by
    calc
      P.real {D | |R D - E D| > δ₃ + t} ≤
          P.real ({D | R D - E D > δ₃ + t} ∪ {D | E D - R D > δ₃ + t}) :=
            measureReal_mono hAbsSubset
      _ ≤ P.real {D | R D - E D > δ₃ + t} +
          P.real {D | E D - R D > δ₃ + t} := measureReal_union_le _ _
      _ ≤ gaussian + gaussian := add_le_add hPlus hMinus
      _ = 2 * gaussian := by ring
  exact ⟨hPlus, hMinus, hAbs⟩

end ActualSignedSimplified

end LOOConcentration.Manuscript.Internal
