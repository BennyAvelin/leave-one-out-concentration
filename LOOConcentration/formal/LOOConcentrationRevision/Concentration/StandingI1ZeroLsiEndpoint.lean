import LOOConcentrationRevision.Concentration.StandingI1WholeGrowthAssembly
import LOOConcentrationRevision.Probability.ZeroEndpointTails
import LOOConcentrationRevision.Results.StandingLossDecomposition
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

/-- The actual source I₁ has zero two-sided tails when the intrinsic LSI
constant vanishes. Its bias is derived from the source mean and deleted-law
identities, then discharged by the accepted Q3 pointmass endpoint. -/
theorem standing_I1_zero_lsi_endpoint
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)
    (hCzero : observationLogSobolevConstant μ = 0)
    (t : ℝ) (ht : 0 < t) :
    let P : Measure (Dataset (Observation k m) (n + 2)) :=
      Measure.pi fun _ : Fin (n + 2) => μ
    let I₁ : Dataset (Observation k m) (n + 2) → ℝ :=
      standingI1 μ T L δ₁ δ₂ δ₃ c d hSt
    P.real {D | I₁ D > t} = 0 ∧ P.real {D | -I₁ D > t} = 0 := by
  let P : Measure (Dataset (Observation k m) (n + 2)) :=
    Measure.pi fun _ : Fin (n + 2) => μ
  let I₁ : Dataset (Observation k m) (n + 2) → ℝ :=
    standingI1 μ T L δ₁ δ₂ δ₃ c d hSt
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
      (fun p : Dataset (Observation k m) (n + 1) × Observation k m =>
        fittedLoss (T n) L p.1 p.2) := hSt.stable.measurable_loss n
  have hmeanCoord (i : Fin (n + 2)) : Measurable (fun D : Dataset (Observation k m) (n + 2) =>
      meanFittedLoss μ (T n) L (D i) (hSt.mean_integrable (D i))) :=
    hmeanMeas.comp (measurable_pi_apply i)
  have hVMeas : Measurable (standingV μ T L δ₁ δ₂ δ₃ c d hSt) := by
    change Measurable (fun D : Dataset (Observation k m) (n + 2) =>
      (∑ i : Fin (n + 2), meanFittedLoss μ (T n) L (D i)
        (hSt.mean_integrable (D i))) / (n + 2 : ℝ))
    apply Measurable.div_const
    simpa using Finset.measurable_sum Finset.univ
      (fun i hi => hmeanCoord i)
  have hdel (i : Fin (n + 2)) : Measurable
      (fun D : Dataset (Observation k m) (n + 2) => LOOConcentration.deleteAt D i) := by
    apply measurable_pi_lambda
    intro j
    exact measurable_pi_apply (i.succAbove j)
  have hfitTerm (i : Fin (n + 2)) : Measurable
      (fun D : Dataset (Observation k m) (n + 2) =>
        fittedLoss (T n) L (LOOConcentration.deleteAt D i) (D i)) := by
    exact hfitMeas.comp ((hdel i).prodMk (measurable_pi_apply i))
  have hlooMeas : Measurable (LOOConcentration.looEstimate (T n) L) := by
    change Measurable (fun D : Dataset (Observation k m) (n + 2) =>
      (∑ i : Fin (n + 2), fittedLoss (T n) L (LOOConcentration.deleteAt D i) (D i)) /
        (n + 2 : ℝ))
    apply Measurable.div_const
    simpa using Finset.measurable_sum Finset.univ (fun i hi => hfitTerm i)
  have hI₁Meas : Measurable I₁ := by
    change Measurable (standingV μ T L δ₁ δ₂ δ₃ c d hSt -
      LOOConcentration.looEstimate (T n) L)
    exact hVMeas.sub hlooMeas
  have hshort := standingShortLoss_integrable μ T L δ₁ δ₂ δ₃ c d hSt
  have hparts := standingLoss_integrability μ T L δ₁ δ₂ δ₃ c d hSt
  have hVInt : Integrable (standingV μ T L δ₁ δ₂ δ₃ c d hSt) P := hparts.2.1
  have hlooInt : Integrable (LOOConcentration.looEstimate (T n) L) P := hparts.2.2.1
  have hmeanZero : (∫ D, I₁ D ∂P) = 0 := by
    change (∫ D, standingV μ T L δ₁ δ₂ δ₃ c d hSt D -
      LOOConcentration.looEstimate (T n) L D ∂P) = 0
    rw [integral_sub hVInt hlooInt]
    change standingEV μ T L δ₁ δ₂ δ₃ c d hSt -
      (∫ D, LOOConcentration.looEstimate (T n) L D ∂P) = 0
    rw [LOOConcentration.integral_looEstimate_eq_independent_test μ (T n) L hshort]
    rw [standingEV_eq_joint μ T L δ₁ δ₂ δ₃ c d hSt]
    ring
  have hbias : |∫ D, I₁ D ∂Measure.pi (fun _ : Fin (n + 2) => μ)| ≤ (0:ℝ) := by
    change |∫ D, I₁ D ∂P| ≤ 0
    rw [hmeanZero]
    norm_num
  have htails := observation_zero_lsi_original_tails_eq_zero
    μ hCzero I₁ hI₁Meas 0 hbias t ht
  exact ⟨htails.1, htails.2.1⟩


/-- Complete actual source I₁ mixture consumer: the zero-LSI endpoint is
internal, and the positive-LSI case uses the mixed zero/positive-growth source
assembly. -/
theorem standing_I1_mixed_growth_mixture_tail
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
    have hpos := standing_I1_mixed_growth_mixture_tail_positive_constant
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

#print axioms standing_I1_zero_lsi_endpoint
#print axioms standing_I1_mixed_growth_mixture_tail

end LOOConcentration.Revision
