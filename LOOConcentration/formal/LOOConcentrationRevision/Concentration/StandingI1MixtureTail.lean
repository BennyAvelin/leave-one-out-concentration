import LOOConcentrationRevision.Concentration.StandingDeletedLossSubGaussian
import LOOConcentrationRevision.Concentration.CertifiedGaussianChernoff
import LOOConcentration.Frozen.Foundations.LooEstimate
import LOOConcentrationRevision.Frozen.Definitions.StandingAssumption
import LOOConcentration.Probability.DeletedTransport
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic

set_option autoImplicit false
namespace LOOConcentration.Revision

open MeasureTheory

/-- The nonuniform Gaussian-mixture two-sided tail for the source `I₁`
(validation average minus the leave-one-out estimate). -/
theorem standing_I1_mixture_tail
    {k m n : ℕ} (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, Estimator k m (r + 1))
    (L : Responses m → Responses m → ℝ)
    (δ₁ δ₂ : ℕ → Observation k m → ℝ) (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)
    (hzero : ∀ z, δ₂ (n+1) z = 0)
    (t : ℝ) (ht : 0 < t) :
    let P := Measure.pi fun _ : Fin (n+2) => μ
    let I₁ := fun D : Dataset (Observation k m) (n+2) =>
      (∑ i : Fin (n+2), meanFittedLoss μ (T n) L (D i)
        (hSt.mean_integrable (D i))) / (n+2:ℝ) - looEstimate (T n) L D
    let C := (observationLogSobolevConstant μ).toReal
    let G := fun s : ℝ => if C * s^2 = 0 then 0 else
      Real.exp (-(t^2 / (2 * C * s^2)))
    P.real {D | I₁ D > t} ≤ (n+2:ℝ) * ∫ z, G (δ₁ (n+1) z) ∂μ ∧
      P.real {D | -I₁ D > t} ≤ (n+2:ℝ) * ∫ z, G (δ₁ (n+1) z) ∂μ := by
  let P : Measure (Dataset (Observation k m) (n+2)) :=
    Measure.pi fun _ : Fin (n+2) => μ
  let PTrain : Measure (Dataset (Observation k m) (n+1)) :=
    Measure.pi fun _ : Fin (n+1) => μ
  let C : ℝ := (observationLogSobolevConstant μ).toReal
  let G : ℝ → ℝ := fun s => if C*s^2 = 0 then 0 else
    Real.exp (-(t^2/(2*C*s^2)))
  let rate : Observation k m → ℝ := fun z => G (δ₁ (n+1) z)
  let I₁ : Dataset (Observation k m) (n+2) → ℝ := fun D =>
    (∑ i : Fin (n+2), meanFittedLoss μ (T n) L (D i)
      (hSt.mean_integrable (D i))) / (n+2:ℝ) - looEstimate (T n) L D
  let Y : Fin (n+2) → Dataset (Observation k m) (n+2) → ℝ := fun i D =>
    meanFittedLoss μ (T n) L (D i) (hSt.mean_integrable (D i)) -
      fittedLoss (T n) L (deleteAt D i) (D i)
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hGnonneg (s : ℝ) : 0 ≤ G s := by
    dsimp [G]
    split_ifs <;> positivity
  have hGle (s : ℝ) : G s ≤ 1 := by
    dsimp [G]
    split_ifs with hz
    · norm_num
    · have hs : 0 < C*s^2 :=
        lt_of_le_of_ne (mul_nonneg hC (sq_nonneg s)) (Ne.symm hz)
      have hden : 0 < 2*C*s^2 := by
        have h := mul_pos (by norm_num : (0:ℝ) < 2) hs
        simpa [mul_assoc] using h
      have hexp : -(t^2/(2*C*s^2)) ≤ 0 := by
        exact neg_nonpos.mpr (div_nonneg (sq_nonneg t) (le_of_lt hden))
      exact Real.exp_le_one_iff.mpr hexp
  have hGmeas : Measurable G := by
    dsimp [G]
    have hq : Measurable (fun s : ℝ => C*s^2) := by fun_prop
    have hzeroSet : MeasurableSet {s : ℝ | C*s^2 = 0} :=
      measurableSet_eq_fun hq measurable_const
    have hexp : Measurable (fun s : ℝ => Real.exp (-(t^2/(2*C*s^2)))) := by fun_prop
    exact Measurable.ite hzeroSet measurable_const hexp
  have hrate_aesm : AEStronglyMeasurable rate μ := by
    exact (hGmeas.comp_aemeasurable
      hSt.delta₁_deleted_integrable.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  have hrateInt : Integrable rate μ := by
    refine (integrable_const (1:ℝ)).mono' hrate_aesm ?_
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (hGnonneg _)]
    exact hGle _
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
  have hsection := standing_deleted_loss_hasSubgaussianMGF
    μ T L δ₁ δ₂ δ₃ c d hSt hzero
  have hcond : ∀ᵐ z ∂μ,
      PTrain.real {D | X (D,z) > t} ≤ rate z ∧
      PTrain.real {D | -X (D,z) > t} ≤ rate z := by
    filter_upwards [hsection] with z hmgf
    have htails := strict_tails_le_of_subgaussianMGF_via_certified_chernoff
      PTrain (fun D => fittedLoss (T n) L D z -
        meanFittedLoss μ (T n) L z (hSt.mean_integrable z))
      (NNReal.mk (C*(δ₁ (n+1) z)^2)
        (mul_nonneg hC (sq_nonneg _))) hmgf t ht
    have hval : (((NNReal.mk (C*(δ₁ (n+1) z)^2)
        (mul_nonneg hC (sq_nonneg _)) : NNReal) : ℝ)) = C*(δ₁ (n+1) z)^2 := rfl
    have hproxyZero :
        (NNReal.mk (C*(δ₁ (n+1) z)^2) (mul_nonneg hC (sq_nonneg _)) : NNReal) = 0 ↔
          C*(δ₁ (n+1) z)^2 = 0 := by
      constructor
      · intro hz
        have hv := congrArg (fun x : NNReal => (x : ℝ)) hz
        simpa using hv
      · intro hz
        apply Subtype.ext
        simpa using hz
    simpa only [X, rate, G, C, hval, hproxyZero, mul_assoc, neg_sub] using
      And.intro htails.2 htails.1
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
      (Filter.Eventually.of_forall fun z => hGnonneg _)).symm
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
      (Filter.Eventually.of_forall fun z => hGnonneg _)
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
      (Filter.Eventually.of_forall fun z => hGnonneg _)
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

end LOOConcentration.Revision
