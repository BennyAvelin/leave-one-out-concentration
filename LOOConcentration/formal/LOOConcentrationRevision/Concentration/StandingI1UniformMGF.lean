import LOOConcentrationRevision.Concentration.StandingDeletedLossSubGaussian
import LOOConcentration.Probability.DeletedTransport
import LOOConcentration.Probability.SampleTestLaw
import LOOConcentrationRevision.Frozen.Definitions.StandingAssumption
import LOOConcentrationRevision.Frozen.Definitions.MeanFittedLoss
import LOOConcentration.Frozen.Foundations.LooEstimate
import Mathlib.Analysis.Convex.Jensen
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
namespace LOOConcentration.Revision

open MeasureTheory
open scoped MeasureTheory

private theorem hasSubgaussianMGF_mono_param {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} {c₁ c₂ : NNReal}
    (h : ProbabilityTheory.HasSubgaussianMGF X c₁ μ) (hc : (c₁ : ℝ) ≤ (c₂ : ℝ)) :
    ProbabilityTheory.HasSubgaussianMGF X c₂ μ where
  integrable_exp_mul := h.integrable_exp_mul
  mgf_le t := by
    calc
      ProbabilityTheory.mgf X μ t ≤ Real.exp ((c₁ : ℝ) * t ^ 2 / 2) := h.mgf_le t
      _ ≤ Real.exp ((c₂ : ℝ) * t ^ 2 / 2) := by
        apply Real.exp_le_exp.mpr
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hc (sq_nonneg t)) (by norm_num)

/-- Uniform conditional subgaussianity over the second product coordinate
implies the same bound for the product-law random variable. -/
private theorem hasSubgaussianMGF_prod_of_ae {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (ν : Measure α) (μ : Measure β) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (X : α × β → ℝ) (c : NNReal)
    (hX : AEStronglyMeasurable X (ν.prod μ))
    (hsection : ∀ᵐ z ∂μ,
      ProbabilityTheory.HasSubgaussianMGF (fun x => X (x, z)) c ν) :
    ProbabilityTheory.HasSubgaussianMGF X c (ν.prod μ) := by
  have hexpMeas (t : ℝ) : AEStronglyMeasurable
      (fun p : α × β => Real.exp (t * X p)) (ν.prod μ) := by
    exact Real.continuous_exp.comp_aestronglyMeasurable (hX.const_mul t)
  have hexpInt (t : ℝ) : Integrable
      (fun p : α × β => Real.exp (t * X p)) (ν.prod μ) := by
    have hsections : ∀ᵐ z ∂μ,
        Integrable (fun x => Real.exp (t * X (x, z))) ν := by
      filter_upwards [hsection] with z hz
      exact hz.integrable_exp_mul t
    have hGmeas : AEStronglyMeasurable
        (fun z => ∫ x, Real.exp (t * X (x, z)) ∂ν) μ :=
      (hexpMeas t).prod_swap.integral_prod_right'
    have hGbound : ∀ᵐ z ∂μ,
        (∫ x, Real.exp (t * X (x, z)) ∂ν) ≤ Real.exp ((c : ℝ) * t ^ 2 / 2) := by
      filter_upwards [hsection] with z hz
      simpa only [ProbabilityTheory.mgf] using hz.mgf_le t
    have hGnonneg (z : β) :
        0 ≤ ∫ x, Real.exp (t * X (x, z)) ∂ν :=
      integral_nonneg (fun x => (Real.exp_pos _).le)
    have hGnorm : ∀ᵐ z ∂μ,
        ‖(∫ x, Real.exp (t * X (x, z)) ∂ν)‖ ≤ Real.exp ((c : ℝ) * t ^ 2 / 2) := by
      filter_upwards [hGbound] with z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (hGnonneg z)]
      exact hz
    have hGint : Integrable (fun z => ∫ x, Real.exp (t * X (x, z)) ∂ν) μ :=
      (integrable_const (Real.exp ((c : ℝ) * t ^ 2 / 2))).mono' hGmeas hGnorm
    have hGint' : Integrable
        (fun z => ∫ x, ‖Real.exp (t * X (x, z))‖ ∂ν) μ := by
      have heq : (fun z => ∫ x, ‖Real.exp (t * X (x, z))‖ ∂ν) =
          (fun z => ∫ x, Real.exp (t * X (x, z)) ∂ν) := by
        funext z
        congr 1
        funext x
        exact Real.norm_of_nonneg (Real.exp_nonneg _)
      rw [heq]
      exact hGint
    exact (integrable_prod_iff' (hexpMeas t)).2 ⟨hsections, hGint'⟩
  refine ⟨hexpInt, ?_⟩
  intro t
  have hGmeas : AEStronglyMeasurable
      (fun z => ∫ x, Real.exp (t * X (x, z)) ∂ν) μ :=
    (hexpMeas t).prod_swap.integral_prod_right'
  have hGbound : ∀ᵐ z ∂μ,
      (∫ x, Real.exp (t * X (x, z)) ∂ν) ≤ Real.exp ((c : ℝ) * t ^ 2 / 2) := by
    filter_upwards [hsection] with z hz
    simpa only [ProbabilityTheory.mgf] using hz.mgf_le t
  have hGnonneg (z : β) :
      0 ≤ ∫ x, Real.exp (t * X (x, z)) ∂ν :=
    integral_nonneg (fun x => (Real.exp_pos _).le)
  have hGnorm : ∀ᵐ z ∂μ,
      ‖(∫ x, Real.exp (t * X (x, z)) ∂ν)‖ ≤ Real.exp ((c : ℝ) * t ^ 2 / 2) := by
    filter_upwards [hGbound] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (hGnonneg z)]
    exact hz
  have hGint : Integrable (fun z => ∫ x, Real.exp (t * X (x, z)) ∂ν) μ :=
    (integrable_const (Real.exp ((c : ℝ) * t ^ 2 / 2))).mono' hGmeas hGnorm
  change ProbabilityTheory.mgf X (ν.prod μ) t ≤ Real.exp ((c : ℝ) * t ^ 2 / 2)
  calc
    ProbabilityTheory.mgf X (ν.prod μ) t =
        ∫ z, (∫ x, Real.exp (t * X (x, z)) ∂ν) ∂μ := by
      simpa only [ProbabilityTheory.mgf] using
        (integral_prod_symm (fun p : α × β => Real.exp (t * X p)) (hexpInt t))
    _ ≤ Real.exp ((c : ℝ) * t ^ 2 / 2) := by
      calc
        _ ≤ ∫ _z : β, Real.exp ((c : ℝ) * t ^ 2 / 2) ∂μ :=
          integral_mono_ae hGint (integrable_const _) hGbound
        _ = Real.exp ((c : ℝ) * t ^ 2 / 2) := by simp

/-- Jensen's exponential inequality preserves a common subgaussian parameter
under a finite average, without any independence premise. -/
private theorem hasSubgaussianMGF_average {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    (X : Fin (n + 2) → Ω → ℝ) (c : NNReal)
    (hX : ∀ i, ProbabilityTheory.HasSubgaussianMGF (X i) c μ) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun ω => (∑ i : Fin (n + 2), X i ω) / (n + 2 : ℝ)) c μ := by
  let N : ℝ := (n + 2 : ℝ)
  have hN : N ≠ 0 := by dsimp [N]; positivity
  have hNpos : 0 < N := by dsimp [N]; positivity
  have hweights : (∑ i : Fin (n + 2), (1 / N : ℝ)) = 1 := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, N, nsmul_eq_mul]
    field_simp [hN]
  have hsumMeas : AEStronglyMeasurable
      (fun ω => ∑ i : Fin (n + 2), X i ω) μ :=
    by
      have hfun : (∑ i : Fin (n + 2), X i) =
          (fun ω => ∑ i : Fin (n + 2), X i ω) := by
        ext ω
        simp
      exact hfun ▸ Finset.aestronglyMeasurable_sum Finset.univ
        (fun i _ => (hX i).aestronglyMeasurable)
  have havgMeas (t : ℝ) : AEStronglyMeasurable
      (fun ω => Real.exp (t * ((∑ i : Fin (n + 2), X i ω) / N))) μ := by
    have harg : AEStronglyMeasurable
        (fun ω => t * ((∑ i : Fin (n + 2), X i ω) / N)) μ := by
      have harg' : AEStronglyMeasurable
          (fun ω => (t / N) * ∑ i : Fin (n + 2), X i ω) μ :=
        hsumMeas.const_mul (t / N)
      convert harg' using 1
      ext ω
      field_simp [hN]
    exact Real.continuous_exp.comp_aestronglyMeasurable harg
  have hsumInt (t : ℝ) : Integrable
      (fun ω => ∑ i : Fin (n + 2), Real.exp (t * X i ω)) μ := by
    apply integrable_finsetSum Finset.univ
    intro i _
    exact (hX i).integrable_exp_mul t
  have hjensen (t : ℝ) (ω : Ω) :
      Real.exp (t * ((∑ i : Fin (n + 2), X i ω) / N)) ≤
        (∑ i : Fin (n + 2), Real.exp (t * X i ω)) / N := by
    have hj := convexOn_exp.map_sum_le
      (t := Finset.univ) (w := fun _ : Fin (n + 2) => (1 / N : ℝ))
      (p := fun i => t * X i ω)
      (fun _ _ => by positivity) hweights (fun _ _ => Set.mem_univ _)
    have hleft : (∑ i : Fin (n + 2), (1 / N : ℝ) * (t * X i ω)) =
        t * ((∑ i : Fin (n + 2), X i ω) / N) := by
      simp only [← Finset.mul_sum]
      field_simp [hN]
    have hright : (∑ i : Fin (n + 2), (1 / N : ℝ) * Real.exp (t * X i ω)) =
        (∑ i : Fin (n + 2), Real.exp (t * X i ω)) / N := by
      simp only [← Finset.mul_sum]
      ring
    simpa only [smul_eq_mul, hleft, hright] using hj
  have havgInt (t : ℝ) : Integrable
      (fun ω => Real.exp (t * ((∑ i : Fin (n + 2), X i ω) / N))) μ := by
    exact (hsumInt t).div_const N |>.mono' (havgMeas t)
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
        have hright : 0 ≤ (∑ i : Fin (n + 2), Real.exp (t * X i ω)) / N :=
          div_nonneg (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le) hNpos.le
        simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le,
          abs_of_nonneg hright] using hjensen t ω)
  refine ⟨havgInt, ?_⟩
  intro t
  have hconst : Integrable (fun _ : Ω => Real.exp ((c : ℝ) * t ^ 2 / 2)) μ := integrable_const _
  have hsumBound :
      (∑ i : Fin (n + 2), ∫ ω, Real.exp (t * X i ω) ∂μ) ≤
        (n + 2 : ℝ) * Real.exp ((c : ℝ) * t ^ 2 / 2) := by
    calc
      _ ≤ ∑ _i : Fin (n + 2), Real.exp ((c : ℝ) * t ^ 2 / 2) :=
        Finset.sum_le_sum fun i _ => by simpa [ProbabilityTheory.mgf] using (hX i).mgf_le t
      _ = (n + 2 : ℝ) * Real.exp ((c : ℝ) * t ^ 2 / 2) := by simp
  change ProbabilityTheory.mgf
    (fun ω => (∑ i : Fin (n + 2), X i ω) / N) μ t ≤ Real.exp ((c : ℝ) * t ^ 2 / 2)
  rw [ProbabilityTheory.mgf]
  calc
    (∫ ω, Real.exp (t * ((∑ i : Fin (n + 2), X i ω) / N)) ∂μ) ≤
        ∫ ω, (∑ i : Fin (n + 2), Real.exp (t * X i ω)) / N ∂μ :=
      integral_mono_ae (havgInt t) ((hsumInt t).div_const N)
        (Filter.Eventually.of_forall fun ω => hjensen t ω)
    _ = ((∑ i : Fin (n + 2), ∫ ω, Real.exp (t * X i ω) ∂μ) / N) := by
      rw [integral_div, integral_finsetSum Finset.univ (fun i _ => (hX i).integrable_exp_mul t), Finset.sum_div]
    _ ≤ Real.exp ((c : ℝ) * t ^ 2 / 2) := by
      dsimp [N]
      rw [div_le_iff₀ (by positivity)]
      simpa only [mul_comm] using hsumBound

/-- The actual revision `I₁`: mean validation average minus the empirical
leave-one-out estimate, with the source-optimal observation LSI constant. -/
theorem standing_I1_uniform_hasSubgaussianMGF
    {k m n : ℕ} (μ : Measure (LOOConcentration.Observation k m)) [IsProbabilityMeasure μ]
    (T : ∀ r : ℕ, LOOConcentration.Estimator k m (r + 1))
    (L : LOOConcentration.Responses m → LOOConcentration.Responses m → ℝ)
    (δ₁ δ₂ : ℕ → LOOConcentration.Observation k m → ℝ)
    (δ₃ : ℕ → ℝ) (c d : ℝ)
    (hSt : StandingAssumption (n := n) μ T L δ₁ δ₂ δ₃ c d)
    (hzeroDeleted : ∀ z, δ₂ (n + 1) z = 0)
    (a : NNReal)
    (hbound : ∀ᵐ z ∂μ, δ₁ (n + 1) z ≤ (a : ℝ)) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun D : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 2) =>
        (∑ i : Fin (n + 2),
          meanFittedLoss μ (T n) L (D i) (hSt.mean_integrable (D i))) / (n + 2 : ℝ) -
          LOOConcentration.looEstimate (T n) L D)
      (NNReal.mk
        ((observationLogSobolevConstant μ).toReal * (a : ℝ)^2)
        (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)))
      (Measure.pi fun _ : Fin (n + 2) => μ) := by
  let ν := Measure.pi fun _ : Fin (n + 2) => μ
  let νdel := Measure.pi fun _ : Fin (n + 1) => μ
  let C : ℝ := (observationLogSobolevConstant μ).toReal
  let v : ℝ := C * (a : ℝ)^2
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hv : 0 ≤ v := mul_nonneg hC (sq_nonneg _)
  let cv : NNReal := ⟨v, hv⟩
  have hshort : Integrable
      (fun p : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 1) ×
        LOOConcentration.Observation k m => LOOConcentration.fittedLoss (T n) L p.1 p.2)
      (νdel.prod μ) := by
    let i : Fin (n + 2) := ⟨0, by omega⟩
    let f : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 1) ×
        LOOConcentration.Observation k m → ℝ := fun p => LOOConcentration.fittedLoss (T n) L p.1 p.2
    have hm : Measurable f := hSt.stable.measurable_loss n
    have hc : Integrable (fun D : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 2) =>
        f (LOOConcentration.deleteAt D i, D i)) ν := by
      simpa only [f] using hSt.stable.integrable_deleted n i
    exact (LOOConcentration.deleted_section_integrable_iff μ i f hm.aestronglyMeasurable).mp hc
  have hmeanInt : Integrable
      (fun z => meanFittedLoss μ (T n) L z (hSt.mean_integrable z)) μ := by
    simpa only [meanFittedLoss] using hshort.integral_prod_right
  have hsrc := standing_deleted_loss_hasSubgaussianMGF μ T L δ₁ δ₂ δ₃ c d hSt hzeroDeleted
  have hcoord : ∀ i : Fin (n + 2),
      ProbabilityTheory.HasSubgaussianMGF
        (fun D : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 2) =>
          meanFittedLoss μ (T n) L (D i) (hSt.mean_integrable (D i)) -
            LOOConcentration.fittedLoss (T n) L (LOOConcentration.deleteAt D i) (D i)) cv ν := by
    intro i
    let X : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 1) ×
        LOOConcentration.Observation k m → ℝ := fun p =>
      meanFittedLoss μ (T n) L p.2 (hSt.mean_integrable p.2) -
        LOOConcentration.fittedLoss (T n) L p.1 p.2
    have hXmeas : AEStronglyMeasurable X (νdel.prod μ) := by
      have hloss : AEStronglyMeasurable
          (fun p : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 1) ×
            LOOConcentration.Observation k m => LOOConcentration.fittedLoss (T n) L p.1 p.2)
          (νdel.prod μ) := hshort.aestronglyMeasurable
      have hm : AEStronglyMeasurable
          (fun p : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 1) ×
            LOOConcentration.Observation k m => meanFittedLoss μ (T n) L p.2 (hSt.mean_integrable p.2))
          (νdel.prod μ) := by
        have hmap : Measure.map Prod.snd (νdel.prod μ) = μ := by
          rw [Measure.map_snd_prod, measure_univ, one_smul]
        have hmeanMap : AEStronglyMeasurable
            (fun z => meanFittedLoss μ (T n) L z (hSt.mean_integrable z))
            (Measure.map Prod.snd (νdel.prod μ)) := by
          rw [hmap]
          exact hmeanInt.aestronglyMeasurable
        have hcomp := hmeanMap.comp_measurable measurable_snd
        simpa only [Function.comp_def] using hcomp
      have hsub : (fun p : LOOConcentration.Dataset
          (LOOConcentration.Observation k m) (n + 1) × LOOConcentration.Observation k m =>
          meanFittedLoss μ (T n) L p.2 (hSt.mean_integrable p.2)) -
          (fun p => LOOConcentration.fittedLoss (T n) L p.1 p.2) = X := by
        funext p
        rfl
      rw [← hsub]
      exact hm.sub hloss
    have hsect : ∀ᵐ z ∂μ,
        ProbabilityTheory.HasSubgaussianMGF (fun D : LOOConcentration.Dataset
          (LOOConcentration.Observation k m) (n + 1) => X (D, z)) cv νdel := by
      filter_upwards [hsrc, hbound] with z hmgf hz
      let vz : ℝ := C * (δ₁ (n + 1) z)^2
      let cz : NNReal := ⟨vz, mul_nonneg hC (sq_nonneg _)⟩
      have hcoeff : vz ≤ v := by
        dsimp [vz, v, C]
        have hδ0 := hSt.stable.delta₁_nonneg n z
        have ha0 : 0 ≤ (a : ℝ) := NNReal.coe_nonneg _
        have hsq : (δ₁ (n + 1) z)^2 ≤ (a : ℝ)^2 := by
          have hp : 0 ≤ ((a : ℝ) - δ₁ (n + 1) z) *
              ((a : ℝ) + δ₁ (n + 1) z) :=
            mul_nonneg (sub_nonneg.mpr hz) (add_nonneg ha0 hδ0)
          nlinarith
        exact mul_le_mul_of_nonneg_left hsq hC
      have hcoeffNN : cz ≤ cv := by
        apply NNReal.coe_le_coe.mpr
        exact hcoeff
      have hneg : ProbabilityTheory.HasSubgaussianMGF
          (fun D : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 1) =>
            meanFittedLoss μ (T n) L z (hSt.mean_integrable z) -
              LOOConcentration.fittedLoss (T n) L D z)
          (NNReal.mk
            ((observationLogSobolevConstant μ).toReal * (δ₁ (n + 1) z)^2)
            (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))) νdel := by
        have h0 := hmgf.neg
        have hEq : (fun D : LOOConcentration.Dataset
            (LOOConcentration.Observation k m) (n + 1) =>
              -(LOOConcentration.fittedLoss (T n) L D z -
                meanFittedLoss μ (T n) L z (hSt.mean_integrable z))) =ᵐ[νdel]
            (fun D => meanFittedLoss μ (T n) L z (hSt.mean_integrable z) -
              LOOConcentration.fittedLoss (T n) L D z) := by
          filter_upwards [] with D
          ring
        simpa [νdel] using h0.congr hEq
      exact hasSubgaussianMGF_mono_param hneg (by exact_mod_cast hcoeffNN)
    have hpair := hasSubgaussianMGF_prod_of_ae νdel μ X cv hXmeas hsect
    let φ : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 2) →
        LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 1) ×
          LOOConcentration.Observation k m := fun D => (LOOConcentration.deleteAt D i, D i)
    have hmp := LOOConcentration.deleted_sample_and_heldout_measurePreserving μ i
    have hpair' : ProbabilityTheory.HasSubgaussianMGF X cv (ν.map φ) := by
      rw [hmp.map_eq]
      exact hpair
    have hfull := ProbabilityTheory.HasSubgaussianMGF.of_map hmp.measurable.aemeasurable hpair'
    simpa only [Function.comp_def, X, φ] using hfull
  let Y : Fin (n + 2) →
      LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 2) → ℝ := fun i D =>
        meanFittedLoss μ (T n) L (D i) (hSt.mean_integrable (D i)) -
          LOOConcentration.fittedLoss (T n) L (LOOConcentration.deleteAt D i) (D i)
  have hAvg := hasSubgaussianMGF_average ν Y cv hcoord
  have hI1 : (fun D : LOOConcentration.Dataset (LOOConcentration.Observation k m) (n + 2) =>
      (∑ i : Fin (n + 2), Y i D) / (n + 2 : ℝ)) =ᵐ[ν]
      (fun D => (∑ i : Fin (n + 2),
        meanFittedLoss μ (T n) L (D i) (hSt.mean_integrable (D i))) / (n + 2 : ℝ) -
        LOOConcentration.looEstimate (T n) L D) := by
    filter_upwards [] with D
    simp only [Y, LOOConcentration.looEstimate, LOOConcentration.fittedLoss,
      Finset.sum_sub_distrib]
    ring
  have hresult := hAvg.congr hI1
  change ProbabilityTheory.HasSubgaussianMGF _ cv ν
  exact hresult

end LOOConcentration.Revision
