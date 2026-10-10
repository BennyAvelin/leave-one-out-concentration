import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic
import LOOConcentration.Examples.GaussianInverseDesignMoment
import LOOConcentration.Examples.OlsConditionalNoiseMoment
import LOOConcentration.Examples.GaussianDesignIndependence

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LOOConcentration

private noncomputable abbrev olsDesignGaussianLaw (N : ℕ) : Measure (Fin N → ℝ) :=
  Measure.pi fun _ : Fin N => standardGaussian

private noncomputable abbrev olsNoiseGaussianVectorLaw (N : ℕ) : Measure (Fin N → ℝ) :=
  Measure.pi fun _ : Fin N => standardGaussian

private noncomputable def olsPairSplitEquiv (N : ℕ) :
    (Fin N → ℝ × ℝ) ≃ᵐ (Fin N → ℝ) × (Fin N → ℝ) :=
  MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin N)

private theorem measurePreserving_olsPairSplit (N : ℕ) :
    MeasurePreserving (olsPairSplitEquiv N) (olsPairGaussianLaw N)
      ((olsDesignGaussianLaw N).prod (olsNoiseGaussianVectorLaw N)) := by
  exact measurePreserving_arrowProdEquivProdArrow
    (α := ℝ) (β := ℝ) (γ := Fin N)
    (fun _ : Fin N => standardGaussian) (fun _ : Fin N => standardGaussian)

private noncomputable def olsPairTestReorderEquiv (N : ℕ) :
    ((Fin N → ℝ × ℝ) × ℝ) ≃ᵐ
      (Fin N → ℝ) × (ℝ × (Fin N → ℝ)) := by
  let split := olsPairSplitEquiv N
  exact (split.prodCongr (MeasurableEquiv.refl ℝ)).trans
    (MeasurableEquiv.prodAssoc.trans
      ((MeasurableEquiv.refl (Fin N → ℝ)).prodCongr MeasurableEquiv.prodComm))

private theorem measurePreserving_olsPairTestReorder (N : ℕ) :
    MeasurePreserving (olsPairTestReorderEquiv N)
      ((olsPairGaussianLaw N).prod standardGaussian)
      ((olsDesignGaussianLaw N).prod
        (standardGaussian.prod (olsNoiseGaussianVectorLaw N))) := by
  let hsplit := measurePreserving_olsPairSplit N
  let h₁ := hsplit.prod (MeasurePreserving.id standardGaussian)
  let h₂ := measurePreserving_prodAssoc (olsDesignGaussianLaw N)
    (olsNoiseGaussianVectorLaw N) standardGaussian
  have hswap : MeasurePreserving MeasurableEquiv.prodComm
      ((olsNoiseGaussianVectorLaw N).prod standardGaussian)
      (standardGaussian.prod (olsNoiseGaussianVectorLaw N)) := by
    exact ⟨MeasurableEquiv.prodComm.measurable, Measure.prod_swap⟩
  let h₃ := (MeasurePreserving.id (olsDesignGaussianLaw N)).prod
    hswap
  change MeasurePreserving
    (((olsPairSplitEquiv N).prodCongr (MeasurableEquiv.refl ℝ)).trans
      (MeasurableEquiv.prodAssoc.trans
        ((MeasurableEquiv.refl (Fin N → ℝ)).prodCongr MeasurableEquiv.prodComm))) _ _
  exact h₁.trans (h₂.trans h₃)

private def olsCovariateVector {N : ℕ} (G : Fin N → ℝ × ℝ) : Fin N → ℝ :=
  fun i => (G i).1

private noncomputable def olsCovariateCenteredSq {N : ℕ} (x : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, (x i - (∑ j : Fin N, x j) / (N : ℝ)) ^ 2

private lemma measurable_olsCovariateVector {N : ℕ} :
    Measurable (olsCovariateVector (N := N)) := by
  rw [measurable_pi_iff]
  intro i
  exact measurable_fst.comp (measurable_pi_apply i)

@[fun_prop]
private lemma measurable_olsCovariateCenteredSq {N : ℕ} :
    Measurable (olsCovariateCenteredSq (N := N)) := by
  unfold olsCovariateCenteredSq
  fun_prop

private lemma olsPairGaussianLaw_covariate_map (N : ℕ) :
    (olsPairGaussianLaw N).map (olsCovariateVector (N := N)) =
      olsDesignGaussianLaw N := by
  change (Measure.pi fun _ : Fin N => standardGaussian.prod standardGaussian).map
      (fun G i => (G i).1) = Measure.pi fun _ : Fin N => standardGaussian
  rw [Measure.pi_map_pi]
  · congr 1
    funext i
    simp [Measure.map_fst_prod]
  · intro i
    exact measurable_fst.aemeasurable

private lemma olsCenteredDesign_covariate_map (N : ℕ) :
    (olsPairGaussianLaw N).map olsCenteredDesign =
      (olsDesignGaussianLaw N).map (olsCovariateCenteredSq (N := N)) := by
  have hfun : (olsCenteredDesign : (Fin N → ℝ × ℝ) → ℝ) =
      (olsCovariateCenteredSq (N := N)) ∘ (olsCovariateVector (N := N)) := by
    funext G
    rfl
  rw [hfun, ← Measure.map_map measurable_olsCovariateCenteredSq
    measurable_olsCovariateVector]
  exact congrArg (fun μ : Measure (Fin N → ℝ) => μ.map olsCovariateCenteredSq)
    (olsPairGaussianLaw_covariate_map N)

private lemma standardGaussianSqSum_nonneg_local {N : ℕ} (x : Fin N → ℝ) :
    0 ≤ standardGaussianSqSum x := by
  unfold standardGaussianSqSum
  exact Finset.sum_nonneg fun i _ => sq_nonneg (x i)

private lemma measurable_standardGaussianSqSum_local {N : ℕ} :
    Measurable (standardGaussianSqSum (r := N)) := by
  unfold standardGaussianSqSum
  fun_prop

private instance instOlsStandardGaussianNullSingleton :
    NullSingletonClass standardGaussian :=
  ProbabilityTheory.nullSingletonClass_gaussianReal (μ := 0) (v := 1) (by norm_num)

private lemma ae_olsDesignCenteredSq_pos {N : ℕ} (hN : 1 < N) :
    ∀ᵐ x : Fin N → ℝ ∂olsDesignGaussianLaw N,
      0 < olsCovariateCenteredSq x := by
  let d := N - 1
  have hd : 0 < d := by dsimp [d]; omega
  have hsum : ∀ᵐ y : Fin d → ℝ ∂Measure.pi (fun _ : Fin d => standardGaussian),
      0 < standardGaussianSqSum y := by
    let i : Fin d := ⟨0, hd⟩
    have hi := Measure.ae_eval_ne (μ := fun _ : Fin d => standardGaussian) i (0 : ℝ)
    filter_upwards [hi] with y hy
    by_contra hnot
    have hzero : standardGaussianSqSum y = 0 :=
      le_antisymm (le_of_not_gt hnot) (standardGaussianSqSum_nonneg_local y)
    have hle : y i ^ 2 ≤ standardGaussianSqSum y := by
      unfold standardGaussianSqSum
      exact Finset.single_le_sum (fun j _ => sq_nonneg (y j)) (Finset.mem_univ i)
    have hsq : y i ^ 2 = 0 := by nlinarith
    exact hy (sq_eq_zero_iff.mp hsq)
  have hpush := olsCenteredDesign_gaussian_pushforward d
  have hdim : d + 1 = N := by dsimp [d]; omega
  have hpush' : (olsPairGaussianLaw N).map olsCenteredDesign =
      (Measure.pi (fun _ : Fin d => standardGaussian)).map
        (fun x => ∑ i : Fin d, x i ^ 2) := by
    rw [← hdim]
    simpa [olsPairGaussianLaw, standardGaussian, standardGaussianSqSum] using hpush
  have hmappos : ∀ᵐ z : ℝ ∂(olsPairGaussianLaw N).map olsCenteredDesign, 0 < z := by
    rw [hpush']
    exact (ae_map_iff measurable_standardGaussianSqSum_local.aemeasurable
      measurableSet_Ioi).2 hsum
  have hcovpos : ∀ᵐ x : Fin N → ℝ ∂olsDesignGaussianLaw N,
      0 < olsCovariateCenteredSq x := by
    rw [olsCenteredDesign_covariate_map N] at hmappos
    exact (ae_map_iff measurable_olsCovariateCenteredSq.aemeasurable
      measurableSet_Ioi).1 hmappos
  exact hcovpos

private noncomputable def olsDesignMean {N : ℕ} (x : Fin N → ℝ) : ℝ :=
  (∑ i : Fin N, x i) / (N : ℝ)

private noncomputable def olsDesignInvCenteredSq {N : ℕ} (x : Fin N → ℝ) : ℝ :=
  (olsCovariateCenteredSq x)⁻¹

private noncomputable def olsDesignMixedMeanInv {N : ℕ} (x : Fin N → ℝ) : ℝ :=
  (olsDesignMean x) ^ 2 / olsCovariateCenteredSq x

private noncomputable def olsDesignConditionalMoment {N : ℕ} (x : Fin N → ℝ) : ℝ :=
  1 / (N : ℝ) +
    (1 + (olsDesignMean x) ^ 2) / olsCovariateCenteredSq x

private lemma measurable_olsDesignInvCenteredSq {N : ℕ} :
    Measurable (olsDesignInvCenteredSq (N := N)) := by
  unfold olsDesignInvCenteredSq
  fun_prop

private lemma measurable_olsDesignMixedMeanInv {N : ℕ} :
    Measurable (olsDesignMixedMeanInv (N := N)) := by
  unfold olsDesignMixedMeanInv olsDesignMean
  fun_prop

private lemma olsCovariateCenteredSq_nonneg {N : ℕ} (x : Fin N → ℝ) :
    0 ≤ olsCovariateCenteredSq x := by
  unfold olsCovariateCenteredSq
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

private lemma olsXBar_eq_designMean {N : ℕ} (G : Fin N → ℝ × ℝ) :
    olsXBar G = olsDesignMean (olsCovariateVector G) := by
  rfl

private lemma olsCenteredDesign_eq_designCenteredSq {N : ℕ}
    (G : Fin N → ℝ × ℝ) :
    olsCenteredDesign G = olsCovariateCenteredSq (olsCovariateVector G) := by
  rfl

private lemma integrable_olsDesignStat_of_pair {N : ℕ} {g : (Fin N → ℝ) → ℝ}
    (hg : Measurable g)
    (hpair : Integrable (fun G : Fin N → ℝ × ℝ =>
      g (olsCovariateVector G)) (olsPairGaussianLaw N)) :
    Integrable g (olsDesignGaussianLaw N) := by
  have hmap : Integrable g ((olsPairGaussianLaw N).map
      (olsCovariateVector (N := N))) := by
    exact (integrable_map_measure hg.aestronglyMeasurable
      measurable_olsCovariateVector.aemeasurable).mpr hpair
  simpa only [olsPairGaussianLaw_covariate_map] using hmap

private lemma integral_olsDesignStat_eq_pair {N : ℕ} {g : (Fin N → ℝ) → ℝ}
    (hgInt : Integrable g (olsDesignGaussianLaw N)) :
    (∫ x : Fin N → ℝ, g x ∂olsDesignGaussianLaw N) =
      ∫ G : Fin N → ℝ × ℝ, g (olsCovariateVector G) ∂olsPairGaussianLaw N := by
  have hgm : AEStronglyMeasurable g
      ((olsPairGaussianLaw N).map (olsCovariateVector (N := N))) := by
    simpa only [olsPairGaussianLaw_covariate_map] using hgInt.aestronglyMeasurable
  rw [← olsPairGaussianLaw_covariate_map]
  exact integral_map measurable_olsCovariateVector.aemeasurable hgm

private lemma integrable_olsDesignInvCenteredSq {N : ℕ} (hN : 3 < N) :
    Integrable (olsDesignInvCenteredSq (N := N)) (olsDesignGaussianLaw N) := by
  let d := N - 1
  have hd : 2 < d := by dsimp [d]; omega
  have hdim : d + 1 = N := by dsimp [d]; omega
  apply integrable_olsDesignStat_of_pair measurable_olsDesignInvCenteredSq
  rw [← hdim]
  simpa [olsDesignInvCenteredSq, olsCenteredDesign_eq_designCenteredSq] using
    (integrable_inv_olsCenteredDesign_gaussian (d := d) hd)

private lemma integral_olsDesignInvCenteredSq {N : ℕ} (hN : 3 < N) :
    (∫ x : Fin N → ℝ, olsDesignInvCenteredSq x ∂olsDesignGaussianLaw N) =
      1 / ((N : ℝ) - 3) := by
  have hInt := integrable_olsDesignInvCenteredSq hN
  calc
    _ = ∫ G : Fin N → ℝ × ℝ,
          olsDesignInvCenteredSq (olsCovariateVector G) ∂olsPairGaussianLaw N :=
        integral_olsDesignStat_eq_pair hInt
    _ = 1 / ((N : ℝ) - 3) := by
      simpa [olsDesignInvCenteredSq, olsCenteredDesign_eq_designCenteredSq] using
        integral_inv_olsCenteredDesign_gaussian_sample (N := N) hN

private lemma integrable_olsDesignMixedMeanInv {N : ℕ} (hN : 3 < N) :
    Integrable (olsDesignMixedMeanInv (N := N)) (olsDesignGaussianLaw N) := by
  apply integrable_olsDesignStat_of_pair measurable_olsDesignMixedMeanInv
  simpa [olsDesignMixedMeanInv, olsDesignMean, olsXBar_eq_designMean,
    olsCenteredDesign_eq_designCenteredSq] using
    (integrable_olsXBar_sq_div_olsCenteredDesign (N := N) hN)

private lemma integral_olsDesignMixedMeanInv {N : ℕ} (hN : 3 < N) :
    (∫ x : Fin N → ℝ, olsDesignMixedMeanInv x ∂olsDesignGaussianLaw N) =
      1 / ((N : ℝ) * ((N : ℝ) - 3)) := by
  have hInt := integrable_olsDesignMixedMeanInv hN
  calc
    _ = ∫ G : Fin N → ℝ × ℝ,
          olsDesignMixedMeanInv (olsCovariateVector G) ∂olsPairGaussianLaw N :=
        integral_olsDesignStat_eq_pair hInt
    _ = 1 / ((N : ℝ) * ((N : ℝ) - 3)) := by
      simpa [olsDesignMixedMeanInv, olsDesignMean, olsXBar_eq_designMean,
        olsCenteredDesign_eq_designCenteredSq] using
        integral_olsXBar_sq_div_olsCenteredDesign (N := N) hN

private lemma integrable_olsDesignConditionalMoment {N : ℕ} (hN : 3 < N) :
    Integrable (olsDesignConditionalMoment (N := N)) (olsDesignGaussianLaw N) := by
  have hconst : Integrable (fun _ : Fin N → ℝ => 1 / (N : ℝ))
      (olsDesignGaussianLaw N) := integrable_const _
  have hinv := integrable_olsDesignInvCenteredSq hN
  have hmixed := integrable_olsDesignMixedMeanInv hN
  have hfun : olsDesignConditionalMoment (N := N) =
      fun x => 1 / (N : ℝ) + olsDesignInvCenteredSq x +
        olsDesignMixedMeanInv x := by
    funext x
    simp [olsDesignConditionalMoment, olsDesignInvCenteredSq,
      olsDesignMixedMeanInv, div_eq_mul_inv]
    ring
  rw [hfun]
  exact (hconst.add hinv).add hmixed

private lemma olsDesignConditionalMoment_nonneg {N : ℕ} (x : Fin N → ℝ) :
    0 ≤ olsDesignConditionalMoment x := by
  unfold olsDesignConditionalMoment
  apply add_nonneg
  · exact div_nonneg (by positivity) (by positivity)
  · exact div_nonneg (by positivity) (olsCovariateCenteredSq_nonneg x)

private lemma integral_olsDesignConditionalMoment {N : ℕ} (hN : 3 < N) :
    (∫ x : Fin N → ℝ, olsDesignConditionalMoment x ∂olsDesignGaussianLaw N) =
      1 / (N : ℝ) + (1 + 1 / (N : ℝ)) / ((N : ℝ) - 3) := by
  have hconst : Integrable (fun _ : Fin N → ℝ => 1 / (N : ℝ))
      (olsDesignGaussianLaw N) := integrable_const _
  have hinv := integrable_olsDesignInvCenteredSq hN
  have hmixed := integrable_olsDesignMixedMeanInv hN
  have hfun : olsDesignConditionalMoment (N := N) =
      fun x => 1 / (N : ℝ) + olsDesignInvCenteredSq x +
        olsDesignMixedMeanInv x := by
    funext x
    simp [olsDesignConditionalMoment, olsDesignInvCenteredSq,
      olsDesignMixedMeanInv, div_eq_mul_inv]
    ring
  rw [hfun]
  calc
    _ = (∫ x : Fin N → ℝ,
        1 / (N : ℝ) + olsDesignInvCenteredSq x ∂olsDesignGaussianLaw N) +
        ∫ x : Fin N → ℝ, olsDesignMixedMeanInv x ∂olsDesignGaussianLaw N := by
          exact integral_add (hconst.add hinv) hmixed
    _ = (∫ x : Fin N → ℝ, (1 / (N : ℝ)) ∂olsDesignGaussianLaw N) +
        (∫ x : Fin N → ℝ, olsDesignInvCenteredSq x ∂olsDesignGaussianLaw N) +
        ∫ x : Fin N → ℝ, olsDesignMixedMeanInv x ∂olsDesignGaussianLaw N := by
          rw [integral_add hconst hinv]
    _ = 1 / (N : ℝ) + (1 / ((N : ℝ) - 3)) +
        1 / ((N : ℝ) * ((N : ℝ) - 3)) := by
          rw [integral_const, integral_olsDesignInvCenteredSq hN,
            integral_olsDesignMixedMeanInv hN]
          simp [olsDesignGaussianLaw, standardGaussian]
    _ = 1 / (N : ℝ) + (1 + 1 / (N : ℝ)) / ((N : ℝ) - 3) := by
          have hNreal : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
          have hN3 : (0 : ℝ) < (N : ℝ) - 3 := by
            have hNcast : (3 : ℝ) < (N : ℝ) := by exact_mod_cast hN
            linarith
          field_simp
          ring

private noncomputable def olsReorderedNoisePredictorSq {N : ℕ} :
    (Fin N → ℝ) × (ℝ × (Fin N → ℝ)) → ℝ := fun z =>
  (olsNoisePredictor (fun i => (z.1 i, z.2.2 i)) z.2.1) ^ 2

private noncomputable def olsActualNoisePredictorSq {N : ℕ} :
    ((Fin N → ℝ × ℝ) × ℝ) → ℝ := fun p =>
  (olsNoisePredictor p.1 p.2) ^ 2

private lemma measurable_olsReorderedNoisePredictorSq {N : ℕ} :
    Measurable (olsReorderedNoisePredictorSq (N := N)) := by
  unfold olsReorderedNoisePredictorSq
  fun_prop [olsNoisePredictor, olsEBar, olsNoiseSlope, olsCenteredCross,
    olsCenteredDesign, olsXBar]

private lemma olsReorderedNoisePredictorSq_comp_reorder {N : ℕ}
    (p : (Fin N → ℝ × ℝ) × ℝ) :
    olsReorderedNoisePredictorSq (olsPairTestReorderEquiv N p) =
      olsActualNoisePredictorSq p := by
  rcases p with ⟨G, u⟩
  rfl

private lemma integral_olsReorderedNoisePredictorSq_fiber {N : ℕ}
    (hN : 3 < N) (x : Fin N → ℝ)
    (hs : 0 < olsCovariateCenteredSq x) :
    (∫ p : ℝ × (Fin N → ℝ),
      olsReorderedNoisePredictorSq (x, p) ∂
        (standardGaussian.prod (olsNoiseGaussianVectorLaw N))) =
      olsDesignConditionalMoment x := by
  simpa [olsReorderedNoisePredictorSq, olsDesignConditionalMoment,
    olsDesignMean, olsCovariateCenteredSq] using
    olsNoisePredictor_independentTest_secondMoment (r := N) (by omega) x hs

private lemma lintegral_olsReorderedNoisePredictorSq_fiber {N : ℕ}
    (hN : 3 < N) (x : Fin N → ℝ)
    (hs : 0 < olsCovariateCenteredSq x) :
    (∫⁻ p : ℝ × (Fin N → ℝ),
      ‖olsReorderedNoisePredictorSq (x, p)‖ₑ ∂
        (standardGaussian.prod (olsNoiseGaussianVectorLaw N))) =
      ENNReal.ofReal (olsDesignConditionalMoment x) := by
  let f : ℝ × (Fin N → ℝ) → ℝ := fun p => olsReorderedNoisePredictorSq (x, p)
  have hfInt : Integrable f (standardGaussian.prod (olsNoiseGaussianVectorLaw N)) := by
    simpa [f, olsReorderedNoisePredictorSq] using
      olsNoisePredictor_sq_integrable_product (r := N) (by omega) x hs
  have hfnonneg : ∀ᵐ p : ℝ × (Fin N → ℝ) ∂
      (standardGaussian.prod (olsNoiseGaussianVectorLaw N)), 0 ≤ f p :=
    ae_of_all _ fun p => sq_nonneg _
  calc
    _ = ∫⁻ p : ℝ × (Fin N → ℝ), ENNReal.ofReal (f p) ∂
        (standardGaussian.prod (olsNoiseGaussianVectorLaw N)) := by
      apply lintegral_congr_ae
      filter_upwards with p
      exact Real.enorm_eq_ofReal (sq_nonneg _)
    _ = ENNReal.ofReal (∫ p : ℝ × (Fin N → ℝ), f p ∂
        (standardGaussian.prod (olsNoiseGaussianVectorLaw N))) := by
      symm
      exact ofReal_integral_eq_lintegral_ofReal hfInt hfnonneg
    _ = ENNReal.ofReal (olsDesignConditionalMoment x) := by
      rw [integral_olsReorderedNoisePredictorSq_fiber hN x hs]

private lemma lintegral_olsReorderedNoisePredictorSq {N : ℕ} (hN : 3 < N) :
    (∫⁻ z : (Fin N → ℝ) × (ℝ × (Fin N → ℝ)),
      ‖olsReorderedNoisePredictorSq z‖ₑ ∂
        ((olsDesignGaussianLaw N).prod
          (standardGaussian.prod (olsNoiseGaussianVectorLaw N)))) =
      ENNReal.ofReal
        (1 / (N : ℝ) + (1 + 1 / (N : ℝ)) / ((N : ℝ) - 3)) := by
  let f : (Fin N → ℝ) × (ℝ × (Fin N → ℝ)) → ℝ≥0∞ := fun z =>
    ‖olsReorderedNoisePredictorSq z‖ₑ
  have hf : Measurable f := by
    dsimp [f]
    exact measurable_olsReorderedNoisePredictorSq.enorm
  calc
    _ = ∫⁻ x : Fin N → ℝ, ∫⁻ p : ℝ × (Fin N → ℝ),
          f (x, p) ∂(standardGaussian.prod (olsNoiseGaussianVectorLaw N))
          ∂olsDesignGaussianLaw N := by
      exact lintegral_prod f hf.aemeasurable
    _ = ∫⁻ x : Fin N → ℝ,
          ENNReal.ofReal (olsDesignConditionalMoment x) ∂olsDesignGaussianLaw N := by
      apply lintegral_congr_ae
      filter_upwards [ae_olsDesignCenteredSq_pos (N := N) (by omega)] with x hx
      exact lintegral_olsReorderedNoisePredictorSq_fiber hN x hx
    _ = ENNReal.ofReal
        (1 / (N : ℝ) + (1 + 1 / (N : ℝ)) / ((N : ℝ) - 3)) := by
      calc
        _ = ENNReal.ofReal
            (∫ x : Fin N → ℝ, olsDesignConditionalMoment x ∂
              olsDesignGaussianLaw N) := by
          symm
          apply ofReal_integral_eq_lintegral_ofReal
            (integrable_olsDesignConditionalMoment hN)
          exact ae_of_all _ olsDesignConditionalMoment_nonneg
        _ = _ := by rw [integral_olsDesignConditionalMoment hN]

private theorem integrable_olsReorderedNoisePredictorSq {N : ℕ} (hN : 3 < N) :
    Integrable (olsReorderedNoisePredictorSq (N := N))
      ((olsDesignGaussianLaw N).prod
        (standardGaussian.prod (olsNoiseGaussianVectorLaw N))) := by
  refine ⟨measurable_olsReorderedNoisePredictorSq.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  rw [lintegral_olsReorderedNoisePredictorSq hN]
  exact ENNReal.ofReal_lt_top

theorem integrable_olsNoisePredictor_sq_gaussian {N : ℕ} (hN : 3 < N) :
    Integrable (fun p : (Fin N → ℝ × ℝ) × ℝ =>
      (olsNoisePredictor p.1 p.2) ^ 2)
      ((olsPairGaussianLaw N).prod standardGaussian) := by
  have hcomp := (measurePreserving_olsPairTestReorder N).integrable_comp_of_integrable
    (integrable_olsReorderedNoisePredictorSq hN)
  have hEq : (olsReorderedNoisePredictorSq (N := N) ∘
      olsPairTestReorderEquiv N) = (fun p : (Fin N → ℝ × ℝ) × ℝ =>
        (olsNoisePredictor p.1 p.2) ^ 2) := by
    funext p
    exact olsReorderedNoisePredictorSq_comp_reorder p
  rw [hEq] at hcomp
  exact hcomp

theorem integral_olsNoisePredictor_sq_gaussian {N : ℕ} (hN : 3 < N) :
    (∫ p : (Fin N → ℝ × ℝ) × ℝ, (olsNoisePredictor p.1 p.2) ^ 2
      ∂((olsPairGaussianLaw N).prod standardGaussian)) =
      1 / (N : ℝ) + (1 + 1 / (N : ℝ)) / ((N : ℝ) - 3) := by
  let μ : Measure ((Fin N → ℝ) × (ℝ × (Fin N → ℝ))) :=
    (olsDesignGaussianLaw N).prod
      (standardGaussian.prod (olsNoiseGaussianVectorLaw N))
  have hInt := integrable_olsReorderedNoisePredictorSq hN
  calc
    _ = ∫ p : (Fin N → ℝ × ℝ) × ℝ,
        olsReorderedNoisePredictorSq (olsPairTestReorderEquiv N p)
        ∂((olsPairGaussianLaw N).prod standardGaussian) := by
      apply integral_congr_ae
      exact ae_of_all _ (olsReorderedNoisePredictorSq_comp_reorder (N := N))
    _ = ∫ z : (Fin N → ℝ) × (ℝ × (Fin N → ℝ)),
        olsReorderedNoisePredictorSq z ∂μ := by
      exact (measurePreserving_olsPairTestReorder N).integral_comp'
        (olsReorderedNoisePredictorSq (N := N))
    _ = ∫ x : Fin N → ℝ,
        ∫ p : ℝ × (Fin N → ℝ), olsReorderedNoisePredictorSq (x, p)
          ∂(standardGaussian.prod (olsNoiseGaussianVectorLaw N))
        ∂olsDesignGaussianLaw N := by
      exact integral_prod (olsReorderedNoisePredictorSq (N := N)) hInt
    _ = ∫ x : Fin N → ℝ, olsDesignConditionalMoment x
        ∂olsDesignGaussianLaw N := by
      apply integral_congr_ae
      filter_upwards [ae_olsDesignCenteredSq_pos (N := N) (by omega)] with x hx
      exact integral_olsReorderedNoisePredictorSq_fiber hN x hx
    _ = 1 / (N : ℝ) + (1 + 1 / (N : ℝ)) / ((N : ℝ) - 3) :=
      integral_olsDesignConditionalMoment hN

#print axioms integrable_olsNoisePredictor_sq_gaussian
#print axioms integral_olsNoisePredictor_sq_gaussian

end LOOConcentration
