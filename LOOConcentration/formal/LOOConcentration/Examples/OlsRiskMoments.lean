import Mathlib.Algebra.Order.Chebyshev
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic
import LOOConcentration.Examples.OlsGoodSetErrorLipschitz
import LOOConcentration.Examples.OlsRandomNoiseMoment

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace LOOConcentration

private noncomputable def olsRiskLossSqAssoc {r : ℕ} :
    ((Fin r → ℝ × ℝ) × ℝ) × ℝ → ℝ := fun p =>
  (p.2 - olsNoisePredictor p.1.1 p.1.2) ^ 2

private lemma standardGaussian_shiftSq_integral_local {c : ℝ} :
    (∫ e : ℝ, (e - c) ^ 2 ∂standardGaussian) = 1 + c ^ 2 := by
  have hmean : (∫ e : ℝ, e ∂standardGaussian) = 0 := by
    simp [standardGaussian]
  have hsecond : (∫ e : ℝ, e ^ 2 ∂standardGaussian) = 1 := by
    calc
      (∫ e : ℝ, e ^ 2 ∂standardGaussian) =
          ProbabilityTheory.variance (fun e : ℝ => e) standardGaussian := by
        symm
        exact ProbabilityTheory.variance_of_integral_eq_zero
          (Measurable.aemeasurable measurable_id') hmean
      _ = 1 := by simp [standardGaussian]
  have hId : Integrable (id : ℝ → ℝ) standardGaussian := by
    change Integrable (id : ℝ → ℝ) (gaussianReal 0 1)
    exact IsGaussian.integrable_id
  have hsq : Integrable (fun e : ℝ => e ^ 2) standardGaussian := by
    have hmem : MemLp (id : ℝ → ℝ) 2 standardGaussian := by
      change MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 1)
      exact IsGaussian.memLp_two_id
    exact hmem.integrable_sq
  have hcross : Integrable (fun e : ℝ => (2 * c) * e) standardGaussian :=
    hId.const_mul _
  calc
    _ = ∫ e : ℝ, (e ^ 2 - (2 * c) * e) + c ^ 2 ∂standardGaussian := by
      apply integral_congr_ae
      exact ae_of_all _ fun e => by ring
    _ = (∫ e : ℝ, e ^ 2 - (2 * c) * e ∂standardGaussian) +
        ∫ _e : ℝ, c ^ 2 ∂standardGaussian :=
      integral_add (hsq.sub hcross) (integrable_const _)
    _ = (∫ e : ℝ, e ^ 2 ∂standardGaussian) -
        ∫ e : ℝ, (2 * c) * e ∂standardGaussian + c ^ 2 := by
      rw [integral_sub hsq hcross, integral_const]
      simp [standardGaussian]
    _ = 1 + c ^ 2 := by
      rw [integral_const_mul, hmean, hsecond]
      ring

private theorem measurable_olsRiskLossSqAssoc {r : ℕ} :
    Measurable (olsRiskLossSqAssoc (r := r)) := by
  have hG : Measurable
      (fun p : ((Fin r → ℝ × ℝ) × ℝ) × ℝ => p.1.1) :=
    measurable_fst.comp measurable_fst
  have hxbar : Measurable
      (fun p : ((Fin r → ℝ × ℝ) × ℝ) × ℝ => olsXBar p.1.1) :=
    measurable_olsXBar.comp hG
  have hEbar : Measurable
      (fun p : ((Fin r → ℝ × ℝ) × ℝ) × ℝ => olsEBar p.1.1) :=
    measurable_olsEBar.comp hG
  have hSlope : Measurable
      (fun p : ((Fin r → ℝ × ℝ) × ℝ) × ℝ => olsNoiseSlope p.1.1) :=
    measurable_olsNoiseSlope.comp hG
  unfold olsRiskLossSqAssoc olsNoisePredictor
  exact (measurable_snd.sub
    (hEbar.add (hSlope.mul ((measurable_snd.comp measurable_fst).sub hxbar)))).pow_const 2

private theorem olsRiskLoss_sq_integrable_product {r : ℕ} (hr : 3 < r) :
    Integrable (fun p : (Fin r → ℝ × ℝ) × (ℝ × ℝ) =>
      (olsRiskLoss p.1 p.2) ^ 2)
      ((olsPairGaussianLaw r).prod olsTestLaw) := by
  let μ₀ : Measure ((Fin r → ℝ × ℝ) × ℝ) :=
    (olsPairGaussianLaw r).prod standardGaussian
  let μ₁ : Measure (((Fin r → ℝ × ℝ) × ℝ) × ℝ) := μ₀.prod standardGaussian
  have hPredSq : Integrable
      (fun p : ((Fin r → ℝ × ℝ) × ℝ) × ℝ =>
        (olsNoisePredictor p.1.1 p.1.2) ^ 2) μ₁ := by
    have hbase := integrable_olsNoisePredictor_sq_gaussian (N := r) hr
    exact (measurePreserving_fst (μ := μ₀) (ν := standardGaussian))
      |>.integrable_comp_of_integrable hbase
  have hNoiseSq : Integrable (fun p : ((Fin r → ℝ × ℝ) × ℝ) × ℝ => p.2 ^ 2) μ₁ := by
    have hbase : Integrable (fun e : ℝ => e ^ 2) standardGaussian := by
      have hmem : MemLp (id : ℝ → ℝ) 2 standardGaussian := by
        change MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 1)
        exact IsGaussian.memLp_two_id
      exact hmem.integrable_sq
    exact (measurePreserving_snd (μ := μ₀) (ν := standardGaussian))
      |>.integrable_comp_of_integrable hbase
  have hfMeas := measurable_olsRiskLossSqAssoc (r := r)
  have hMajor : Integrable
      (fun p : ((Fin r → ℝ × ℝ) × ℝ) × ℝ =>
        2 * (p.2 ^ 2 + (olsNoisePredictor p.1.1 p.1.2) ^ 2)) μ₁ := by
    have hsum := hNoiseSq.add hPredSq
    simpa [mul_add, add_comm, add_left_comm, add_assoc] using hsum.const_mul 2
  have hAssocInt : Integrable (olsRiskLossSqAssoc (r := r)) μ₁ := by
    apply hMajor.mono_nonneg hfMeas.aestronglyMeasurable
    · exact ae_of_all _ fun p => sq_nonneg _
    · filter_upwards with p
      unfold olsRiskLossSqAssoc
      nlinarith [sq_nonneg (p.2 + olsNoisePredictor p.1.1 p.1.2)]
  have hAssoc : MeasurePreserving MeasurableEquiv.prodAssoc μ₁
      ((olsPairGaussianLaw r).prod olsTestLaw) := by
    simpa [μ₀, μ₁, olsTestLaw, olsTestGaussian] using
      (measurePreserving_prodAssoc (olsPairGaussianLaw r)
        standardGaussian standardGaussian)
  have hReorder := hAssoc.symm
  have hComp : (olsRiskLossSqAssoc (r := r) ∘ MeasurableEquiv.prodAssoc.symm) =
      (fun p : (Fin r → ℝ × ℝ) × (ℝ × ℝ) =>
        (olsRiskLoss p.1 p.2) ^ 2) := by
    funext p
    rcases p with ⟨G, ⟨x, e⟩⟩
    simp [olsRiskLossSqAssoc, olsRiskLoss, MeasurableEquiv.prodAssoc]
  have hInt := hReorder.integrable_comp_of_integrable hAssocInt
  rw [hComp] at hInt
  exact hInt

private theorem integral_olsRiskLoss_sq_product {r : ℕ} (hr : 3 < r) :
    (∫ p : (Fin r → ℝ × ℝ) × (ℝ × ℝ),
      (olsRiskLoss p.1 p.2) ^ 2 ∂((olsPairGaussianLaw r).prod olsTestLaw)) =
      1 + (1 / (r : ℝ) + (1 + 1 / (r : ℝ)) / ((r : ℝ) - 3)) := by
  let μ₀ : Measure ((Fin r → ℝ × ℝ) × ℝ) :=
    (olsPairGaussianLaw r).prod standardGaussian
  let μ₁ : Measure (((Fin r → ℝ × ℝ) × ℝ) × ℝ) := μ₀.prod standardGaussian
  have hAssocInt : Integrable (olsRiskLossSqAssoc (r := r)) μ₁ := by
    have hsource := olsRiskLoss_sq_integrable_product hr
    have hReorder : MeasurePreserving MeasurableEquiv.prodAssoc.symm
        ((olsPairGaussianLaw r).prod olsTestLaw) μ₁ := by
      simpa [μ₀, μ₁, olsTestLaw, olsTestGaussian] using
        (measurePreserving_prodAssoc (olsPairGaussianLaw r)
          standardGaussian standardGaussian).symm
    have hComp : (olsRiskLossSqAssoc (r := r) ∘ MeasurableEquiv.prodAssoc.symm) =
        (fun p : (Fin r → ℝ × ℝ) × (ℝ × ℝ) =>
          (olsRiskLoss p.1 p.2) ^ 2) := by
      funext p
      rcases p with ⟨G, ⟨x, e⟩⟩
      simp [olsRiskLossSqAssoc, olsRiskLoss, MeasurableEquiv.prodAssoc]
    have hsource' :
        Integrable
          (olsRiskLossSqAssoc (r := r) ∘ MeasurableEquiv.prodAssoc.symm)
          ((olsPairGaussianLaw r).prod olsTestLaw) := by
      rw [hComp]
      exact hsource
    exact (hReorder.integrable_comp
      (measurable_olsRiskLossSqAssoc (r := r)).aestronglyMeasurable).mp hsource'
  have hPredSq : Integrable
      (fun p : (Fin r → ℝ × ℝ) × ℝ => (olsNoisePredictor p.1 p.2) ^ 2) μ₀ := by
    simpa [μ₀] using integrable_olsNoisePredictor_sq_gaussian (N := r) hr
  have hIntegral := integral_olsNoisePredictor_sq_gaussian (N := r) hr
  have hProd : (∫ p : ((Fin r → ℝ × ℝ) × ℝ) × ℝ,
      olsRiskLossSqAssoc (r := r) p ∂μ₁) =
      ∫ w : (Fin r → ℝ × ℝ) × ℝ,
        ∫ e : ℝ, olsRiskLossSqAssoc (r := r) (w, e) ∂standardGaussian ∂μ₀ :=
    integral_prod (olsRiskLossSqAssoc (r := r)) hAssocInt
  have hFiber (w : (Fin r → ℝ × ℝ) × ℝ) :
      (∫ e : ℝ, olsRiskLossSqAssoc (r := r) (w, e) ∂standardGaussian) =
        1 + (olsNoisePredictor w.1 w.2) ^ 2 := by
    simpa [olsRiskLossSqAssoc] using
      (standardGaussian_shiftSq_integral_local
        (c := olsNoisePredictor w.1 w.2))
  have hVal : (∫ w : (Fin r → ℝ × ℝ) × ℝ,
      1 + (olsNoisePredictor w.1 w.2) ^ 2 ∂μ₀) =
      1 + (1 / (r : ℝ) + (1 + 1 / (r : ℝ)) / ((r : ℝ) - 3)) := by
    rw [integral_add (integrable_const 1) hPredSq, integral_const]
    have hmass : μ₀.real Set.univ = 1 := by
      simp [μ₀, olsPairGaussianLaw, standardGaussian]
    rw [hmass]
    simp only [one_smul]
    rw [hIntegral]
  have hSourceTarget : MeasurePreserving MeasurableEquiv.prodAssoc.symm
      ((olsPairGaussianLaw r).prod olsTestLaw) μ₁ := by
    simpa [μ₀, μ₁, olsTestLaw, olsTestGaussian] using
      (measurePreserving_prodAssoc (olsPairGaussianLaw r)
        standardGaussian standardGaussian).symm
  have hComp : (olsRiskLossSqAssoc (r := r) ∘ MeasurableEquiv.prodAssoc.symm) =
      (fun p : (Fin r → ℝ × ℝ) × (ℝ × ℝ) =>
        (olsRiskLoss p.1 p.2) ^ 2) := by
    funext p
    rcases p with ⟨G, ⟨x, e⟩⟩
    simp [olsRiskLossSqAssoc, olsRiskLoss, MeasurableEquiv.prodAssoc]
  calc
    _ = ∫ p : (Fin r → ℝ × ℝ) × (ℝ × ℝ),
        olsRiskLossSqAssoc (r := r) (MeasurableEquiv.prodAssoc.symm p)
        ∂((olsPairGaussianLaw r).prod olsTestLaw) := by
      apply integral_congr_ae
      exact ae_of_all _ fun p => by
        exact (congrFun hComp p).symm
    _ = ∫ p : ((Fin r → ℝ × ℝ) × ℝ) × ℝ,
        olsRiskLossSqAssoc (r := r) p ∂μ₁ :=
      hSourceTarget.integral_comp' (olsRiskLossSqAssoc (r := r))
    _ = 1 + (1 / (r : ℝ) + (1 + 1 / (r : ℝ)) / ((r : ℝ) - 3)) := by
      rw [hProd]
      calc
        _ = ∫ w : (Fin r → ℝ × ℝ) × ℝ,
            1 + (olsNoisePredictor w.1 w.2) ^ 2 ∂μ₀ := by
          apply integral_congr_ae
          exact ae_of_all _ hFiber
        _ = _ := hVal

private theorem olsRiskLoss_sq_integrable_testLaw {r : ℕ}
    (G : Fin r → ℝ × ℝ) :
    Integrable (fun z : ℝ × ℝ => (olsRiskLoss G z) ^ 2) olsTestLaw := by
  have htestSq : Integrable (fun x : ℝ => x ^ 2) olsTestGaussian := by
    have hmem : MemLp (id : ℝ → ℝ) 2 olsTestGaussian := by
      change MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 1)
      exact IsGaussian.memLp_two_id
    exact hmem.integrable_sq
  have hxSq : Integrable (fun z : ℝ × ℝ => z.1 ^ 2) olsTestLaw :=
    (measurePreserving_fst (μ := olsTestGaussian) (ν := olsTestGaussian))
      |>.integrable_comp_of_integrable htestSq
  have heSq : Integrable (fun z : ℝ × ℝ => z.2 ^ 2) olsTestLaw :=
    (measurePreserving_snd (μ := olsTestGaussian) (ν := olsTestGaussian))
      |>.integrable_comp_of_integrable htestSq
  have hPredMeas : Measurable (fun z : ℝ × ℝ => olsNoisePredictor G z.1) := by
    have hEbar : Measurable (fun _ : ℝ × ℝ => olsEBar G) := measurable_const
    have hSlope : Measurable (fun _ : ℝ × ℝ => olsNoiseSlope G) := measurable_const
    have hxbar : Measurable (fun _ : ℝ × ℝ => olsXBar G) := measurable_const
    unfold olsNoisePredictor
    exact hEbar.add (hSlope.mul (measurable_fst.sub hxbar))
  have hPredSq : Integrable
      (fun z : ℝ × ℝ => (olsNoisePredictor G z.1) ^ 2) olsTestLaw := by
    let c : ℝ := olsEBar G - olsNoiseSlope G * olsXBar G
    let b : ℝ := olsNoiseSlope G
    have hlin : Integrable (fun z : ℝ × ℝ => (b * z.1) ^ 2) olsTestLaw := by
      simpa [mul_pow] using hxSq.const_mul (b ^ 2)
    have hconst : Integrable (fun _ : ℝ × ℝ => c ^ 2) olsTestLaw := integrable_const _
    have hmajor : Integrable
        (fun z : ℝ × ℝ => 2 * ((b * z.1) ^ 2 + c ^ 2)) olsTestLaw := by
      simpa [mul_add, add_comm, add_left_comm, add_assoc] using
        (hlin.add hconst).const_mul 2
    apply hmajor.mono_nonneg (hPredMeas.pow_const 2).aestronglyMeasurable
    · exact ae_of_all _ fun z => sq_nonneg _
    · filter_upwards with z
      have hPred : olsNoisePredictor G z.1 = b * z.1 + c := by
        simp [b, c, olsNoisePredictor]
        ring
      rw [hPred]
      nlinarith [sq_nonneg (b * z.1 - c)]
  have hLossMeas : Measurable (fun z : ℝ × ℝ => olsRiskLoss G z) := by
    unfold olsRiskLoss
    exact measurable_abs.comp (measurable_snd.sub hPredMeas)
  have hmajor : Integrable
      (fun z : ℝ × ℝ => 2 * (z.2 ^ 2 + (olsNoisePredictor G z.1) ^ 2)) olsTestLaw := by
    simpa [mul_add, add_comm, add_left_comm, add_assoc] using
      (heSq.add hPredSq).const_mul 2
  apply hmajor.mono_nonneg (hLossMeas.pow_const 2).aestronglyMeasurable
  · exact ae_of_all _ fun z => sq_nonneg _
  · filter_upwards with z
    simp only [olsRiskLoss, sq_abs]
    nlinarith [sq_nonneg (z.2 + olsNoisePredictor G z.1)]

private theorem olsTestRisk_sq_le_integral {r : ℕ}
    (G : Fin r → ℝ × ℝ) :
    olsTestRisk G ^ 2 ≤ ∫ z : ℝ × ℝ, (olsRiskLoss G z) ^ 2 ∂olsTestLaw := by
  have hLossMeas : AEStronglyMeasurable (olsRiskLoss G) olsTestLaw :=
    (olsTestRiskLoss_integrable G).aestronglyMeasurable
  have hLossSq := olsRiskLoss_sq_integrable_testLaw G
  have hmemLoss0 : MemLp (olsRiskLoss G) 2 olsTestLaw :=
    (memLp_two_iff_integrable_sq hLossMeas).2 (by
      simpa [sq_abs] using hLossSq)
  have hmemLoss : MemLp (olsRiskLoss G) (ENNReal.ofReal 2) olsTestLaw := by
    simpa using hmemLoss0
  have hmemOne : MemLp (fun _ : ℝ × ℝ => (1 : ℝ)) (ENNReal.ofReal 2) olsTestLaw :=
    memLp_const 1
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := olsTestLaw) (p := 2) (q := 2) Real.HolderConjugate.two_two
    (f := olsRiskLoss G) (g := fun _ : ℝ × ℝ => (1 : ℝ))
    (ae_of_all _ fun z => abs_nonneg _)
    (ae_of_all _ fun _ => (show 0 ≤ (1 : ℝ) by norm_num))
    hmemLoss hmemOne
  have hRiskNonneg : 0 ≤ olsTestRisk G := by
    unfold olsTestRisk
    exact integral_nonneg_of_ae (ae_of_all _ fun z => abs_nonneg _)
  have hLossSqNonneg : 0 ≤ ∫ z : ℝ × ℝ, (olsRiskLoss G z) ^ 2 ∂olsTestLaw :=
    integral_nonneg_of_ae (ae_of_all _ fun z => sq_nonneg _)
  have hCauchy : olsTestRisk G ≤ Real.sqrt
      (∫ z : ℝ × ℝ, (olsRiskLoss G z) ^ 2 ∂olsTestLaw) := by
    have hHolder' : olsTestRisk G ≤
        (∫ z : ℝ × ℝ, (olsRiskLoss G z) ^ 2 ∂olsTestLaw) ^ (1 / 2 : ℝ) := by
      simpa [olsTestRisk, integral_const] using hHolder
    simpa [Real.sqrt_eq_rpow] using hHolder'
  have hsqrtNonneg := Real.sqrt_nonneg
    (∫ z : ℝ × ℝ, (olsRiskLoss G z) ^ 2 ∂olsTestLaw)
  have hmul := mul_nonneg (sub_nonneg.mpr hCauchy)
    (add_nonneg hsqrtNonneg hRiskNonneg)
  nlinarith [Real.sq_sqrt hLossSqNonneg]

private theorem olsTestRisk_sq_integrable_gaussian {r : ℕ} (hr : 3 < r) :
    Integrable (fun G : Fin r → ℝ × ℝ => (olsTestRisk G) ^ 2)
      (olsPairGaussianLaw r) := by
  have hjoint := olsRiskLoss_sq_integrable_product hr
  have hinner := hjoint.integral_prod_left
  apply hinner.mono_nonneg (measurable_olsTestRisk.pow_const 2).aestronglyMeasurable
  · exact ae_of_all _ fun G => sq_nonneg _
  · filter_upwards with G
    exact olsTestRisk_sq_le_integral G

theorem integrable_olsTestRisk_sq_gaussian {r : ℕ} (hr : 3 < r) :
    Integrable (fun G : Fin r → ℝ × ℝ => (olsTestRisk G) ^ 2)
      (olsPairGaussianLaw r) :=
  olsTestRisk_sq_integrable_gaussian hr

private theorem olsTestRisk_nonneg {r : ℕ} (G : Fin r → ℝ × ℝ) :
    0 ≤ olsTestRisk G := by
  unfold olsTestRisk
  exact integral_nonneg_of_ae (ae_of_all _ fun z => abs_nonneg _)

theorem integrable_olsTestRisk_gaussian {r : ℕ} (hr : 3 < r) :
    Integrable (olsTestRisk : (Fin r → ℝ × ℝ) → ℝ) (olsPairGaussianLaw r) := by
  have hsq := integrable_olsTestRisk_sq_gaussian hr
  have hmajor : Integrable (fun G : Fin r → ℝ × ℝ => 1 + (olsTestRisk G) ^ 2)
      (olsPairGaussianLaw r) := (integrable_const 1).add hsq
  apply hmajor.mono_nonneg measurable_olsTestRisk.aestronglyMeasurable
  · exact ae_of_all _ olsTestRisk_nonneg
  · filter_upwards with G
    have h := olsTestRisk_nonneg G
    nlinarith [sq_nonneg (olsTestRisk G - (1 / 2 : ℝ))]

theorem integral_olsTestRisk_sq_gaussian_le {r : ℕ} (hr : 3 < r) :
    (∫ G : Fin r → ℝ × ℝ, (olsTestRisk G) ^ 2 ∂olsPairGaussianLaw r) ≤
      1 + (1 / (r : ℝ) + (1 + 1 / (r : ℝ)) / ((r : ℝ) - 3)) := by
  have hjoint := olsRiskLoss_sq_integrable_product hr
  have hinner := hjoint.integral_prod_left
  have hRiskSq := olsTestRisk_sq_integrable_gaussian hr
  have hle := integral_mono_ae hRiskSq hinner (ae_of_all _ olsTestRisk_sq_le_integral)
  calc
    _ ≤ ∫ G : Fin r → ℝ × ℝ,
        ∫ z : ℝ × ℝ, (olsRiskLoss G z) ^ 2 ∂olsTestLaw ∂olsPairGaussianLaw r := hle
    _ = ∫ p : (Fin r → ℝ × ℝ) × (ℝ × ℝ),
        (olsRiskLoss p.1 p.2) ^ 2 ∂((olsPairGaussianLaw r).prod olsTestLaw) :=
      (integral_prod _ hjoint).symm
    _ = _ := integral_olsRiskLoss_sq_product hr

private theorem measurePreserving_olsDeletedHeldout {n : ℕ} (i : Fin (n + 2)) :
    MeasurePreserving (fun G : Fin (n + 2) → ℝ × ℝ => (deleteAt G i, G i))
      (olsPairGaussianLaw (n + 2))
      ((olsPairGaussianLaw (n + 1)).prod olsTestLaw) := by
  have h := Measure.measurePreserving_swap.comp
    (measurePreserving_piFinSuccAbove
      (fun _ : Fin (n + 2) => standardGaussian.prod standardGaussian) i)
  change MeasurePreserving
    (fun G : Fin (n + 2) → ℝ × ℝ =>
      (fun j : Fin (n + 1) => G (i.succAbove j), G i))
    (Measure.pi fun _ : Fin (n + 2) => standardGaussian.prod standardGaussian)
    ((Measure.pi fun _ : Fin (n + 1) => standardGaussian.prod standardGaussian).prod
      (standardGaussian.prod standardGaussian)) at h
  change MeasurePreserving
    (fun G : Fin (n + 2) → ℝ × ℝ =>
      (fun j : Fin (n + 1) => G (i.succAbove j), G i))
    (Measure.pi fun _ : Fin (n + 2) => standardGaussian.prod standardGaussian)
    ((Measure.pi fun _ : Fin (n + 1) => standardGaussian.prod standardGaussian).prod
      (standardGaussian.prod standardGaussian))
  exact h

private noncomputable def olsValidationSummand {n : ℕ}
    (G : Fin (n + 2) → ℝ × ℝ) (i : Fin (n + 2)) : ℝ :=
  |(G i).2 - olsNoisePredictor (deleteAt G i) (G i).1|

private theorem olsValidation_sq_le_average {n : ℕ}
    (G : Fin (n + 2) → ℝ × ℝ) :
    (olsValidationError G) ^ 2 ≤
      (1 / (n + 2 : ℝ)) * ∑ i : Fin (n + 2), olsValidationSummand G i ^ 2 := by
  let m : ℝ := n + 2
  have hm : 0 < m := by positivity
  have hcard : (((Finset.univ : Finset (Fin (n + 2))).card : ℕ) : ℝ) = m := by
    simp [m]
  have hcs :
      (∑ i : Fin (n + 2), olsValidationSummand G i) ^ 2 ≤
      m * ∑ i : Fin (n + 2), olsValidationSummand G i ^ 2 := by
    simpa [m, hcard] using
      (sq_sum_le_card_mul_sum_sq (α := ℝ)
        (s := (Finset.univ : Finset (Fin (n + 2))))
        (f := fun i => olsValidationSummand G i))
  rw [olsValidationError, div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hm)).2
  calc
    (∑ i : Fin (n + 2), olsValidationSummand G i) ^ 2 ≤
        m * ∑ i : Fin (n + 2), olsValidationSummand G i ^ 2 := hcs
    _ = (1 / m * ∑ i : Fin (n + 2), olsValidationSummand G i ^ 2) * m ^ 2 := by
      field_simp [ne_of_gt hm]

private theorem integrable_olsValidationSummand_sq {n : ℕ} (hn : 3 < n + 1)
    (i : Fin (n + 2)) :
    Integrable (fun G : Fin (n + 2) → ℝ × ℝ => olsValidationSummand G i ^ 2)
      (olsPairGaussianLaw (n + 2)) := by
  have hproduct := olsRiskLoss_sq_integrable_product (r := n + 1) hn
  have hcomp := (measurePreserving_olsDeletedHeldout i).integrable_comp_of_integrable hproduct
  have hEq : (fun G : Fin (n + 2) → ℝ × ℝ =>
      olsRiskLoss (deleteAt G i) (G i) ^ 2) =
      (fun G => olsValidationSummand G i ^ 2) := by
    funext G
    simp [olsValidationSummand, olsRiskLoss]
  have hcomp' : Integrable
      (fun G : Fin (n + 2) → ℝ × ℝ => olsRiskLoss (deleteAt G i) (G i) ^ 2)
      (olsPairGaussianLaw (n + 2)) := by
    change Integrable (fun G : Fin (n + 2) → ℝ × ℝ =>
      olsRiskLoss (deleteAt G i) (G i) ^ 2) (olsPairGaussianLaw (n + 2)) at hcomp
    exact hcomp
  rw [← hEq]
  exact hcomp'

private theorem integral_olsValidationSummand_sq {n : ℕ} (hn : 3 < n + 1)
    (i : Fin (n + 2)) :
    (∫ G : Fin (n + 2) → ℝ × ℝ, olsValidationSummand G i ^ 2
      ∂olsPairGaussianLaw (n + 2)) =
      1 + (1 / ((n + 1 : ℕ) : ℝ) +
        (1 + 1 / ((n + 1 : ℕ) : ℝ)) / ((n + 1 : ℕ) - 3 : ℝ)) := by
  let hmp := measurePreserving_olsDeletedHeldout i
  have hcomp : (fun G : Fin (n + 2) → ℝ × ℝ =>
      olsRiskLoss (deleteAt G i) (G i) ^ 2) =
      (fun G => olsValidationSummand G i ^ 2) := by
    funext G
    simp [olsValidationSummand, olsRiskLoss]
  calc
    _ = ∫ G : Fin (n + 2) → ℝ × ℝ,
        olsRiskLoss (deleteAt G i) (G i) ^ 2 ∂olsPairGaussianLaw (n + 2) := by
      exact integral_congr_ae (ae_of_all _ fun G => (congrFun hcomp G).symm)
    _ = ∫ p : (Fin (n + 1) → ℝ × ℝ) × (ℝ × ℝ),
        olsRiskLoss p.1 p.2 ^ 2 ∂((olsPairGaussianLaw (n + 1)).prod olsTestLaw) := by
      have hproduct := olsRiskLoss_sq_integrable_product (r := n + 1) hn
      have hmap := hmp.map_eq
      have hfm : AEStronglyMeasurable
          (fun p : (Fin (n + 1) → ℝ × ℝ) × (ℝ × ℝ) => olsRiskLoss p.1 p.2 ^ 2)
          ((olsPairGaussianLaw (n + 2)).map
            (fun G : Fin (n + 2) → ℝ × ℝ => (deleteAt G i, G i))) := by
        rw [hmap]
        exact hproduct.aestronglyMeasurable
      rw [← hmap]
      exact (integral_map hmp.measurable.aemeasurable hfm).symm
    _ = _ := integral_olsRiskLoss_sq_product hn

theorem integrable_olsValidationError_sq_gaussian {n : ℕ} (hn : 3 < n + 1) :
    Integrable (fun G : Fin (n + 2) → ℝ × ℝ => (olsValidationError G) ^ 2)
      (olsPairGaussianLaw (n + 2)) := by
  let μ := olsPairGaussianLaw (n + 2)
  let f : Fin (n + 2) → (Fin (n + 2) → ℝ × ℝ) → ℝ :=
    fun i G => olsValidationSummand G i
  have hsumSq : Integrable (fun G => ∑ i : Fin (n + 2), f i G ^ 2) μ := by
    refine integrable_finsetSum Finset.univ ?_
    intro i hi
    exact integrable_olsValidationSummand_sq hn i
  have hmajor : Integrable
      (fun G => (1 / (n + 2 : ℝ)) * ∑ i : Fin (n + 2), f i G ^ 2) μ :=
    hsumSq.const_mul _
  have hmeas : Measurable (fun G : Fin (n + 2) → ℝ × ℝ =>
      (olsValidationError G) ^ 2) :=
    (measurable_olsValidationError.pow_const 2)
  apply hmajor.mono_nonneg hmeas.aestronglyMeasurable
  · exact ae_of_all _ fun G => sq_nonneg _
  · filter_upwards with G
    simpa [f] using olsValidation_sq_le_average G

theorem integral_olsValidationError_sq_gaussian_le {n : ℕ} (hn : 3 < n + 1) :
    (∫ G : Fin (n + 2) → ℝ × ℝ, (olsValidationError G) ^ 2
      ∂olsPairGaussianLaw (n + 2)) ≤
      1 + (1 / ((n + 1 : ℕ) : ℝ) +
        (1 + 1 / ((n + 1 : ℕ) : ℝ)) / ((n + 1 : ℕ) - 3 : ℝ)) := by
  let μ := olsPairGaussianLaw (n + 2)
  let f : Fin (n + 2) → (Fin (n + 2) → ℝ × ℝ) → ℝ :=
    fun i G => olsValidationSummand G i
  have hsumSq : Integrable (fun G => ∑ i : Fin (n + 2), f i G ^ 2) μ := by
    refine integrable_finsetSum Finset.univ ?_
    intro i hi
    exact integrable_olsValidationSummand_sq hn i
  have hmajor : Integrable
      (fun G => (1 / (n + 2 : ℝ)) * ∑ i : Fin (n + 2), f i G ^ 2) μ :=
    hsumSq.const_mul _
  have hValSq : Integrable (fun G : Fin (n + 2) → ℝ × ℝ =>
      (olsValidationError G) ^ 2) μ := integrable_olsValidationError_sq_gaussian hn
  have hle : (∫ G : Fin (n + 2) → ℝ × ℝ, (olsValidationError G) ^ 2 ∂μ) ≤
      ∫ G : Fin (n + 2) → ℝ × ℝ,
        (1 / (n + 2 : ℝ)) * ∑ i : Fin (n + 2), f i G ^ 2 ∂μ :=
    integral_mono_ae hValSq hmajor (ae_of_all _ fun G => by
      simpa [f] using olsValidation_sq_le_average G)
  have hsumIntegral : (∫ G : Fin (n + 2) → ℝ × ℝ,
      (1 / (n + 2 : ℝ)) * ∑ i : Fin (n + 2), f i G ^ 2 ∂μ) =
      1 + (1 / ((n + 1 : ℕ) : ℝ) +
        (1 + 1 / ((n + 1 : ℕ) : ℝ)) / ((n + 1 : ℕ) - 3 : ℝ)) := by
    rw [integral_const_mul]
    have hsum : (∫ G : Fin (n + 2) → ℝ × ℝ,
        ∑ i : Fin (n + 2), f i G ^ 2 ∂μ) =
        ∑ i : Fin (n + 2), ∫ G : Fin (n + 2) → ℝ × ℝ, f i G ^ 2 ∂μ := by
      rw [integral_finsetSum]
      intro i hi
      exact integrable_olsValidationSummand_sq hn i
    rw [hsum]
    have hterms : (∑ i : Fin (n + 2),
        ∫ G : Fin (n + 2) → ℝ × ℝ, f i G ^ 2 ∂μ) =
        (n + 2 : ℝ) * (1 + (1 / ((n + 1 : ℕ) : ℝ) +
          (1 + 1 / ((n + 1 : ℕ) : ℝ)) / ((n + 1 : ℕ) - 3 : ℝ))) := by
      let c : ℝ := 1 + (1 / ((n + 1 : ℕ) : ℝ) +
        (1 + 1 / ((n + 1 : ℕ) : ℝ)) / ((n + 1 : ℕ) - 3 : ℝ))
      calc
        _ = ∑ _i : Fin (n + 2), c := by
          apply Finset.sum_congr rfl
          intro i hi
          simpa [f, μ, c] using integral_olsValidationSummand_sq hn i
        _ = (n + 2 : ℝ) * c := by
          simp [c]
          ring
    rw [hterms]
    field_simp
  exact hle.trans_eq hsumIntegral

private theorem olsValidationError_nonneg {n : ℕ}
    (G : Fin (n + 2) → ℝ × ℝ) : 0 ≤ olsValidationError G := by
  unfold olsValidationError
  apply div_nonneg
  · exact Finset.sum_nonneg fun i _ => abs_nonneg _
  · positivity

theorem integrable_olsValidationError_gaussian {n : ℕ} (hn : 3 < n + 1) :
    Integrable (olsValidationError : (Fin (n + 2) → ℝ × ℝ) → ℝ)
      (olsPairGaussianLaw (n + 2)) := by
  have hsq := integrable_olsValidationError_sq_gaussian hn
  have hmajor : Integrable
      (fun G : Fin (n + 2) → ℝ × ℝ => 1 + (olsValidationError G) ^ 2)
      (olsPairGaussianLaw (n + 2)) := (integrable_const 1).add hsq
  apply hmajor.mono_nonneg measurable_olsValidationError.aestronglyMeasurable
  · exact ae_of_all _ olsValidationError_nonneg
  · filter_upwards with G
    have h := olsValidationError_nonneg G
    nlinarith [sq_nonneg (olsValidationError G - (1 / 2 : ℝ))]

private theorem olsFitVariance_le_two {r : ℕ} (hr : 5 ≤ r) :
    1 / (r : ℝ) + (1 + 1 / (r : ℝ)) / ((r : ℝ) - 3) ≤ 2 := by
  have hrR : 5 ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : 0 < (r : ℝ) := by linarith
  have hden : 2 ≤ (r : ℝ) - 3 := by linarith
  have hdenpos : 0 < (r : ℝ) - 3 := by linarith
  have hrecip : 0 ≤ 1 / (r : ℝ) ∧ 1 / (r : ℝ) ≤ 1 := by
    constructor
    · positivity
    · rw [div_le_iff₀ hrpos]
      norm_num
      linarith
  have hnum : 0 ≤ 1 + 1 / (r : ℝ) ∧ 1 + 1 / (r : ℝ) ≤ 2 := by
    constructor <;> linarith
  have hquot : (1 + 1 / (r : ℝ)) / ((r : ℝ) - 3) ≤ 1 := by
    rw [div_le_iff₀ hdenpos]
    linarith
  linarith

private theorem measurable_olsRiskLoss_product {r : ℕ} :
    Measurable (fun p : (Fin r → ℝ × ℝ) × (ℝ × ℝ) => olsRiskLoss p.1 p.2) := by
  have hG : Measurable (fun p : (Fin r → ℝ × ℝ) × (ℝ × ℝ) => p.1) :=
    measurable_fst
  have hxbar : Measurable
      (fun p : (Fin r → ℝ × ℝ) × (ℝ × ℝ) => olsXBar p.1) :=
    measurable_olsXBar.comp hG
  have hEbar : Measurable
      (fun p : (Fin r → ℝ × ℝ) × (ℝ × ℝ) => olsEBar p.1) :=
    measurable_olsEBar.comp hG
  have hSlope : Measurable
      (fun p : (Fin r → ℝ × ℝ) × (ℝ × ℝ) => olsNoiseSlope p.1) :=
    measurable_olsNoiseSlope.comp hG
  have hPredictor : Measurable
      (fun p : (Fin r → ℝ × ℝ) × (ℝ × ℝ) => olsNoisePredictor p.1 p.2.1) := by
    unfold olsNoisePredictor
    exact hEbar.add (hSlope.mul ((measurable_fst.comp measurable_snd).sub hxbar))
  unfold olsRiskLoss
  exact measurable_abs.comp (measurable_snd.snd.sub hPredictor)

private theorem integrable_olsRiskLoss_product {r : ℕ} (hr : 3 < r) :
    Integrable (fun p : (Fin r → ℝ × ℝ) × (ℝ × ℝ) => olsRiskLoss p.1 p.2)
      ((olsPairGaussianLaw r).prod olsTestLaw) := by
  have hsq := olsRiskLoss_sq_integrable_product hr
  have hmajor : Integrable
      (fun p : (Fin r → ℝ × ℝ) × (ℝ × ℝ) =>
        1 + (olsRiskLoss p.1 p.2) ^ 2)
      ((olsPairGaussianLaw r).prod olsTestLaw) :=
    (integrable_const 1).add hsq
  apply hmajor.mono_nonneg
    (measurable_olsRiskLoss_product (r := r)).aestronglyMeasurable
  · exact ae_of_all _ fun p => abs_nonneg _
  · filter_upwards with p
    have h := abs_nonneg (olsRiskLoss p.1 p.2)
    nlinarith [sq_nonneg (olsRiskLoss p.1 p.2 - (1 / 2 : ℝ))]

private theorem integrable_olsTestNoiseAbs :
    Integrable (fun z : ℝ × ℝ => |z.2|) olsTestLaw := by
  have hGauss : Integrable (fun e : ℝ => |e|) olsTestGaussian := by
    change Integrable (fun e : ℝ => |e|) (gaussianReal 0 1)
    exact IsGaussian.integrable_id.abs
  exact (measurePreserving_snd (μ := olsTestGaussian) (ν := olsTestGaussian))
    |>.integrable_comp_of_integrable hGauss

private theorem measurePreserving_olsRiskCovariateMap {r : ℕ} :
    MeasurePreserving
      (fun p : (Fin r → ℝ × ℝ) × (ℝ × ℝ) => (p.1, p.2.1))
      ((olsPairGaussianLaw r).prod olsTestLaw)
      ((olsPairGaussianLaw r).prod standardGaussian) := by
  have hfst : MeasurePreserving (fun z : ℝ × ℝ => z.1) olsTestLaw standardGaussian := by
    simpa [olsTestLaw, olsTestGaussian, standardGaussian] using
      (measurePreserving_fst (μ := olsTestGaussian) (ν := olsTestGaussian))
  exact (MeasurePreserving.id (olsPairGaussianLaw r)).prod hfst

private theorem measurable_olsNoisePredictor_trainCovariate {r : ℕ} :
    Measurable
      (fun p : (Fin r → ℝ × ℝ) × ℝ => olsNoisePredictor p.1 p.2) := by
  have hG : Measurable (fun p : (Fin r → ℝ × ℝ) × ℝ => p.1) := measurable_fst
  have hxbar : Measurable
      (fun p : (Fin r → ℝ × ℝ) × ℝ => olsXBar p.1) := measurable_olsXBar.comp hG
  have hEbar : Measurable
      (fun p : (Fin r → ℝ × ℝ) × ℝ => olsEBar p.1) := measurable_olsEBar.comp hG
  have hSlope : Measurable
      (fun p : (Fin r → ℝ × ℝ) × ℝ => olsNoiseSlope p.1) :=
    measurable_olsNoiseSlope.comp hG
  unfold olsNoisePredictor
  exact hEbar.add (hSlope.mul (measurable_snd.sub hxbar))

private theorem olsNoisePredictor_abs_integrable_gaussian {r : ℕ} (hr : 3 < r) :
    Integrable
      (fun p : (Fin r → ℝ × ℝ) × ℝ => |olsNoisePredictor p.1 p.2|)
      ((olsPairGaussianLaw r).prod standardGaussian) := by
  have hsq := integrable_olsNoisePredictor_sq_gaussian (N := r) hr
  have hmajor : Integrable
      (fun p : (Fin r → ℝ × ℝ) × ℝ =>
        1 + (olsNoisePredictor p.1 p.2) ^ 2)
      ((olsPairGaussianLaw r).prod standardGaussian) :=
    (integrable_const 1).add hsq
  apply hmajor.mono_nonneg
    (measurable_abs.comp measurable_olsNoisePredictor_trainCovariate).aestronglyMeasurable
  · exact ae_of_all _ fun p => abs_nonneg _
  · filter_upwards with p
    change |olsNoisePredictor p.1 p.2| ≤
      1 + (olsNoisePredictor p.1 p.2) ^ 2
    rw [abs_le]
    constructor
    · nlinarith [sq_nonneg (olsNoisePredictor p.1 p.2 + (1 / 2 : ℝ))]
    · nlinarith [sq_nonneg (olsNoisePredictor p.1 p.2 - (1 / 2 : ℝ))]

private theorem olsNoisePredictor_abs_integral_le_sqrt_variance {r : ℕ}
    (hr : 3 < r) :
    (∫ p : (Fin r → ℝ × ℝ) × ℝ,
      |olsNoisePredictor p.1 p.2| ∂((olsPairGaussianLaw r).prod standardGaussian)) ≤
      Real.sqrt (1 / (r : ℝ) + (1 + 1 / (r : ℝ)) / ((r : ℝ) - 3)) := by
  let μ := (olsPairGaussianLaw r).prod standardGaussian
  let f : (Fin r → ℝ × ℝ) × ℝ → ℝ := fun p => olsNoisePredictor p.1 p.2
  have hsq := integrable_olsNoisePredictor_sq_gaussian (N := r) hr
  have hsqf : Integrable (fun p => f p ^ 2) μ := by simpa [f, μ] using hsq
  have hfMeas : Measurable f := by simpa [f] using
    measurable_olsNoisePredictor_trainCovariate (r := r)
  have hmem : MemLp f 2 μ := by
    exact (memLp_two_iff_integrable_sq hfMeas.aestronglyMeasurable).2 hsqf
  have hmemAbs0 : MemLp (fun p => |f p|) 2 μ := by
    simpa [Real.norm_eq_abs] using hmem.norm
  have hmemAbs : MemLp (fun p => |f p|) (ENNReal.ofReal 2) μ := by
    simpa using hmemAbs0
  have hmemOne : MemLp (fun _ : (Fin r → ℝ × ℝ) × ℝ => (1 : ℝ))
      (ENNReal.ofReal 2) μ := memLp_const 1
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := μ) (p := 2) (q := 2) Real.HolderConjugate.two_two
    (f := fun p => |f p|) (g := fun _ => (1 : ℝ))
    (ae_of_all _ fun p => abs_nonneg _)
    (ae_of_all _ fun _ => (show 0 ≤ (1 : ℝ) by norm_num))
    hmemAbs hmemOne
  have hHolder' : (∫ p, |f p| ∂μ) ≤
      (∫ p, (f p) ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
    have hAbsSqNat : (∫ p, (|f p|) ^ 2 ∂μ) =
        ∫ p, (f p) ^ 2 ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ fun p => sq_abs (f p)
    have hAbsSq : (∫ p, (|f p|) ^ (2 : ℝ) ∂μ) =
        ∫ p, (f p) ^ 2 ∂μ := by
      calc
        _ = ∫ p, (|f p|) ^ 2 ∂μ := by
          apply integral_congr_ae
          exact ae_of_all _ fun p => Real.rpow_natCast _ 2
        _ = _ := hAbsSqNat
    have hOneSq : (∫ _p : (Fin r → ℝ × ℝ) × ℝ,
        (1 : ℝ) ^ (2 : ℝ) ∂μ) = 1 := by simp
    calc
      _ = ∫ p, |f p| * (1 : ℝ) ∂μ := by
        congr 1
        funext p
        ring
      _ ≤ (∫ p, (|f p|) ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) *
          (∫ p, (1 : ℝ) ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := hHolder
      _ = _ := by
        have hfirst : (∫ p, (|f p|) ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) =
            (∫ p, (f p) ^ 2 ∂μ) ^ (1 / 2 : ℝ) :=
          congrArg (fun x : ℝ => x ^ (1 / 2 : ℝ)) hAbsSq
        have hsecond : (∫ _p : (Fin r → ℝ × ℝ) × ℝ,
            (1 : ℝ) ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) = 1 := by
          rw [hOneSq]
          norm_num
        calc
          _ = (∫ p, (f p) ^ 2 ∂μ) ^ (1 / 2 : ℝ) *
              (∫ _p : (Fin r → ℝ × ℝ) × ℝ, (1 : ℝ) ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) :=
            congrArg (fun x : ℝ => x *
              (∫ _p : (Fin r → ℝ × ℝ) × ℝ, (1 : ℝ) ^ 2 ∂μ) ^ (1 / 2 : ℝ)) hfirst
          _ = (∫ p, (f p) ^ 2 ∂μ) ^ (1 / 2 : ℝ) * 1 :=
            congrArg (fun x : ℝ => (∫ p, (f p) ^ 2 ∂μ) ^ (1 / 2 : ℝ) * x) hsecond
          _ = _ := by simp
  have hHolder'' : (∫ p, |f p| ∂μ) ≤ Real.sqrt
      (∫ p, (f p) ^ 2 ∂μ) := by
    simpa [Real.sqrt_eq_rpow] using hHolder'
  have hExact := integral_olsNoisePredictor_sq_gaussian (N := r) hr
  calc
    _ ≤ Real.sqrt (∫ p : (Fin r → ℝ × ℝ) × ℝ,
        (olsNoisePredictor p.1 p.2) ^ 2 ∂((olsPairGaussianLaw r).prod standardGaussian)) := by
      simpa [μ, f] using hHolder''
    _ = Real.sqrt (1 / (r : ℝ) + (1 + 1 / (r : ℝ)) / ((r : ℝ) - 3)) := by
      rw [hExact]

private theorem olsNoisePredictor_abs_integrable_product {r : ℕ} (hr : 3 < r) :
    Integrable
      (fun p : (Fin r → ℝ × ℝ) × (ℝ × ℝ) => |olsNoisePredictor p.1 p.2.1|)
      ((olsPairGaussianLaw r).prod olsTestLaw) := by
  have hbase := olsNoisePredictor_abs_integrable_gaussian (r := r) hr
  have hcomp := (measurePreserving_olsRiskCovariateMap (r := r))
    |>.integrable_comp_of_integrable hbase
  change Integrable
    (fun p : (Fin r → ℝ × ℝ) × (ℝ × ℝ) => |olsNoisePredictor p.1 p.2.1|)
    ((olsPairGaussianLaw r).prod olsTestLaw) at hcomp
  exact hcomp

private theorem integral_olsNoisePredictor_abs_joint_eq_native {r : ℕ}
    (hr : 3 < r) :
    (∫ p : (Fin r → ℝ × ℝ) × (ℝ × ℝ),
      |olsNoisePredictor p.1 p.2.1| ∂((olsPairGaussianLaw r).prod olsTestLaw)) =
      ∫ p : (Fin r → ℝ × ℝ) × ℝ,
        |olsNoisePredictor p.1 p.2| ∂((olsPairGaussianLaw r).prod standardGaussian) := by
  let hmp := measurePreserving_olsRiskCovariateMap (r := r)
  let f : (Fin r → ℝ × ℝ) × ℝ → ℝ := fun p => |olsNoisePredictor p.1 p.2|
  have hbase : Integrable f ((olsPairGaussianLaw r).prod standardGaussian) := by
    simpa [f] using olsNoisePredictor_abs_integrable_gaussian (r := r) hr
  have hmap := hmp.map_eq
  have hfm : AEStronglyMeasurable f
      (((olsPairGaussianLaw r).prod olsTestLaw).map
        (fun p : (Fin r → ℝ × ℝ) × (ℝ × ℝ) => (p.1, p.2.1))) := by
    rw [hmap]
    exact hbase.aestronglyMeasurable
  calc
    _ = ∫ p : (Fin r → ℝ × ℝ) × (ℝ × ℝ),
        f (p.1, p.2.1) ∂((olsPairGaussianLaw r).prod olsTestLaw) := by
      congr 1
    _ = ∫ p : (Fin r → ℝ × ℝ) × ℝ,
        f p ∂((olsPairGaussianLaw r).prod standardGaussian) := by
      rw [← hmap]
      exact (integral_map hmp.measurable.aemeasurable hfm).symm

private theorem abs_integral_olsTestRisk_sub_noise_baseline_le {r : ℕ}
    (hr : 3 < r) :
    |(∫ G : Fin r → ℝ × ℝ, olsTestRisk G ∂olsPairGaussianLaw r) -
        ∫ z : ℝ × ℝ, |z.2| ∂olsTestLaw| ≤
      Real.sqrt (1 / (r : ℝ) + (1 + 1 / (r : ℝ)) / ((r : ℝ) - 3)) := by
  let μ := (olsPairGaussianLaw r).prod olsTestLaw
  let loss : (Fin r → ℝ × ℝ) × (ℝ × ℝ) → ℝ := fun p => olsRiskLoss p.1 p.2
  let noise : (Fin r → ℝ × ℝ) × (ℝ × ℝ) → ℝ := fun p => |p.2.2|
  let predictor : (Fin r → ℝ × ℝ) × (ℝ × ℝ) → ℝ :=
    fun p => |olsNoisePredictor p.1 p.2.1|
  have hLoss : Integrable loss μ := by
    simpa [loss, μ] using integrable_olsRiskLoss_product (r := r) hr
  have hNoiseBase : Integrable (fun z : ℝ × ℝ => |z.2|) olsTestLaw :=
    integrable_olsTestNoiseAbs
  have hNoise : Integrable noise μ := by
    have h := (measurePreserving_snd
      (μ := olsPairGaussianLaw r) (ν := olsTestLaw)).integrable_comp_of_integrable
      hNoiseBase
    simpa [noise, Function.comp_def] using h
  have hDelta : Integrable (fun p => loss p - noise p) μ := hLoss.sub hNoise
  have hAbsDelta : Integrable (fun p => |loss p - noise p|) μ := hDelta.abs
  have hPredictor : Integrable predictor μ := by
    simpa [predictor, μ] using olsNoisePredictor_abs_integrable_product (r := r) hr
  have hpoint : ∀ p, |loss p - noise p| ≤ predictor p := by
    intro p
    have h := abs_abs_sub_abs_le_abs_sub
      (p.2.2 - olsNoisePredictor p.1 p.2.1) p.2.2
    simpa [loss, noise, predictor, olsRiskLoss, sub_sub, abs_neg] using h
  have hjointRisk :
      (∫ p : (Fin r → ℝ × ℝ) × (ℝ × ℝ), loss p ∂μ) =
        ∫ G : Fin r → ℝ × ℝ, olsTestRisk G ∂olsPairGaussianLaw r := by
    simpa [loss, μ, olsTestRisk] using integral_prod
      (fun p : (Fin r → ℝ × ℝ) × (ℝ × ℝ) => olsRiskLoss p.1 p.2) hLoss
  have hjointNoise :
      (∫ p : (Fin r → ℝ × ℝ) × (ℝ × ℝ), noise p ∂μ) =
        ∫ z : ℝ × ℝ, |z.2| ∂olsTestLaw := by
    have hprod := integral_prod
      (fun p : (Fin r → ℝ × ℝ) × (ℝ × ℝ) => |p.2.2|) hNoise
    calc
      _ = ∫ G : Fin r → ℝ × ℝ,
          ∫ z : ℝ × ℝ, |z.2| ∂olsTestLaw ∂olsPairGaussianLaw r := by
        simpa [noise, μ] using hprod
      _ = ∫ z : ℝ × ℝ, |z.2| ∂olsTestLaw := by
        simp [olsPairGaussianLaw, standardGaussian]
  calc
    _ = |(∫ p : (Fin r → ℝ × ℝ) × (ℝ × ℝ), loss p ∂μ) -
        ∫ p : (Fin r → ℝ × ℝ) × (ℝ × ℝ), noise p ∂μ| := by
      rw [← hjointRisk, ← hjointNoise]
    _ = |∫ p : (Fin r → ℝ × ℝ) × (ℝ × ℝ), (loss p - noise p) ∂μ| := by
      rw [integral_sub hLoss hNoise]
    _ ≤ ∫ p : (Fin r → ℝ × ℝ) × (ℝ × ℝ), |loss p - noise p| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ p : (Fin r → ℝ × ℝ) × (ℝ × ℝ), predictor p ∂μ :=
      integral_mono_ae hAbsDelta hPredictor (ae_of_all _ hpoint)
    _ = ∫ p : (Fin r → ℝ × ℝ) × (ℝ × ℝ),
        |olsNoisePredictor p.1 p.2.1| ∂μ := by rfl
    _ ≤ Real.sqrt (1 / (r : ℝ) + (1 + 1 / (r : ℝ)) / ((r : ℝ) - 3)) := by
      simpa [μ, predictor] using
        integral_olsNoisePredictor_abs_joint_eq_native (r := r) hr |>.trans_le
          (olsNoisePredictor_abs_integral_le_sqrt_variance (r := r) hr)

private theorem integrable_olsValidationSummand {n : ℕ} (hn : 3 < n + 1)
    (i : Fin (n + 2)) :
    Integrable (fun G : Fin (n + 2) → ℝ × ℝ => olsValidationSummand G i)
      (olsPairGaussianLaw (n + 2)) := by
  have hproduct := integrable_olsRiskLoss_product (r := n + 1) hn
  have hcomp := (measurePreserving_olsDeletedHeldout i).integrable_comp_of_integrable hproduct
  have hEq : (fun G : Fin (n + 2) → ℝ × ℝ =>
      olsRiskLoss (deleteAt G i) (G i)) =
      (fun G => olsValidationSummand G i) := by
    funext G
    simp [olsValidationSummand, olsRiskLoss]
  have hcomp' : Integrable
      (fun G : Fin (n + 2) → ℝ × ℝ => olsRiskLoss (deleteAt G i) (G i))
      (olsPairGaussianLaw (n + 2)) := by
    change Integrable (fun G : Fin (n + 2) → ℝ × ℝ =>
      olsRiskLoss (deleteAt G i) (G i)) (olsPairGaussianLaw (n + 2)) at hcomp
    exact hcomp
  rw [← hEq]
  exact hcomp'

private theorem integral_olsValidationSummand_eq_risk_mean {n : ℕ}
    (hn : 3 < n + 1) (i : Fin (n + 2)) :
    (∫ G : Fin (n + 2) → ℝ × ℝ,
      olsValidationSummand G i ∂olsPairGaussianLaw (n + 2)) =
      ∫ G : Fin (n + 1) → ℝ × ℝ,
        olsTestRisk G ∂olsPairGaussianLaw (n + 1) := by
  have hmp := measurePreserving_olsDeletedHeldout i
  have hproduct := integrable_olsRiskLoss_product (r := n + 1) hn
  have hcomp : (fun G : Fin (n + 2) → ℝ × ℝ =>
      olsRiskLoss (deleteAt G i) (G i)) =
      (fun G => olsValidationSummand G i) := by
    funext G
    simp [olsValidationSummand, olsRiskLoss]
  calc
    _ = ∫ G : Fin (n + 2) → ℝ × ℝ,
        olsRiskLoss (deleteAt G i) (G i) ∂olsPairGaussianLaw (n + 2) := by
      apply integral_congr_ae
      exact ae_of_all _ fun G => (congrFun hcomp G).symm
    _ = ∫ p : (Fin (n + 1) → ℝ × ℝ) × (ℝ × ℝ),
        olsRiskLoss p.1 p.2 ∂((olsPairGaussianLaw (n + 1)).prod olsTestLaw) := by
      have hmap := hmp.map_eq
      have hfm : AEStronglyMeasurable
          (fun p : (Fin (n + 1) → ℝ × ℝ) × (ℝ × ℝ) => olsRiskLoss p.1 p.2)
          ((olsPairGaussianLaw (n + 2)).map
            (fun G : Fin (n + 2) → ℝ × ℝ => (deleteAt G i, G i))) := by
        rw [hmap]
        exact hproduct.aestronglyMeasurable
      rw [← hmap]
      exact (integral_map hmp.measurable.aemeasurable hfm).symm
    _ = ∫ G : Fin (n + 1) → ℝ × ℝ,
        olsTestRisk G ∂olsPairGaussianLaw (n + 1) := by
      simpa [olsTestRisk] using (integral_prod
        (fun p : (Fin (n + 1) → ℝ × ℝ) × (ℝ × ℝ) => olsRiskLoss p.1 p.2)
        hproduct)

theorem integral_olsValidationError_eq_deletedRisk_mean {n : ℕ}
    (hn : 3 < n + 1) :
    (∫ G : Fin (n + 2) → ℝ × ℝ,
      olsValidationError G ∂olsPairGaussianLaw (n + 2)) =
      ∫ G : Fin (n + 1) → ℝ × ℝ,
        olsTestRisk G ∂olsPairGaussianLaw (n + 1) := by
  have hsumInt : Integrable
      (fun G : Fin (n + 2) → ℝ × ℝ =>
        ∑ i : Fin (n + 2), olsValidationSummand G i)
      (olsPairGaussianLaw (n + 2)) := by
    refine integrable_finsetSum Finset.univ ?_
    intro i hi
    exact integrable_olsValidationSummand hn i
  have hsum :
      (∫ G : Fin (n + 2) → ℝ × ℝ,
        ∑ i : Fin (n + 2), olsValidationSummand G i
        ∂olsPairGaussianLaw (n + 2)) =
        ∑ i : Fin (n + 2), ∫ G : Fin (n + 2) → ℝ × ℝ,
          olsValidationSummand G i ∂olsPairGaussianLaw (n + 2) := by
    rw [integral_finsetSum]
    intro i hi
    exact integrable_olsValidationSummand hn i
  have hterms :
      (∑ i : Fin (n + 2), ∫ G : Fin (n + 2) → ℝ × ℝ,
        olsValidationSummand G i ∂olsPairGaussianLaw (n + 2)) =
        (n + 2 : ℝ) *
          (∫ G : Fin (n + 1) → ℝ × ℝ,
            olsTestRisk G ∂olsPairGaussianLaw (n + 1)) := by
    calc
      _ = ∑ _i : Fin (n + 2),
          ∫ G : Fin (n + 1) → ℝ × ℝ,
            olsTestRisk G ∂olsPairGaussianLaw (n + 1) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact integral_olsValidationSummand_eq_risk_mean hn i
      _ = _ := by simp
  have hm : (n + 2 : ℝ) ≠ 0 := by positivity
  have hdef : ∀ G : Fin (n + 2) → ℝ × ℝ,
      olsValidationError G = (1 / (n + 2 : ℝ)) *
        ∑ i : Fin (n + 2), olsValidationSummand G i := by
    intro G
    simp only [olsValidationError, olsValidationSummand, div_eq_mul_inv]
    ring_nf
  calc
    _ = ∫ G : Fin (n + 2) → ℝ × ℝ,
        (1 / (n + 2 : ℝ)) *
          ∑ i : Fin (n + 2), olsValidationSummand G i
        ∂olsPairGaussianLaw (n + 2) := by
      apply integral_congr_ae
      exact ae_of_all _ hdef
    _ = (1 / (n + 2 : ℝ)) *
        ∑ i : Fin (n + 2), ∫ G : Fin (n + 2) → ℝ × ℝ,
          olsValidationSummand G i ∂olsPairGaussianLaw (n + 2) := by
      rw [integral_const_mul, hsum]
    _ = ∫ G : Fin (n + 1) → ℝ × ℝ,
        olsTestRisk G ∂olsPairGaussianLaw (n + 1) := by
      rw [hterms]
      field_simp

theorem abs_integral_olsTestError_gaussian_le_bias {n : ℕ}
    (hn : 3 < n + 1) :
    |∫ G : Fin (n + 2) → ℝ × ℝ,
      olsTestError G ∂olsPairGaussianLaw (n + 2)| ≤
      Real.sqrt (1 / ((n + 2 : ℕ) : ℝ) +
        (1 + 1 / ((n + 2 : ℕ) : ℝ)) / ((n + 2 : ℕ) - 3 : ℝ)) +
      Real.sqrt (1 / ((n + 1 : ℕ) : ℝ) +
        (1 + 1 / ((n + 1 : ℕ) : ℝ)) / ((n + 1 : ℕ) - 3 : ℝ)) := by
  let B : ℝ := ∫ z : ℝ × ℝ, |z.2| ∂olsTestLaw
  let R : ℝ := ∫ G : Fin (n + 2) → ℝ × ℝ,
    olsTestRisk G ∂olsPairGaussianLaw (n + 2)
  let V : ℝ := ∫ G : Fin (n + 2) → ℝ × ℝ,
    olsValidationError G ∂olsPairGaussianLaw (n + 2)
  have hR := abs_integral_olsTestRisk_sub_noise_baseline_le
    (r := n + 2) (by omega : 3 < n + 2)
  have hV := abs_integral_olsTestRisk_sub_noise_baseline_le
    (r := n + 1) hn
  have hR' : |R - B| ≤
      Real.sqrt (1 / ((n + 2 : ℕ) : ℝ) +
        (1 + 1 / ((n + 2 : ℕ) : ℝ)) / ((n + 2 : ℕ) - 3 : ℝ)) := by
    simpa [R, B] using hR
  have hV' : |V - B| ≤
      Real.sqrt (1 / ((n + 1 : ℕ) : ℝ) +
        (1 + 1 / ((n + 1 : ℕ) : ℝ)) / ((n + 1 : ℕ) - 3 : ℝ)) := by
    rw [← integral_olsValidationError_eq_deletedRisk_mean hn] at hV
    simpa [V, B] using hV
  have hRiskInt : Integrable (olsTestRisk :
      (Fin (n + 2) → ℝ × ℝ) → ℝ) (olsPairGaussianLaw (n + 2)) :=
    integrable_olsTestRisk_gaussian (by omega : 3 < n + 2)
  have hValInt : Integrable (olsValidationError :
      (Fin (n + 2) → ℝ × ℝ) → ℝ) (olsPairGaussianLaw (n + 2)) :=
    integrable_olsValidationError_gaussian hn
  have hErrorMean :
      (∫ G : Fin (n + 2) → ℝ × ℝ,
        olsTestError G ∂olsPairGaussianLaw (n + 2)) = R - V := by
    calc
      _ = ∫ G : Fin (n + 2) → ℝ × ℝ,
          olsTestRisk G - olsValidationError G ∂olsPairGaussianLaw (n + 2) := by rfl
      _ = R - V := by
        rw [integral_sub hRiskInt hValInt]
  have htriangle : |R - V| ≤ |R - B| + |V - B| := by
    calc
      |R - V| = |(R - B) + (B - V)| := by congr 1; ring
      _ ≤ |R - B| + |B - V| := abs_add_le _ _
      _ = |R - B| + |V - B| :=
        congrArg (fun x : ℝ => |R - B| + x) (abs_sub_comm B V)
  rw [hErrorMean]
  exact htriangle.trans (add_le_add hR' hV')

theorem integrable_olsTestError_sq_gaussian {n : ℕ} (hn : 4 ≤ n) :
    Integrable (fun G : Fin (n + 2) → ℝ × ℝ => (olsTestError G) ^ 2)
      (olsPairGaussianLaw (n + 2)) := by
  have hRiskSq := integrable_olsTestRisk_sq_gaussian (by omega : 3 < n + 2)
  have hValSq := integrable_olsValidationError_sq_gaussian (by omega : 3 < n + 1)
  have hsum := hRiskSq.add hValSq
  have hmajor : Integrable
      (fun G : Fin (n + 2) → ℝ × ℝ =>
        2 * ((olsTestRisk G) ^ 2 + (olsValidationError G) ^ 2))
      (olsPairGaussianLaw (n + 2)) := by
    simpa [mul_add, add_comm, add_left_comm, add_assoc] using hsum.const_mul 2
  apply hmajor.mono_nonneg (measurable_olsTestError.pow_const 2).aestronglyMeasurable
  · exact ae_of_all _ fun G => sq_nonneg _
  · filter_upwards with G
    unfold olsTestError
    nlinarith [sq_nonneg (olsTestRisk G + olsValidationError G)]

theorem integral_olsTestError_sq_gaussian_le_twelve {n : ℕ} (hn : 4 ≤ n) :
    (∫ G : Fin (n + 2) → ℝ × ℝ, (olsTestError G) ^ 2
      ∂olsPairGaussianLaw (n + 2)) ≤ 12 := by
  let N : ℕ := n + 2
  have hRiskSq := integrable_olsTestRisk_sq_gaussian (by dsimp [N]; omega : 3 < N)
  have hValSq := integrable_olsValidationError_sq_gaussian (by omega : 3 < n + 1)
  have hErrSq := integrable_olsTestError_sq_gaussian hn
  have hmajor : Integrable
      (fun G : Fin (n + 2) → ℝ × ℝ =>
        2 * ((olsTestRisk G) ^ 2 + (olsValidationError G) ^ 2))
      (olsPairGaussianLaw (n + 2)) := by
    simpa [mul_add, add_comm, add_left_comm, add_assoc] using hRiskSq.add hValSq |>.const_mul 2
  have hle := integral_mono_ae hErrSq hmajor (ae_of_all _ fun G => by
    unfold olsTestError
    nlinarith [sq_nonneg (olsTestRisk G + olsValidationError G)])
  have hR := integral_olsTestRisk_sq_gaussian_le (by dsimp [N]; omega : 3 < N)
  have hV := integral_olsValidationError_sq_gaussian_le (by omega : 3 < n + 1)
  have hRN :
      1 / ((n + 2 : ℕ) : ℝ) +
        (1 + 1 / ((n + 2 : ℕ) : ℝ)) / ((n + 2 : ℕ) - 3 : ℝ) ≤ 2 :=
    olsFitVariance_le_two (by omega)
  have hRprev :
      1 / ((n + 1 : ℕ) : ℝ) +
        (1 + 1 / ((n + 1 : ℕ) : ℝ)) / ((n + 1 : ℕ) - 3 : ℝ) ≤ 2 :=
    olsFitVariance_le_two (by omega)
  have hmajorIntegral :
      (∫ G : Fin (n + 2) → ℝ × ℝ,
        2 * ((olsTestRisk G) ^ 2 + (olsValidationError G) ^ 2)
        ∂olsPairGaussianLaw (n + 2)) ≤ 12 := by
    rw [integral_const_mul, integral_add hRiskSq hValSq]
    have hRiskLeThree :
        (∫ G : Fin (n + 2) → ℝ × ℝ, (olsTestRisk G) ^ 2
          ∂olsPairGaussianLaw (n + 2)) ≤ 3 := by
      have hR' :
          (∫ G : Fin (n + 2) → ℝ × ℝ, (olsTestRisk G) ^ 2
            ∂olsPairGaussianLaw (n + 2)) ≤
            1 + (1 / ((n + 2 : ℕ) : ℝ) +
              (1 + 1 / ((n + 2 : ℕ) : ℝ)) / ((n + 2 : ℕ) - 3 : ℝ)) := by
        simpa [N] using hR
      linarith [hR', hRN]
    have hValLeThree :
        (∫ G : Fin (n + 2) → ℝ × ℝ, (olsValidationError G) ^ 2
          ∂olsPairGaussianLaw (n + 2)) ≤ 3 := by
      linarith [hV, hRprev]
    nlinarith [hRiskLeThree, hValLeThree]
  exact hle.trans hmajorIntegral

theorem olsTestError_eLpNorm_two_le_sqrt_twelve {n : ℕ} (hn : 4 ≤ n) :
    eLpNorm (olsTestError : (Fin (n + 2) → ℝ × ℝ) → ℝ) 2
      (olsPairGaussianLaw (n + 2)) ≤ ENNReal.ofReal (Real.sqrt 12) := by
  have hsq := integrable_olsTestError_sq_gaussian hn
  have hmem : MemLp (olsTestError : (Fin (n + 2) → ℝ × ℝ) → ℝ) 2
      (olsPairGaussianLaw (n + 2)) :=
    (memLp_two_iff_integrable_sq
      measurable_olsTestError.aestronglyMeasurable).2 hsq
  rw [hmem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  have hnorm : (∫ G : Fin (n + 2) → ℝ × ℝ,
      ‖olsTestError G‖ ^ 2 ∂olsPairGaussianLaw (n + 2)) =
      ∫ G : Fin (n + 2) → ℝ × ℝ,
        (olsTestError G) ^ 2 ∂olsPairGaussianLaw (n + 2) := by
    apply integral_congr_ae
    exact ae_of_all _ fun G => by
      simp only [Real.norm_eq_abs, sq_abs]
  have hnormR : (∫ G : Fin (n + 2) → ℝ × ℝ,
      ‖olsTestError G‖ ^ (2 : ℝ) ∂olsPairGaussianLaw (n + 2)) =
      ∫ G : Fin (n + 2) → ℝ × ℝ,
        (olsTestError G) ^ 2 ∂olsPairGaussianLaw (n + 2) := by
    calc
      _ = ∫ G : Fin (n + 2) → ℝ × ℝ,
          ‖olsTestError G‖ ^ 2 ∂olsPairGaussianLaw (n + 2) := by
        apply integral_congr_ae
        exact ae_of_all _ fun G => Real.rpow_natCast _ _
      _ = _ := hnorm
  simp only [ENNReal.toReal_ofNat]
  rw [hnormR]
  have hbound := integral_olsTestError_sq_gaussian_le_twelve hn
  have hboundRoot : Real.sqrt
      (∫ G : Fin (n + 2) → ℝ × ℝ, (olsTestError G) ^ 2
        ∂olsPairGaussianLaw (n + 2)) ≤ Real.sqrt 12 :=
    Real.sqrt_le_sqrt (show
      (∫ G : Fin (n + 2) → ℝ × ℝ, (olsTestError G) ^ 2
        ∂olsPairGaussianLaw (n + 2)) ≤ 12 from hbound)
  simpa [Real.sqrt_eq_rpow] using hboundRoot

#print axioms integral_olsValidationError_eq_deletedRisk_mean
#print axioms abs_integral_olsTestError_gaussian_le_bias
#print axioms integral_olsTestRisk_sq_gaussian_le
#print axioms integral_olsValidationError_sq_gaussian_le
#print axioms integral_olsTestError_sq_gaussian_le_twelve
#print axioms olsTestError_eLpNorm_two_le_sqrt_twelve

end LOOConcentration
