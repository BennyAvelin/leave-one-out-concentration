import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic
import LOOConcentration.Examples.OlsQuotient

set_option autoImplicit false

namespace LOOConcentration

open MeasureTheory
open scoped ENNReal NNReal

/-!
# Risk, validation, and error Lipschitz bounds on the OLS good set

The risk uses an independent standard Gaussian covariate and noise pair.  The
validation error is the finite leave-one-out average on the exact `Fin (n+2)`
sample carrier.
-/

noncomputable abbrev olsTestGaussian : Measure ℝ :=
  ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0)

noncomputable abbrev olsTestLaw : Measure (ℝ × ℝ) :=
  olsTestGaussian.prod olsTestGaussian

/-- The noise-coordinate loss at an independent test pair. -/
noncomputable def olsRiskLoss {N : ℕ} (G : Fin N → ℝ × ℝ) (z : ℝ × ℝ) : ℝ :=
  |z.2 - olsNoisePredictor G z.1|

/-- Actual Gaussian test risk of the noise-coordinate predictor. -/
noncomputable def olsTestRisk {N : ℕ} (G : Fin N → ℝ × ℝ) : ℝ :=
  ∫ z, olsRiskLoss G z ∂olsTestLaw

/-- The validation error computed from the leave-one-out fits. -/
noncomputable def olsValidationError {n : ℕ} (G : Fin (n + 2) → ℝ × ℝ) : ℝ :=
  (∑ i : Fin (n + 2),
      |(G i).2 - olsNoisePredictor (deleteAt G i) (G i).1|) / (n + 2 : ℝ)

/-- The generalization error as actual test risk minus validation error. -/
noncomputable def olsTestError {n : ℕ} (G : Fin (n + 2) → ℝ × ℝ) : ℝ :=
  olsTestRisk G - olsValidationError G

private lemma olsTestGaussian_id_memLp (p : ℝ≥0) :
    MemLp (id : ℝ → ℝ) p olsTestGaussian := by
  exact ProbabilityTheory.memLp_id_gaussianReal p

private lemma olsTestGaussian_id_integrable :
    Integrable (id : ℝ → ℝ) olsTestGaussian := by
  exact (olsTestGaussian_id_memLp 1).integrable (by norm_num)

private lemma olsTestGaussian_abs_integrable :
    Integrable (fun x : ℝ => |x|) olsTestGaussian := by
  simpa only [Real.norm_eq_abs, id_eq] using olsTestGaussian_id_integrable.abs

private lemma olsTestGaussian_sq_integral :
    ∫ x, x ^ 2 ∂olsTestGaussian = 1 := by
  have hv := ProbabilityTheory.variance_id_gaussianReal
    (μ := 0) (v := (1 : ℝ≥0))
  change ProbabilityTheory.variance (fun x : ℝ => x) olsTestGaussian = 1 at hv
  rw [ProbabilityTheory.variance_eq_integral
    (X := fun x : ℝ => x) (μ := olsTestGaussian) measurable_id'.aemeasurable] at hv
  simpa [ProbabilityTheory.integral_id_gaussianReal] using hv

/-- A standard Gaussian has absolute first moment at most one. -/
theorem olsTestGaussian_abs_integral_le_one :
    ∫ x, |x| ∂olsTestGaussian ≤ 1 := by
  have hmem₂ : MemLp (id : ℝ → ℝ) (ENNReal.ofReal 2) olsTestGaussian := by
    exact ProbabilityTheory.memLp_id_gaussianReal' _ (by norm_num)
  have hmemAbs₂ : MemLp (fun x : ℝ => |x|) (ENNReal.ofReal 2) olsTestGaussian := by
    simpa only [Real.norm_eq_abs, id_eq] using hmem₂.norm
  have hmemOne₂ : MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal 2) olsTestGaussian :=
    memLp_const 1
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := olsTestGaussian) (p := 2) (q := 2) Real.HolderConjugate.two_two
    (ae_of_all _ fun _ => abs_nonneg _)
    (ae_of_all _ fun _ => (show 0 ≤ (1 : ℝ) by norm_num))
    hmemAbs₂ hmemOne₂
  have hAbsSq : ∫ x, |x| ^ 2 ∂olsTestGaussian = 1 := by
    calc
      _ = ∫ x, x ^ 2 ∂olsTestGaussian := by
        apply integral_congr_ae
        filter_upwards with x
        rw [sq_abs]
      _ = 1 := olsTestGaussian_sq_integral
  have hOneSq : ∫ _x : ℝ, (1 : ℝ) ^ 2 ∂olsTestGaussian = 1 := by
    simp
  have hHolder' : (∫ x, |x| * (1 : ℝ) ∂olsTestGaussian) ≤ 1 := by
    calc
      _ ≤ (∫ x, |x| ^ 2 ∂olsTestGaussian) ^ (1 / 2) *
          (∫ x, (1 : ℝ) ^ 2 ∂olsTestGaussian) ^ (1 / 2) := hHolder
      _ = 1 := by norm_num [hAbsSq, hOneSq, olsTestGaussian_sq_integral]
  calc
    ∫ x, |x| ∂olsTestGaussian = ∫ x, |x| * (1 : ℝ) ∂olsTestGaussian := by
      congr 1
      funext x
      ring
    _ ≤ 1 := hHolder'

private lemma olsTestLaw_fst_abs_integrable :
    Integrable (fun z : ℝ × ℝ => |z.1|) olsTestLaw := by
  exact olsTestGaussian_abs_integrable.comp_fst olsTestGaussian

private lemma olsTestLaw_snd_abs_integrable :
    Integrable (fun z : ℝ × ℝ => |z.2|) olsTestLaw := by
  exact olsTestGaussian_abs_integrable.comp_snd olsTestGaussian

theorem olsTestLaw_one_add_fst_abs_integral_le_two :
    ∫ z, (1 + |z.1|) ∂olsTestLaw ≤ 2 := by
  have hf : Integrable (fun z : ℝ × ℝ => 1 + |z.1|) olsTestLaw :=
    (integrable_const 1).add olsTestLaw_fst_abs_integrable
  rw [integral_prod _ hf]
  have hinner : ∀ x : ℝ, ∫ y, (1 + |x|) ∂olsTestGaussian = 1 + |x| := by
    intro x
    simp
  simp_rw [hinner]
  rw [integral_add (integrable_const 1) olsTestGaussian_abs_integrable]
  have hconst : ∫ _x : ℝ, (1 : ℝ) ∂olsTestGaussian = 1 := by simp
  rw [hconst]
  linarith [olsTestGaussian_abs_integral_le_one]

private theorem measurable_olsNoisePredictor {N : ℕ} :
    Measurable (fun p : (Fin N → ℝ × ℝ) × ℝ => olsNoisePredictor p.1 p.2) := by
  have hE : Measurable (fun p : (Fin N → ℝ × ℝ) × ℝ => olsEBar p.1) :=
    measurable_olsEBar.comp measurable_fst
  have hq : Measurable (fun p : (Fin N → ℝ × ℝ) × ℝ => olsNoiseSlope p.1) :=
    measurable_olsNoiseSlope.comp measurable_fst
  have hx : Measurable (fun p : (Fin N → ℝ × ℝ) × ℝ => olsXBar p.1) :=
    measurable_olsXBar.comp measurable_fst
  unfold olsNoisePredictor
  exact hE.add (hq.mul (measurable_snd.sub hx))

private theorem measurable_olsRiskLoss {N : ℕ} :
    Measurable (fun p : (Fin N → ℝ × ℝ) × (ℝ × ℝ) => olsRiskLoss p.1 p.2) := by
  have hp : Measurable (fun p : (Fin N → ℝ × ℝ) × (ℝ × ℝ) =>
      olsNoisePredictor p.1 p.2.1) := by
    exact measurable_olsNoisePredictor.comp (measurable_fst.prodMk measurable_snd.fst)
  unfold olsRiskLoss
  exact measurable_abs.comp (measurable_snd.snd.sub hp)

theorem measurable_olsTestRisk {N : ℕ} :
    Measurable (olsTestRisk : (Fin N → ℝ × ℝ) → ℝ) := by
  have hjoint : StronglyMeasurable
      (fun p : (Fin N → ℝ × ℝ) × (ℝ × ℝ) => olsRiskLoss p.1 p.2) :=
    measurable_olsRiskLoss.stronglyMeasurable
  have hsm : StronglyMeasurable
      (fun G : Fin N → ℝ × ℝ => ∫ z, olsRiskLoss G z ∂olsTestLaw) :=
    hjoint.integral_prod_right'
  exact hsm.measurable

private theorem measurable_olsValidationSummand {n : ℕ} (i : Fin (n + 2)) :
    Measurable (fun G : Fin (n + 2) → ℝ × ℝ =>
      |(G i).2 - olsNoisePredictor (deleteAt G i) (G i).1|) := by
  have hdel : Measurable (fun G : Fin (n + 2) → ℝ × ℝ => deleteAt G i) := by
    apply measurable_pi_iff.mpr
    intro j
    exact (continuous_apply (i.succAbove j)).measurable
  have hz : Measurable (fun G : Fin (n + 2) → ℝ × ℝ => (G i).1) :=
    measurable_fst.comp (continuous_apply i).measurable
  have he : Measurable (fun G : Fin (n + 2) → ℝ × ℝ => (G i).2) :=
    measurable_snd.comp (continuous_apply i).measurable
  have hp : Measurable (fun G : Fin (n + 2) → ℝ × ℝ =>
      olsNoisePredictor (deleteAt G i) (G i).1) :=
    measurable_olsNoisePredictor.comp (hdel.prodMk hz)
  exact measurable_abs.comp (he.sub hp)

private theorem measurable_olsValidationError' {n : ℕ} :
    Measurable (olsValidationError : (Fin (n + 2) → ℝ × ℝ) → ℝ) := by
  unfold olsValidationError
  have hsum : Measurable (fun G : Fin (n + 2) → ℝ × ℝ =>
      ∑ i : Fin (n + 2),
        |(G i).2 - olsNoisePredictor (deleteAt G i) (G i).1|) := by
    apply Finset.measurable_sum Finset.univ
    intro i hi
    exact measurable_olsValidationSummand i
  exact hsum.div_const (n + 2 : ℝ)

theorem measurable_olsValidationError {n : ℕ} :
    Measurable (olsValidationError : (Fin (n + 2) → ℝ × ℝ) → ℝ) :=
  measurable_olsValidationError'

theorem measurable_olsTestError {n : ℕ} :
    Measurable (olsTestError : (Fin (n + 2) → ℝ × ℝ) → ℝ) := by
  unfold olsTestError
  exact measurable_olsTestRisk.sub measurable_olsValidationError

theorem olsTestRiskLoss_integrable {N : ℕ} (G : Fin N → ℝ × ℝ) :
    Integrable (olsRiskLoss G) olsTestLaw := by
  have hmeas : AEStronglyMeasurable (olsRiskLoss G) olsTestLaw := by
    have hp : Measurable (fun z : ℝ × ℝ => olsNoisePredictor G z.1) := by
      exact measurable_olsNoisePredictor.comp (measurable_const.prodMk measurable_fst)
    change AEStronglyMeasurable (fun z : ℝ × ℝ => |z.2 - olsNoisePredictor G z.1|) _
    exact (measurable_abs.comp (measurable_snd.sub hp)).aestronglyMeasurable
  let C : ℝ := |olsEBar G| + |olsNoiseSlope G| * |olsXBar G|
  let K : ℝ := |olsNoiseSlope G|
  have hmajor : Integrable (fun z : ℝ × ℝ => |z.2| + C + K * |z.1|) olsTestLaw := by
    have hconst : Integrable (fun _ : ℝ × ℝ => C) olsTestLaw := integrable_const C
    have hlinear := olsTestLaw_fst_abs_integrable.const_mul K
    exact (olsTestLaw_snd_abs_integrable.add hconst).add hlinear
  apply hmajor.mono' hmeas
  filter_upwards with z
  change ‖olsRiskLoss G z‖ ≤ |z.2| + C + K * |z.1|
  simp only [Real.norm_eq_abs, olsRiskLoss, abs_abs]
  have hp : |olsNoisePredictor G z.1| ≤
      |olsEBar G| + |olsNoiseSlope G| * (|z.1| + |olsXBar G|) := by
    unfold olsNoisePredictor
    calc
      _ ≤ |olsEBar G| + |olsNoiseSlope G * (z.1 - olsXBar G)| := abs_add_le _ _
      _ = |olsEBar G| + |olsNoiseSlope G| * |z.1 - olsXBar G| := by rw [abs_mul]
      _ ≤ |olsEBar G| + |olsNoiseSlope G| * (|z.1| + |olsXBar G|) := by
        have hsub : |z.1 - olsXBar G| ≤ |z.1| + |olsXBar G| := by
          simpa only [sub_eq_add_neg, abs_neg] using abs_add_le z.1 (-olsXBar G)
        gcongr
  calc
    _ ≤ |z.2| + |olsNoisePredictor G z.1| := by
      have h := abs_add_le z.2 (-olsNoisePredictor G z.1)
      simpa only [sub_eq_add_neg, abs_neg] using h
    _ ≤ |z.2| + (|olsEBar G| + |olsNoiseSlope G| *
          (|z.1| + |olsXBar G|)) := by gcongr
    _ = |z.2| + C + K * |z.1| := by
      simp only [C, K]
      ring

theorem olsTestRisk_pairwise_bound {n : ℕ}
    (hn : 192 ≤ n + 2) (G G' : Fin (n + 2) → ℝ × ℝ)
    (hG : G ∈ olsGoodSet n) (hG' : G' ∈ olsGoodSet n) :
    |olsTestRisk G - olsTestRisk G'| ≤
      12000 * olsPairDistance G G' / Real.sqrt (n + 2 : ℝ) := by
  let Δ := olsPairDistance G G'
  let c := 6000 * Δ / Real.sqrt (n + 2 : ℝ)
  have hΔ : 0 ≤ Δ := Real.sqrt_nonneg _
  have hc : 0 ≤ c := by dsimp [c, Δ]; positivity
  have hGint := olsTestRiskLoss_integrable G
  have hG'int := olsTestRiskLoss_integrable G'
  have hdiff := hGint.sub hG'int
  have hmajor : Integrable (fun z : ℝ × ℝ => c * (1 + |z.1|)) olsTestLaw := by
    have hbase := (integrable_const (1 : ℝ)).add olsTestLaw_fst_abs_integrable
    exact hbase.const_mul c
  have hpoint : ∀ z : ℝ × ℝ,
      |olsRiskLoss G z - olsRiskLoss G' z| ≤ c * (1 + |z.1|) := by
    intro z
    have hpred := ols_goodSet_noisePredictor_pairwise hn G G' hG hG' z.1
    have htri₁ := abs_sub_abs_le_abs_sub (z.2 - olsNoisePredictor G z.1)
      (z.2 - olsNoisePredictor G' z.1)
    have htri₂ := abs_sub_abs_le_abs_sub (z.2 - olsNoisePredictor G' z.1)
      (z.2 - olsNoisePredictor G z.1)
    have htri :
        |(|z.2 - olsNoisePredictor G z.1| -
            |z.2 - olsNoisePredictor G' z.1|)| ≤
          |(z.2 - olsNoisePredictor G z.1) -
            (z.2 - olsNoisePredictor G' z.1)| := by
      rw [abs_le]
      constructor
      · have htri₂' :
            |z.2 - olsNoisePredictor G' z.1| -
                |z.2 - olsNoisePredictor G z.1| ≤
              |(z.2 - olsNoisePredictor G z.1) -
                (z.2 - olsNoisePredictor G' z.1)| := by
            simpa only [abs_sub_comm] using htri₂
        linarith
      · exact htri₁
    unfold olsRiskLoss
    calc
      _ ≤ |(z.2 - olsNoisePredictor G z.1) -
          (z.2 - olsNoisePredictor G' z.1)| := htri
      _ = |olsNoisePredictor G' z.1 - olsNoisePredictor G z.1| := by
        congr 1
        ring
      _ = |olsNoisePredictor G z.1 - olsNoisePredictor G' z.1| := by
        rw [abs_sub_comm]
      _ ≤ 6000 * (1 + |z.1|) * Δ / Real.sqrt (n + 2 : ℝ) := by
        simpa [Δ] using hpred
      _ = c * (1 + |z.1|) := by dsimp [c]; ring
  have hbound : ∫ z, |olsRiskLoss G z - olsRiskLoss G' z| ∂olsTestLaw ≤
      c * ∫ z, (1 + |z.1|) ∂olsTestLaw := by
    calc
      _ ≤ ∫ z, c * (1 + |z.1|) ∂olsTestLaw :=
        integral_mono_ae hdiff.abs hmajor (ae_of_all _ hpoint)
      _ = c * ∫ z, (1 + |z.1|) ∂olsTestLaw := integral_const_mul c _
  have hmoment := olsTestLaw_one_add_fst_abs_integral_le_two
  calc
    |olsTestRisk G - olsTestRisk G'| =
        |∫ z, olsRiskLoss G z - olsRiskLoss G' z ∂olsTestLaw| := by
          change |(∫ z, olsRiskLoss G z ∂olsTestLaw) -
            (∫ z, olsRiskLoss G' z ∂olsTestLaw)| = _
          rw [← integral_sub hGint hG'int]
    _ ≤ ∫ z, |olsRiskLoss G z - olsRiskLoss G' z| ∂olsTestLaw :=
      abs_integral_le_integral_abs
    _ ≤ c * ∫ z, (1 + |z.1|) ∂olsTestLaw := hbound
    _ ≤ c * 2 := mul_le_mul_of_nonneg_left hmoment hc
    _ = 12000 * Δ / Real.sqrt (n + 2 : ℝ) := by dsimp [c, Δ]; ring

private lemma ols_sum_abs_le_sqrt_card_mul_sqrt_sum_sq {r : ℕ} (x : Fin r → ℝ) :
    (∑ i : Fin r, |x i|) ≤
      Real.sqrt (r : ℝ) * Real.sqrt (∑ i : Fin r, x i ^ 2) := by
  have hcsRaw := Finset.sum_mul_sq_le_sq_mul_sq
    (s := Finset.univ) (fun _ : Fin r => (1 : ℝ)) (fun i => |x i|)
  have hcs : (∑ i : Fin r, |x i|) ^ 2 ≤
      (r : ℝ) * ∑ i : Fin r, x i ^ 2 := by
    simpa [Finset.sum_const, nsmul_eq_mul, sq_abs] using hcsRaw
  have hsumNonneg : 0 ≤ ∑ i : Fin r, x i ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg (x i)
  have hsumAbsNonneg : 0 ≤ ∑ i : Fin r, |x i| :=
    Finset.sum_nonneg fun i _ => abs_nonneg (x i)
  have hrNonneg : 0 ≤ (r : ℝ) := Nat.cast_nonneg _
  apply (sq_le_sq₀ hsumAbsNonneg
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).1
  rw [mul_pow, Real.sq_sqrt hrNonneg, Real.sq_sqrt hsumNonneg]
  exact hcs

private lemma olsPairDistance_sq {r : ℕ} (G G' : Fin r → ℝ × ℝ) :
    olsPairDistance G G' ^ 2 =
      olsNoiseNormSq (fun i => G i - G' i) := by
  unfold olsPairDistance olsNoiseNorm
  exact Real.sq_sqrt (by
    unfold olsNoiseNormSq
    exact Finset.sum_nonneg fun i _ => add_nonneg (sq_nonneg _) (sq_nonneg _))

private lemma ols_sum_abs_fst_diff_le_pairDistance {r : ℕ}
    (G G' : Fin r → ℝ × ℝ) :
    (∑ i : Fin r, |(G i).1 - (G' i).1|) ≤
      Real.sqrt (r : ℝ) * olsPairDistance G G' := by
  have hsq : (∑ i : Fin r, ((G i).1 - (G' i).1) ^ 2) ≤
      olsPairDistance G G' ^ 2 := by
    rw [olsPairDistance_sq]
    unfold olsNoiseNormSq
    apply Finset.sum_le_sum
    intro i hi
    simp only [Prod.fst_sub]
    exact le_add_of_nonneg_right (sq_nonneg ((G i).2 - (G' i).2))
  have hΔ : 0 ≤ olsPairDistance G G' := Real.sqrt_nonneg _
  have hroot := Real.sqrt_le_sqrt hsq
  have hroot' : Real.sqrt (∑ i : Fin r, ((G i).1 - (G' i).1) ^ 2) ≤
      olsPairDistance G G' := by
    simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg hΔ] using hroot
  calc
      _ ≤ Real.sqrt (r : ℝ) *
        Real.sqrt (∑ i : Fin r, ((G i).1 - (G' i).1) ^ 2) :=
      ols_sum_abs_le_sqrt_card_mul_sqrt_sum_sq
        (fun i : Fin r => (G i).1 - (G' i).1)
    _ ≤ Real.sqrt (r : ℝ) * olsPairDistance G G' :=
      mul_le_mul_of_nonneg_left hroot' (Real.sqrt_nonneg _)

private lemma ols_sum_abs_snd_diff_le_pairDistance {r : ℕ}
    (G G' : Fin r → ℝ × ℝ) :
    (∑ i : Fin r, |(G i).2 - (G' i).2|) ≤
      Real.sqrt (r : ℝ) * olsPairDistance G G' := by
  have hsq : (∑ i : Fin r, ((G i).2 - (G' i).2) ^ 2) ≤
      olsPairDistance G G' ^ 2 := by
    rw [olsPairDistance_sq]
    unfold olsNoiseNormSq
    apply Finset.sum_le_sum
    intro i hi
    simp only [Prod.snd_sub]
    exact le_add_of_nonneg_left (sq_nonneg ((G i).1 - (G' i).1))
  have hΔ : 0 ≤ olsPairDistance G G' := Real.sqrt_nonneg _
  have hroot := Real.sqrt_le_sqrt hsq
  have hroot' : Real.sqrt (∑ i : Fin r, ((G i).2 - (G' i).2) ^ 2) ≤
      olsPairDistance G G' := by
    simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg hΔ] using hroot
  calc
    _ ≤ Real.sqrt (r : ℝ) *
        Real.sqrt (∑ i : Fin r, ((G i).2 - (G' i).2) ^ 2) :=
      ols_sum_abs_le_sqrt_card_mul_sqrt_sum_sq _
    _ ≤ Real.sqrt (r : ℝ) * olsPairDistance G G' :=
      mul_le_mul_of_nonneg_left hroot' (Real.sqrt_nonneg _)

private lemma ols_sum_abs_covariate_le_threeN {n : ℕ}
    (G : Fin (n + 2) → ℝ × ℝ) (hG : G ∈ olsGoodSet n) :
    (∑ i : Fin (n + 2), |(G i).1|) ≤ 3 * (n + 2 : ℝ) := by
  have hXsq : (∑ i : Fin (n + 2), (G i).1 ^ 2) ≤ olsNoiseNormSq G := by
    unfold olsNoiseNormSq
    apply Finset.sum_le_sum
    intro i hi
    exact le_add_of_nonneg_right (sq_nonneg ((G i).2))
  have hnormNonneg : 0 ≤ olsNoiseNormSq G := by
    unfold olsNoiseNormSq
    exact Finset.sum_nonneg fun i _ => add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hnormsq : olsNoiseNormSq G ≤ 9 * (n + 2 : ℝ) := by
    have h := (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity :
      0 ≤ 3 * Real.sqrt (n + 2 : ℝ))).2 hG.1
    rw [Real.sq_sqrt hnormNonneg, mul_pow,
      Real.sq_sqrt (by positivity : 0 ≤ (n + 2 : ℝ))] at h
    nlinarith only [h]
  have hroot : Real.sqrt (∑ i : Fin (n + 2), (G i).1 ^ 2) ≤
      3 * Real.sqrt (n + 2 : ℝ) := by
    calc
      _ ≤ Real.sqrt (olsNoiseNormSq G) := Real.sqrt_le_sqrt hXsq
      _ = olsNoiseNorm G := rfl
      _ ≤ 3 * Real.sqrt (n + 2 : ℝ) := hG.1
  calc
    _ ≤ Real.sqrt (n + 2 : ℝ) *
        Real.sqrt (∑ i : Fin (n + 2), (G i).1 ^ 2) :=
      by
        simpa only [Nat.cast_add, Nat.cast_ofNat] using
          ols_sum_abs_le_sqrt_card_mul_sqrt_sum_sq
            (fun i : Fin (n + 2) => (G i).1)
    _ ≤ Real.sqrt (n + 2 : ℝ) * (3 * Real.sqrt (n + 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg _)
    _ = 3 * (n + 2 : ℝ) := by
      calc
        _ = 3 * (Real.sqrt (n + 2 : ℝ)) ^ 2 := by ring
        _ = 3 * (n + 2 : ℝ) := by
          rw [Real.sq_sqrt (by positivity : 0 ≤ (n + 2 : ℝ))]

private lemma ols_deletedNoiseSlope_abs_le {n : ℕ}
    (hn : 192 ≤ n + 2) (G : Fin (n + 2) → ℝ × ℝ)
    (hG : G ∈ olsGoodSet n) (i : Fin (n + 2)) :
    |olsNoiseSlope (deleteAt G i)| ≤ 6 := by
  have hnorm : olsNoiseNorm (deleteAt G i) ≤ 3 * Real.sqrt (n + 2 : ℝ) :=
    (ols_deletedNoiseNorm_le G i).trans hG.1
  have hdesign := ols_deletedCenteredDesign_lower_bound hn G hG i
  have hnormCast : olsNoiseNorm (deleteAt G i) ≤
      3 * Real.sqrt ((n + 2 : ℕ) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hnorm
  have hdesignCast : ((n + 2 : ℕ) : ℝ) / 4 ≤
      olsCenteredDesign (deleteAt G i) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hdesign
  exact ols_noiseSlope_abs_le (N := n + 2) (r := n + 1) (by omega) (by omega)
    (deleteAt G i) hnormCast hdesignCast

private lemma ols_validation_summand_pairwise {n : ℕ}
    (hn : 192 ≤ n + 2) (G G' : Fin (n + 2) → ℝ × ℝ)
    (hG : G ∈ olsGoodSet n) (hG' : G' ∈ olsGoodSet n) (i : Fin (n + 2)) :
    |(|(G i).2 - olsNoisePredictor (deleteAt G i) (G i).1| -
        |(G' i).2 - olsNoisePredictor (deleteAt G' i) (G' i).1|)| ≤
      |(G i).2 - (G' i).2| + 6 * |(G i).1 - (G' i).1| +
        6000 * (1 + |(G i).1|) * olsPairDistance G G' /
          Real.sqrt (n + 2 : ℝ) := by
  let Δ := olsPairDistance G G'
  have hpred := ols_deletedGoodSet_noisePredictor_pairwise hn G G' hG hG' i (G i).1
  have hq := ols_deletedNoiseSlope_abs_le hn G' hG' i
  have hholdExact :
      olsNoisePredictor (deleteAt G' i) (G i).1 -
          olsNoisePredictor (deleteAt G' i) (G' i).1 =
        olsNoiseSlope (deleteAt G' i) * ((G i).1 - (G' i).1) := by
    unfold olsNoisePredictor
    ring
  have hhold :
      |olsNoisePredictor (deleteAt G' i) (G i).1 -
          olsNoisePredictor (deleteAt G' i) (G' i).1| ≤
        6 * |(G i).1 - (G' i).1| := by
    rw [hholdExact, abs_mul]
    exact mul_le_mul_of_nonneg_right hq (abs_nonneg _)
  have hfit :
      |olsNoisePredictor (deleteAt G i) (G i).1 -
          olsNoisePredictor (deleteAt G' i) (G' i).1| ≤
        6000 * (1 + |(G i).1|) * Δ / Real.sqrt (n + 2 : ℝ) +
          6 * |(G i).1 - (G' i).1| := by
    calc
      _ ≤ |olsNoisePredictor (deleteAt G i) (G i).1 -
            olsNoisePredictor (deleteAt G' i) (G i).1| +
          |olsNoisePredictor (deleteAt G' i) (G i).1 -
            olsNoisePredictor (deleteAt G' i) (G' i).1| := abs_sub_le _ _ _
      _ ≤ 6000 * (1 + |(G i).1|) * Δ / Real.sqrt (n + 2 : ℝ) +
          6 * |(G i).1 - (G' i).1| := add_le_add hpred hhold
  have hloss₁ := abs_sub_abs_le_abs_sub
    ((G i).2 - olsNoisePredictor (deleteAt G i) (G i).1)
    ((G' i).2 - olsNoisePredictor (deleteAt G' i) (G' i).1)
  have hloss₂ := abs_sub_abs_le_abs_sub
    ((G' i).2 - olsNoisePredictor (deleteAt G' i) (G' i).1)
    ((G i).2 - olsNoisePredictor (deleteAt G i) (G i).1)
  have hloss :
      |(|(G i).2 - olsNoisePredictor (deleteAt G i) (G i).1| -
          |(G' i).2 - olsNoisePredictor (deleteAt G' i) (G' i).1|)| ≤
        |((G i).2 - olsNoisePredictor (deleteAt G i) (G i).1) -
          ((G' i).2 - olsNoisePredictor (deleteAt G' i) (G' i).1)| := by
    rw [abs_le]
    constructor
    · have hrev :
          |(G' i).2 - olsNoisePredictor (deleteAt G' i) (G' i).1| -
              |(G i).2 - olsNoisePredictor (deleteAt G i) (G i).1| ≤
            |((G i).2 - olsNoisePredictor (deleteAt G i) (G i).1) -
              ((G' i).2 - olsNoisePredictor (deleteAt G' i) (G' i).1)| := by
          simpa only [abs_sub_comm] using hloss₂
      linarith
    · exact hloss₁
  calc
    _ ≤ |((G i).2 - olsNoisePredictor (deleteAt G i) (G i).1) -
        ((G' i).2 - olsNoisePredictor (deleteAt G' i) (G' i).1)| := hloss
    _ ≤ |(G i).2 - (G' i).2| +
        |olsNoisePredictor (deleteAt G i) (G i).1 -
          olsNoisePredictor (deleteAt G' i) (G' i).1| := by
      rw [show ((G i).2 - olsNoisePredictor (deleteAt G i) (G i).1) -
          ((G' i).2 - olsNoisePredictor (deleteAt G' i) (G' i).1) =
          ((G i).2 - (G' i).2) +
            (olsNoisePredictor (deleteAt G' i) (G' i).1 -
              olsNoisePredictor (deleteAt G i) (G i).1) by ring]
      calc
        _ ≤ |(G i).2 - (G' i).2| +
            |olsNoisePredictor (deleteAt G' i) (G' i).1 -
              olsNoisePredictor (deleteAt G i) (G i).1| := abs_add_le _ _
        _ = |(G i).2 - (G' i).2| +
            |olsNoisePredictor (deleteAt G i) (G i).1 -
              olsNoisePredictor (deleteAt G' i) (G' i).1| := by
          congr 1
          rw [abs_sub_comm]
    _ ≤ |(G i).2 - (G' i).2| +
        (6000 * (1 + |(G i).1|) * Δ / Real.sqrt (n + 2 : ℝ) +
          6 * |(G i).1 - (G' i).1|) := by gcongr
    _ = |(G i).2 - (G' i).2| + 6 * |(G i).1 - (G' i).1| +
        6000 * (1 + |(G i).1|) * olsPairDistance G G' /
          Real.sqrt (n + 2 : ℝ) := by dsimp [Δ]; ring

theorem olsValidationError_pairwise_bound {n : ℕ}
    (hn : 192 ≤ n + 2) (G G' : Fin (n + 2) → ℝ × ℝ)
    (hG : G ∈ olsGoodSet n) (hG' : G' ∈ olsGoodSet n) :
    |olsValidationError G - olsValidationError G'| ≤
      24007 * olsPairDistance G G' / Real.sqrt (n + 2 : ℝ) := by
  let Δ := olsPairDistance G G'
  let r := Real.sqrt (n + 2 : ℝ)
  have hΔ : 0 ≤ Δ := Real.sqrt_nonneg _
  have hr : 0 < r := Real.sqrt_pos.2 (by positivity)
  have hrSq : r ^ 2 = (n + 2 : ℝ) := Real.sq_sqrt (by positivity)
  have hSe := ols_sum_abs_snd_diff_le_pairDistance G G'
  have hSx := ols_sum_abs_fst_diff_le_pairDistance G G'
  have hSe' : (∑ i : Fin (n + 2), |(G i).2 - (G' i).2|) ≤ r * Δ := by
    simpa only [Nat.cast_add, Nat.cast_ofNat, r, Δ] using hSe
  have hSx' : (∑ i : Fin (n + 2), |(G i).1 - (G' i).1|) ≤ r * Δ := by
    simpa only [Nat.cast_add, Nat.cast_ofNat, r, Δ] using hSx
  have hweights :
      (∑ i : Fin (n + 2), (1 + |(G i).1|)) ≤ 4 * (n + 2 : ℝ) := by
    rw [Finset.sum_add_distrib]
    have hcount : (∑ _i : Fin (n + 2), (1 : ℝ)) = (n + 2 : ℝ) := by simp
    calc
      _ = (n + 2 : ℝ) + ∑ i : Fin (n + 2), |(G i).1| := by rw [hcount]
      _ ≤ (n + 2 : ℝ) + 3 * (n + 2 : ℝ) :=
        by linarith [ols_sum_abs_covariate_le_threeN G hG]
      _ = 4 * (n + 2 : ℝ) := by ring
  let c : ℝ := 6000 * Δ / r
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have htrainingSum :
      (∑ i : Fin (n + 2),
        6000 * (1 + |(G i).1|) * Δ / r) ≤ 24000 * Δ * r := by
    have hfactor :
        (∑ i : Fin (n + 2), 6000 * (1 + |(G i).1|) * Δ / r) =
          c * ∑ i : Fin (n + 2), (1 + |(G i).1|) := by
      dsimp [c]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    calc
      _ = c * ∑ i : Fin (n + 2), (1 + |(G i).1|) := hfactor
      _ ≤ c * (4 * (n + 2 : ℝ)) := mul_le_mul_of_nonneg_left hweights hc
      _ = 24000 * Δ * r := by
        dsimp [c]
        field_simp [hr.ne']
        rw [hrSq]
        ring
  have htermSum :
      (∑ i : Fin (n + 2),
        |(|(G i).2 - olsNoisePredictor (deleteAt G i) (G i).1| -
            |(G' i).2 - olsNoisePredictor (deleteAt G' i) (G' i).1|)|) ≤
          (∑ i : Fin (n + 2), |(G i).2 - (G' i).2|) +
            6 * (∑ i : Fin (n + 2), |(G i).1 - (G' i).1|) +
            ∑ i : Fin (n + 2), 6000 * (1 + |(G i).1|) * Δ / r := by
    calc
      _ ≤ ∑ i : Fin (n + 2),
          (|(G i).2 - (G' i).2| + 6 * |(G i).1 - (G' i).1| +
            6000 * (1 + |(G i).1|) * Δ / r) := by
        apply Finset.sum_le_sum
        intro i hi
        simpa [Δ, r] using ols_validation_summand_pairwise hn G G' hG hG' i
      _ = (∑ i : Fin (n + 2), |(G i).2 - (G' i).2|) +
          6 * (∑ i : Fin (n + 2), |(G i).1 - (G' i).1|) +
            ∑ i : Fin (n + 2), 6000 * (1 + |(G i).1|) * Δ / r := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hsumBound :
      (∑ i : Fin (n + 2),
        |(|(G i).2 - olsNoisePredictor (deleteAt G i) (G i).1| -
            |(G' i).2 - olsNoisePredictor (deleteAt G' i) (G' i).1|)|) ≤
          24007 * Δ * r := by
    calc
      _ ≤ (∑ i : Fin (n + 2), |(G i).2 - (G' i).2|) +
          6 * (∑ i : Fin (n + 2), |(G i).1 - (G' i).1|) +
          ∑ i : Fin (n + 2), 6000 * (1 + |(G i).1|) * Δ / r := htermSum
      _ ≤ r * Δ + 6 * (r * Δ) + 24000 * Δ * r := by
        exact add_le_add (add_le_add hSe' (mul_le_mul_of_nonneg_left hSx' (by norm_num)))
          htrainingSum
      _ = 24007 * Δ * r := by ring
  have hsumDiff :
      |((∑ i : Fin (n + 2),
          |(G i).2 - olsNoisePredictor (deleteAt G i) (G i).1|) -
        ∑ i : Fin (n + 2),
          |(G' i).2 - olsNoisePredictor (deleteAt G' i) (G' i).1|)| ≤
        24007 * Δ * r := by
    calc
      _ = |∑ i : Fin (n + 2),
          (|(G i).2 - olsNoisePredictor (deleteAt G i) (G i).1| -
            |(G' i).2 - olsNoisePredictor (deleteAt G' i) (G' i).1|)| := by
        rw [← Finset.sum_sub_distrib]
      _ ≤ ∑ i : Fin (n + 2),
          |(|(G i).2 - olsNoisePredictor (deleteAt G i) (G i).1| -
            |(G' i).2 - olsNoisePredictor (deleteAt G' i) (G' i).1|)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ 24007 * Δ * r := hsumBound
  change |(∑ i : Fin (n + 2),
      |(G i).2 - olsNoisePredictor (deleteAt G i) (G i).1|) /
      (n + 2 : ℝ) -
    (∑ i : Fin (n + 2),
      |(G' i).2 - olsNoisePredictor (deleteAt G' i) (G' i).1|) /
      (n + 2 : ℝ)| ≤ 24007 * Δ / r
  rw [show (∑ i : Fin (n + 2),
      |(G i).2 - olsNoisePredictor (deleteAt G i) (G i).1|) /
      (n + 2 : ℝ) -
    (∑ i : Fin (n + 2),
      |(G' i).2 - olsNoisePredictor (deleteAt G' i) (G' i).1|) /
      (n + 2 : ℝ) =
      ((∑ i : Fin (n + 2),
          |(G i).2 - olsNoisePredictor (deleteAt G i) (G i).1|) -
        ∑ i : Fin (n + 2),
          |(G' i).2 - olsNoisePredictor (deleteAt G' i) (G' i).1|) /
          (n + 2 : ℝ) by ring]
  rw [abs_div, abs_of_pos (by positivity : 0 < (n + 2 : ℝ))]
  apply (div_le_iff₀ (by positivity : 0 < (n + 2 : ℝ))).2
  calc
    _ ≤ 24007 * Δ * r := hsumDiff
    _ = (24007 * Δ / r) * (n + 2 : ℝ) := by
      field_simp [hr.ne']
      rw [hrSq]

theorem olsTestError_pairwise_bound {n : ℕ}
    (hn : 192 ≤ n + 2) (G G' : Fin (n + 2) → ℝ × ℝ)
    (hG : G ∈ olsGoodSet n) (hG' : G' ∈ olsGoodSet n) :
    |olsTestError G - olsTestError G'| ≤
      36007 * olsPairDistance G G' / Real.sqrt (n + 2 : ℝ) := by
  have hRisk := olsTestRisk_pairwise_bound hn G G' hG hG'
  have hValidation := olsValidationError_pairwise_bound hn G G' hG hG'
  have hdecomp : olsTestError G - olsTestError G' =
      (olsTestRisk G - olsTestRisk G') -
        (olsValidationError G - olsValidationError G') := by
    unfold olsTestError
    ring
  calc
    |olsTestError G - olsTestError G'| ≤
        |olsTestRisk G - olsTestRisk G'| +
          |olsValidationError G - olsValidationError G'| := by
      rw [hdecomp]
      have h := abs_add_le (olsTestRisk G - olsTestRisk G')
        (-(olsValidationError G - olsValidationError G'))
      simpa only [abs_neg, sub_eq_add_neg] using h
    _ ≤ 12000 * olsPairDistance G G' / Real.sqrt (n + 2 : ℝ) +
        24007 * olsPairDistance G G' / Real.sqrt (n + 2 : ℝ) :=
      add_le_add hRisk hValidation
    _ = 36007 * olsPairDistance G G' / Real.sqrt (n + 2 : ℝ) := by ring

#print axioms olsTestGaussian_abs_integral_le_one
#print axioms olsTestLaw_one_add_fst_abs_integral_le_two
#print axioms olsTestRiskLoss_integrable
#print axioms measurable_olsTestRisk
#print axioms measurable_olsValidationError
#print axioms olsTestRisk_pairwise_bound
#print axioms olsValidationError_pairwise_bound
#print axioms olsTestError_pairwise_bound
