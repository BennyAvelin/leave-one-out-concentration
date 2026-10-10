import LOOConcentration.Examples.GaussianIntegrationByParts
import LOOConcentration.Examples.GaussianMehler
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Tactic

/-!
# Spatial differentiation of the scalar Gaussian Mehler average

The averaging operator below is restricted to measurable bounded functions
and nonnegative times. Its formula is the real standard-Gaussian kernel used
by the OLS application.
-/

set_option autoImplicit false

namespace LOOConcentration.Examples.GaussianMehlerCalculus

open MeasureTheory
open Filter
open scoped Topology NNReal

noncomputable abbrev γ : Measure ℝ := LOOConcentration.standardGaussianIBPMeasure

private theorem mehlerVariance_nonneg {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ 1 - Real.exp (-2 * t) := by
  have ht' : -2 * t ≤ 0 := by nlinarith
  have he : Real.exp (-2 * t) ≤ 1 := Real.exp_le_one_iff.mpr ht'
  linarith

/-- The literal scalar Mehler average, on its source time domain and only for
measurable bounded inputs. -/
noncomputable def standardGaussianMehlerAverage (f : ℝ → ℝ)
    (_hf_meas : Measurable f) (_hf_bounded : ∃ M : ℝ, ∀ x, ‖f x‖ ≤ M)
    (t : ℝ) (_ht : 0 ≤ t) (x : ℝ) : ℝ :=
  ∫ y, f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y) ∂γ

/-- The local calculus average is definitionally the reviewed source
constructor, so its derivative results can be composed with stationarity. -/
theorem standardGaussianMehlerAverage_eq_source
    (f : ℝ → ℝ) (hf_meas : Measurable f)
    (hf_bounded : ∃ M : ℝ, ∀ x, ‖f x‖ ≤ M)
    (t : ℝ) (ht : 0 ≤ t) (x : ℝ) :
    standardGaussianMehlerAverage f hf_meas hf_bounded t ht x =
      LOOConcentration.standardGaussianMehlerAverage f hf_meas hf_bounded t ht x := by
  simp [standardGaussianMehlerAverage, LOOConcentration.standardGaussianMehlerAverage,
    LOOConcentration.standardGaussianMehlerArgument, LOOConcentration.standardGaussianMehlerDrift,
    LOOConcentration.standardGaussianMehlerNoise, γ, LOOConcentration.standardGaussianMehler,
    LOOConcentration.standardGaussianIBPMeasure]

private theorem integrable_of_measurable_norm_le {g : ℝ → ℝ}
    (hg : Measurable g) {M : ℝ} (hM : ∀ x, ‖g x‖ ≤ M) : Integrable g γ := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (g 0)) (hM 0)
  refine (integrable_const M).mono' hg.aestronglyMeasurable ?_
  filter_upwards [] with x
  simpa [Real.norm_eq_abs, abs_of_nonneg hM0] using hM x

/-- Bounded measurable Mehler sections are integrable at every real point,
including time zero where the noise coefficient vanishes. -/
theorem standardGaussianMehler_integrand_integrable {f : ℝ → ℝ}
    (hf_meas : Measurable f) (hf_bounded : ∃ M : ℝ, ∀ x, ‖f x‖ ≤ M)
    (t : ℝ) (ht : 0 ≤ t) (x : ℝ) :
    Integrable (fun y => f
      (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y)) γ := by
  have _hvariance := mehlerVariance_nonneg ht
  rcases hf_bounded with ⟨M, hM⟩
  apply integrable_of_measurable_norm_le
  · exact hf_meas.comp (measurable_const.add (measurable_const.mul measurable_id))
  · intro y
    exact hM _

/-- Differentiate the bounded scalar Mehler average once in space. The
dominating function is the genuine uniform bound `|exp(-t)| * M₁` for the
parameter derivative; no derivative/integral exchange is assumed. -/
theorem standardGaussianMehlerAverage_hasDerivAt
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hf_meas : Measurable f)
    (hf_bounded : ∃ M₀ : ℝ, ∀ x, ‖f x‖ ≤ M₀)
    (hderiv_bounded : ∃ M₁ : ℝ, ∀ x, ‖deriv f x‖ ≤ M₁)
    (t : ℝ) (ht : 0 ≤ t) (x : ℝ) :
    HasDerivAt (fun z => standardGaussianMehlerAverage f hf_meas hf_bounded t ht z)
      (Real.exp (-t) *
        ∫ y, deriv f
          (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y) ∂γ) x := by
  let a : ℝ := Real.exp (-t)
  let b : ℝ := Real.sqrt (1 - Real.exp (-2 * t))
  have _hvariance := mehlerVariance_nonneg ht
  rcases hderiv_bounded with ⟨M₁, hM₁⟩
  let F : ℝ → ℝ → ℝ := fun z y => f (a * z + b * y)
  let F' : ℝ → ℝ → ℝ := fun z y => a * deriv f (a * z + b * y)
  have hF_meas : ∀ᶠ z in 𝓝 x, AEStronglyMeasurable (F z) γ := by
    apply Filter.Eventually.of_forall
    intro z
    exact (hf_meas.comp (measurable_const.add (measurable_const.mul measurable_id))).aestronglyMeasurable
  have hF_int : Integrable (F x) γ := by
    simpa [F, a, b] using
      standardGaussianMehler_integrand_integrable hf_meas hf_bounded t ht x
  have hF'_meas : AEStronglyMeasurable (F' x) γ := by
    exact (measurable_const.mul (hf.continuous_deriv_one.measurable.comp
      (measurable_const.add (measurable_const.mul measurable_id)))).aestronglyMeasurable
  have hdom : ∀ᵐ y ∂γ, ∀ z ∈ (Set.univ : Set ℝ), ‖F' z y‖ ≤ |a| * M₁ := by
    filter_upwards [] with y z hz
    dsimp [F']
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg a)
    simpa [Real.norm_eq_abs] using hM₁ (a * z + b * y)
  have hdom_int : Integrable (fun _ : ℝ => |a| * M₁) γ := integrable_const _
  have hpoint : ∀ᵐ y ∂γ, ∀ z ∈ (Set.univ : Set ℝ),
      HasDerivAt (F · y) (F' z y) z := by
    filter_upwards [] with y z hz
    have harg : HasDerivAt (fun w : ℝ => a * w + b * y) a z := by
      simpa [F, a, b, mul_comm] using
        (((hasDerivAt_id z).const_mul a).add_const (b * y))
    have hfpoint : HasDerivAt f (deriv f (a * z + b * y)) (a * z + b * y) :=
      (hf.differentiable_one (a * z + b * y)).hasDerivAt
    have hcomp := hfpoint.comp z harg
    exact hcomp.congr_deriv (by dsimp [F']; ring)
  have hparam := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Set.univ) (x₀ := x) (F := F) (F' := F')
    (show (Set.univ : Set ℝ) ∈ 𝓝 x from Filter.univ_mem)
    hF_meas hF_int hF'_meas hdom hdom_int hpoint
  have hfactor :
      (∫ y, a * deriv f (a * x + b * y) ∂γ) =
        a * ∫ y, deriv f (a * x + b * y) ∂γ := by
    rw [integral_const_mul]
  have hresult := hparam.2.congr_deriv (by simpa [F', a, b] using hfactor)
  simpa [standardGaussianMehlerAverage, F, a, b] using hresult

/-- The derivative of the first spatial derivative is the actual second
spatial derivative. Applying the first result to `f'` discharges the second
dominated derivative exchange with bound `|exp(-t)| * M₂`. -/
theorem standardGaussianMehlerAverage_secondSpatial_hasDerivAt
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hf_bounded : ∃ M₀ : ℝ, ∀ x, ‖f x‖ ≤ M₀)
    (hderiv_bounded : ∃ M₁ : ℝ, ∀ x, ‖deriv f x‖ ≤ M₁)
    (hsecond_bounded : ∃ M₂ : ℝ, ∀ x, ‖deriv (deriv f) x‖ ≤ M₂)
    (t : ℝ) (ht : 0 ≤ t) (x : ℝ) :
    HasDerivAt
      (fun z => deriv (fun w => standardGaussianMehlerAverage f
        hf.continuous.measurable hf_bounded t ht w) z)
      (Real.exp (-t) ^ 2 *
        ∫ y, deriv (deriv f)
          (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y) ∂γ) x := by
  let hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  let hf' : ContDiff ℝ 1 (deriv f) := hf.deriv'
  let hfm : Measurable f := hf.continuous.measurable
  let hf'm : Measurable (deriv f) := hf1.continuous_deriv_one.measurable
  have hfirst_eq : ∀ z,
      deriv (fun w => standardGaussianMehlerAverage f hfm hf_bounded t ht w) z =
        Real.exp (-t) * ∫ y, deriv f
          (Real.exp (-t) * z + Real.sqrt (1 - Real.exp (-2 * t)) * y) ∂γ := by
    intro z
    exact (standardGaussianMehlerAverage_hasDerivAt hf1 hfm hf_bounded
      hderiv_bounded t ht z).deriv
  have hsecond := standardGaussianMehlerAverage_hasDerivAt hf' hf'm hderiv_bounded
    hsecond_bounded t ht x
  have hrhs : HasDerivAt
      (fun z => Real.exp (-t) * standardGaussianMehlerAverage (deriv f) hf'm
        hderiv_bounded t ht z)
      (Real.exp (-t) * (Real.exp (-t) * ∫ y, deriv (deriv f)
        (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y) ∂γ)) x :=
    hsecond.const_mul (Real.exp (-t))
  have hfun :
      (fun z => deriv (fun w => standardGaussianMehlerAverage f hfm hf_bounded t ht w) z) =
        (fun z => Real.exp (-t) * standardGaussianMehlerAverage (deriv f) hf'm
          hderiv_bounded t ht z) := by
    funext z
    rw [hfirst_eq z]
    rfl
  rw [hfun]
  convert hrhs using 1; ring

/-- Positive-time evolution of the literal Gaussian kernel formula. The
derivative is taken within positive times; the statement makes no claim about
time differentiation at zero. -/
theorem standardGaussianMehler_integral_hasDerivAt_of_pos
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hf_bounded : ∃ M₀ : ℝ, ∀ x, ‖f x‖ ≤ M₀)
    (hderiv_bounded : ∃ M₁ : ℝ, ∀ x, ‖deriv f x‖ ≤ M₁)
    (hsecond_bounded : ∃ M₂ : ℝ, ∀ x, ‖deriv (deriv f) x‖ ≤ M₂)
    (x : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivWithinAt
      (fun s => ∫ y, f
        (Real.exp (-s) * x + Real.sqrt (1 - Real.exp (-2 * s)) * y) ∂γ)
      (Real.exp (-t) ^ 2 * ∫ y, deriv (deriv f)
        (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y) ∂γ -
        x * (Real.exp (-t) * ∫ y, deriv f
          (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y) ∂γ))
      (Set.Ioi 0) t := by
  let A : ℝ → ℝ := fun s => Real.exp (-s)
  let E : ℝ → ℝ := fun s => Real.exp (-2 * s)
  let B : ℝ → ℝ := Real.sqrt ∘ (fun s => 1 - E s)
  let D : ℝ → ℝ := fun s => E s / B s
  let F : ℝ → ℝ → ℝ := fun s y => f (A s * x + B s * y)
  let F' : ℝ → ℝ → ℝ := fun s y =>
    deriv f (A s * x + B s * y) * (-A s * x + D s * y)
  rcases hf_bounded with ⟨M₀, hM₀⟩
  rcases hderiv_bounded with ⟨M₁, hM₁⟩
  rcases hsecond_bounded with ⟨M₂, hM₂⟩
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hfprime : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hM₁_nonneg : 0 ≤ M₁ := le_trans (norm_nonneg (deriv f 0)) (hM₁ 0)
  have hM₂_nonneg : 0 ≤ M₂ := le_trans (norm_nonneg (deriv (deriv f) 0)) (hM₂ 0)
  have hA_deriv : ∀ s, HasDerivAt A (-A s) s := by
    intro s
    simpa [A] using ((hasDerivAt_id s).neg).exp
  have hE_deriv : ∀ s, HasDerivAt E (-2 * E s) s := by
    intro s
    have hlin : HasDerivAt (fun z : ℝ => -2 * z) (-2) s := by
      simpa using (hasDerivAt_id s).const_mul (-2)
    have hexp := hlin.exp
    simpa [E, mul_comm, mul_left_comm, mul_assoc] using hexp
  have hB_deriv : ∀ s, 0 < s → HasDerivAt B (D s) s := by
    intro s hs
    have hqpos : 0 < 1 - E s := by
      have hs' : -2 * s < 0 := by nlinarith
      have he : E s < 1 := by
        exact Real.exp_lt_one_iff.mpr hs'
      dsimp [E]
      linarith
    have hq_deriv : HasDerivAt (fun z : ℝ => 1 - E z) (2 * E s) s := by
      have h := (hE_deriv s).const_sub 1
      exact h.congr_deriv (by ring)
    have hBpos : 0 < B s := by
      dsimp [B]
      exact Real.sqrt_pos.2 hqpos
    have hB0 : B s ≠ 0 := ne_of_gt hBpos
    have hsqrt := (Real.hasDerivAt_sqrt (ne_of_gt hqpos)).comp s hq_deriv
    have hcoef : (1 / (2 * B s)) * (2 * E s) = D s := by
      dsimp [D]
      field_simp [hB0]
    have hfinal := hsqrt.congr_deriv hcoef
    change HasDerivAt B (D s) s
    exact hfinal
  have hA_cont : Continuous A := by
    exact Real.continuous_exp.comp continuous_neg
  have hE_cont : Continuous E := by
    exact Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hB_cont : Continuous B := by
    exact Real.continuous_sqrt.comp (continuous_const.sub hE_cont)
  have hBpos_t : 0 < B t := by
    have hqpos : 0 < 1 - E t := by
      have he : E t < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
      dsimp [E]
      linarith
    dsimp [B]
    exact Real.sqrt_pos.2 hqpos
  have hD_cont_at : ContinuousAt D t := by
    have h := hE_cont.continuousAt.div hB_cont.continuousAt (ne_of_gt hBpos_t)
    change ContinuousAt (fun s => E s / B s) t
    exact h
  let K_A : ℝ := ‖A t‖ + 1
  let K_D : ℝ := ‖D t‖ + 1
  let U : Set ℝ := {s | 0 < s ∧ ‖A s‖ ≤ K_A ∧ ‖D s‖ ≤ K_D}
  have hA_near : ∀ᶠ s in 𝓝 t, A s ∈ Metric.ball (A t) 1 := by
    exact hA_cont.continuousAt.eventually (Metric.ball_mem_nhds _ zero_lt_one)
  have hD_near : ∀ᶠ s in 𝓝 t, D s ∈ Metric.ball (D t) 1 := by
    exact hD_cont_at.eventually (Metric.ball_mem_nhds _ zero_lt_one)
  have hU : U ∈ 𝓝 t := by
    have hpositive : ∀ᶠ s in 𝓝 t, 0 < s := eventually_gt_nhds ht
    filter_upwards [hpositive, hA_near, hD_near] with s hs hAs hDs
    refine ⟨hs, ?_, ?_⟩
    · calc
        ‖A s‖ = ‖(A s - A t) + A t‖ := by congr 1; ring
        _ ≤ ‖A s - A t‖ + ‖A t‖ := norm_add_le _ _
        _ ≤ 1 + ‖A t‖ := by
          have : dist (A s) (A t) < 1 := hAs
          simpa [dist_eq_norm] using (le_of_lt this)
        _ = K_A := by simp [K_A, add_comm]
    · calc
        ‖D s‖ = ‖(D s - D t) + D t‖ := by congr 1; ring
        _ ≤ ‖D s - D t‖ + ‖D t‖ := norm_add_le _ _
        _ ≤ 1 + ‖D t‖ := by
          have : dist (D s) (D t) < 1 := hDs
          simpa [dist_eq_norm] using (le_of_lt this)
        _ = K_D := by simp [K_D, add_comm]
  have hF_meas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (F s) γ := by
    apply Filter.Eventually.of_forall
    intro s
    exact (hf.continuous.measurable.comp
      (measurable_const.add (measurable_const.mul measurable_id))).aestronglyMeasurable
  have hF_int : Integrable (F t) γ := by
    simpa [F, A, B, E] using
      standardGaussianMehler_integrand_integrable hf.continuous.measurable
        ⟨M₀, hM₀⟩ t (le_of_lt ht) x
  have hF'_meas : AEStronglyMeasurable (F' t) γ := by
    exact ((hfprime.continuous.comp
      (continuous_const.add (continuous_const.mul continuous_id))).mul
      (continuous_const.add (continuous_const.mul continuous_id))).aestronglyMeasurable
  let bound : ℝ → ℝ := fun y => M₁ * (K_A * ‖x‖ + K_D * ‖y‖)
  have hIdγ : Integrable id γ := by
    apply memLp_one_iff_integrable.mp
    exact ProbabilityTheory.memLp_id_gaussianReal (μ := 0) (v := (1 : ℝ≥0))
      (1 : ℝ≥0)
  have hbound_int : Integrable bound γ := by
    have hnorm : Integrable (fun y : ℝ => ‖y‖) γ := hIdγ.norm
    have hadd := (integrable_const (K_A * ‖x‖)).add (hnorm.const_mul K_D)
    have hmul := hadd.const_mul M₁
    exact hmul.congr (ae_of_all γ fun _ => rfl)
  have hbound : ∀ᵐ y ∂γ, ∀ s ∈ U, ‖F' s y‖ ≤ bound y := by
    filter_upwards [] with y s hs
    rcases hs with ⟨hspos, hAs, hDs⟩
    dsimp [F', bound]
    calc
      ‖deriv f (A s * x + B s * y) * (-A s * x + D s * y)‖
          = ‖deriv f (A s * x + B s * y)‖ * ‖-A s * x + D s * y‖ := norm_mul _ _
      _ ≤ M₁ * (‖A s * x‖ + ‖D s * y‖) := by
            apply mul_le_mul
            · exact hM₁ _
            · calc
                ‖-A s * x + D s * y‖ ≤ ‖-A s * x‖ + ‖D s * y‖ := norm_add_le _ _
                _ = ‖A s * x‖ + ‖D s * y‖ := by
                  calc
                    _ = ‖-A s‖ * ‖x‖ + ‖D s * y‖ := by rw [norm_mul]
                    _ = ‖A s‖ * ‖x‖ + ‖D s * y‖ := by rw [norm_neg]
                    _ = ‖A s * x‖ + ‖D s * y‖ := by rw [← norm_mul]
            · exact norm_nonneg _
            · exact hM₁_nonneg
      _ = M₁ * (‖A s‖ * ‖x‖ + ‖D s‖ * ‖y‖) := by rw [norm_mul, norm_mul]
      _ ≤ M₁ * (K_A * ‖x‖ + K_D * ‖y‖) := by
            apply mul_le_mul_of_nonneg_left _ hM₁_nonneg
            exact add_le_add (mul_le_mul_of_nonneg_right hAs (norm_nonneg _))
              (mul_le_mul_of_nonneg_right hDs (norm_nonneg _))
  have hpoint : ∀ᵐ y ∂γ, ∀ s ∈ U, HasDerivAt (F · y) (F' s y) s := by
    filter_upwards [] with y s hs
    rcases hs with ⟨hspos, hAs, hDs⟩
    have harg : HasDerivAt (fun z : ℝ => A z * x + B z * y)
        (-A s * x + D s * y) s := by
      have hA := (hA_deriv s).mul_const x
      have hB := (hB_deriv s hspos).mul_const y
      exact hA.add hB
    have hfpoint : HasDerivAt f (deriv f (A s * x + B s * y))
        (A s * x + B s * y) :=
      (hf1.differentiable_one (A s * x + B s * y)).hasDerivAt
    have hcomp := hfpoint.comp s harg
    exact hcomp.congr_deriv (by dsimp [F'])
  have hparam := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := U) (x₀ := t) (F := F) (F' := F') hU hF_meas hF_int hF'_meas
    hbound hbound_int hpoint
  let g : ℝ → ℝ := fun y => deriv f (A t * x + B t * y)
  have hargC1 : ContDiff ℝ 1 (fun y : ℝ => A t * x + B t * y) := by
    exact contDiff_const.add (contDiff_const.mul contDiff_id)
  have hgC1 : ContDiff ℝ 1 g := by
    exact hfprime.comp hargC1
  have hg_bounded : ∃ C : ℝ, ∀ y, ‖g y‖ ≤ C := by
    exact ⟨M₁, fun y => hM₁ _⟩
  have hg_deriv_eq : ∀ y,
      deriv g y = B t * deriv (deriv f) (A t * x + B t * y) := by
    intro y
    have harg : HasDerivAt (fun z : ℝ => A t * x + B t * z) (B t) y := by
      simpa using (hasDerivAt_id y).const_mul (B t) |>.const_add (A t * x)
    have hfp : HasDerivAt (deriv f)
        (deriv (deriv f) (A t * x + B t * y)) (A t * x + B t * y) :=
      (hfprime.differentiable_one _).hasDerivAt
    have hc := hfp.comp y harg
    have hfun : (deriv f) ∘ (fun z : ℝ => A t * x + B t * z) = g := by
      funext z
      simp [g]
    rw [hfun] at hc
    simpa [g, add_comm, mul_comm] using hc.deriv
  have hg_deriv_bounded : ∃ C : ℝ, ∀ y, ‖deriv g y‖ ≤ C := by
    refine ⟨‖B t‖ * M₂, ?_⟩
    intro y
    rw [hg_deriv_eq y, norm_mul]
    exact mul_le_mul_of_nonneg_left (hM₂ _) (norm_nonneg _)
  have hIBP := LOOConcentration.standardGaussian_integral_deriv_eq_mul_of_bounded
    hgC1 hg_bounded hg_deriv_bounded
  have hg_integrable : Integrable g γ := by
    apply integrable_of_measurable_norm_le
    · exact hfprime.continuous.measurable.comp
        (measurable_const.add (measurable_const.mul measurable_id))
    · exact fun y => hM₁ _
  have hy_g_integrable : Integrable (fun y : ℝ => y * g y) γ := hIBP.2.1
  have hIBP_simplified :
      (∫ y, y * g y ∂γ) = B t * ∫ y, deriv (deriv f) (A t * x + B t * y) ∂γ := by
    calc
      (∫ y, y * g y ∂γ) = ∫ y, deriv g y ∂γ := hIBP.2.2.symm
      _ = ∫ y, B t * deriv (deriv f) (A t * x + B t * y) ∂γ := by
        apply integral_congr_ae
        exact ae_of_all γ fun y => hg_deriv_eq y
      _ = B t * ∫ y, deriv (deriv f) (A t * x + B t * y) ∂γ := by
        rw [integral_const_mul]
  have hsplit :
      (∫ y, F' t y ∂γ) =
        (-A t * x) * ∫ y, g y ∂γ + D t * ∫ y, y * g y ∂γ := by
    calc
      (∫ y, F' t y ∂γ) =
          ∫ y, ((-A t * x) * g y + D t * (y * g y)) ∂γ := by
            apply integral_congr_ae
            exact ae_of_all γ fun y => by dsimp [F', g]; ring
      _ = _ := by
            rw [integral_add (hg_integrable.const_mul (-A t * x))
                (hy_g_integrable.const_mul (D t)),
              integral_const_mul, integral_const_mul]
  have htime := hparam.2
  have htime' : HasDerivAt
      (fun s => ∫ y, f (A s * x + B s * y) ∂γ)
      ((A t ^ 2) * ∫ y, deriv (deriv f) (A t * x + B t * y) ∂γ -
        x * (A t * ∫ y, g y ∂γ)) t := by
    have htimevalue : ∫ y, F' t y ∂γ =
        (-A t * x) * ∫ y, g y ∂γ + D t * ∫ y, y * g y ∂γ := hsplit
    have hid : D t * B t = A t ^ 2 := by
      dsimp [D, B, E, A]
      have hsqrt : Real.sqrt (1 - Real.exp (-2 * t)) ≠ 0 := ne_of_gt hBpos_t
      have hexp : Real.exp (-2 * t) = Real.exp (-t) ^ 2 := by
        rw [show -2 * t = -t + -t by ring, Real.exp_add]
        ring
      have hexp' : Real.exp (-(2 * t)) = Real.exp (-t) ^ 2 := by
        rw [show -(2 * t) = -2 * t by ring, hexp]
      have hsqrt' : Real.sqrt (1 - Real.exp (-t) ^ 2) ≠ 0 := by
        simpa [hexp'] using hsqrt
      rw [hexp]
      field_simp [hsqrt']
    have hval :
        (∫ y, F' t y ∂γ) =
          (A t ^ 2) * ∫ y, deriv (deriv f) (A t * x + B t * y) ∂γ -
            x * (A t * ∫ y, g y ∂γ) := by
      rw [htimevalue, hIBP_simplified]
      rw [← mul_assoc, hid]
      ring
    have htime' := htime.congr_deriv hval
    simpa [F, A, B, E, mul_comm, mul_left_comm, mul_assoc] using htime'
  simpa [A, B, E, g, mul_comm, mul_left_comm, mul_assoc] using
    (htime'.hasDerivWithinAt (s := Set.Ioi 0))

end LOOConcentration.Examples.GaussianMehlerCalculus
