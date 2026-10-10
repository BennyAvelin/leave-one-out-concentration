import LOOConcentration.Examples.GaussianMehlerCalculus
import LOOConcentration.Concentration.EntropyCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
# Weighted Gaussian integration by parts for entropy dissipation

This module proves the bounded-positive scalar dissipation identity used by
the Gaussian Mehler entropy argument. The time differentiation and energy
decay integration are separate steps.
-/

set_option autoImplicit false

namespace LOOConcentration.Examples.GaussianMehlerEntropy

open MeasureTheory
open scoped Topology

noncomputable abbrev γ : Measure ℝ := LOOConcentration.standardGaussianIBPMeasure

private theorem integrable_of_measurable_norm_le {g : ℝ → ℝ}
    (hg : Measurable g) {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) : Integrable g γ := by
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (g 0)) (hC 0)
  refine (integrable_const C).mono' hg.aestronglyMeasurable ?_
  filter_upwards [] with x
  simpa [Real.norm_eq_abs, abs_of_nonneg hC0] using hC x

private theorem norm_integral_le_of_pointwise {g : ℝ → ℝ}
    (hg : Integrable g γ) {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) :
    ‖∫ x, g x ∂γ‖ ≤ C := by
  calc
    ‖∫ x, g x ∂γ‖ ≤ ∫ x, ‖g x‖ ∂γ := norm_integral_le_integral_norm _
    _ ≤ ∫ _ : ℝ, C ∂γ := integral_mono hg.norm (integrable_const C) hC
    _ = C := by simp [γ, LOOConcentration.standardGaussianIBPMeasure]

/-! The unrestricted kernel trajectory below is private calculus infrastructure.
Its public interface is the reviewed bounded Mehler constructor on `t ≥ 0`. -/

private noncomputable def rawMehlerAverage (f : ℝ → ℝ)
    (t x : ℝ) : ℝ :=
  ∫ y, f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y) ∂γ

private theorem rawMehlerAverage_eq_source (f : ℝ → ℝ)
    (hf_meas : Measurable f) (hf_bounded : ∃ M : ℝ, ∀ x, ‖f x‖ ≤ M)
    (t : ℝ) (ht : 0 ≤ t) (x : ℝ) :
    rawMehlerAverage f t x =
      LOOConcentration.standardGaussianMehlerAverage f hf_meas hf_bounded t ht x := by
  have h := LOOConcentration.Examples.GaussianMehlerCalculus.standardGaussianMehlerAverage_eq_source
    f hf_meas hf_bounded t ht x
  have hraw : rawMehlerAverage f t x =
      LOOConcentration.Examples.GaussianMehlerCalculus.standardGaussianMehlerAverage
        f hf_meas hf_bounded t ht x := by
    rfl
  exact hraw.trans h

/-- The private literal trajectory is `C²` in space at valid times. -/
private theorem rawMehlerAverage_spatial_regular
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hf_bounded : ∃ M₀ : ℝ, ∀ x, ‖f x‖ ≤ M₀)
    (M₁ M₂ : ℝ) (hderiv_bounded : ∀ x, ‖deriv f x‖ ≤ M₁)
    (hsecond_bounded : ∀ x, ‖deriv (deriv f) x‖ ≤ M₂)
    (t : ℝ) (ht : 0 ≤ t) :
    ContDiff ℝ 2 (fun x => rawMehlerAverage f t x) ∧
      (∀ x, ‖deriv (fun z => rawMehlerAverage f t z) x‖ ≤ M₁) ∧
      (∀ x, ‖deriv (deriv (fun z => rawMehlerAverage f t z)) x‖ ≤ M₂) := by
  let P := LOOConcentration.Examples.GaussianMehlerCalculus.standardGaussianMehlerAverage
    f hf.continuous.measurable hf_bounded t ht
  have hM₁ := hderiv_bounded
  have hM₂ := hsecond_bounded
  have hM₁_nonneg : 0 ≤ M₁ := le_trans (norm_nonneg (deriv f 0)) (hM₁ 0)
  have hM₂_nonneg : 0 ≤ M₂ := le_trans
    (norm_nonneg (deriv (deriv f) 0)) (hM₂ 0)
  let a : ℝ := Real.exp (-t)
  let b : ℝ := Real.sqrt (1 - Real.exp (-2 * t))
  let p₁ : ℝ → ℝ := fun x => ∫ y, deriv f (a * x + b * y) ∂γ
  let p₂ : ℝ → ℝ := fun x => ∫ y, deriv (deriv f) (a * x + b * y) ∂γ
  let hf₁ : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have ha_nonneg : 0 ≤ a := by dsimp [a]; positivity
  have ha_le_one : a ≤ 1 := by
    dsimp [a]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have harg_meas : Measurable (fun z : ℝ × ℝ => a * z.1 + b * z.2) := by
    fun_prop
  have hp₁_cont : Continuous p₁ := by
    apply continuous_of_dominated (bound := fun _ : ℝ => M₁)
    · intro x
      exact (hf₁.continuous_deriv_one.measurable.comp
        (measurable_const.add (measurable_const.mul measurable_id))).aestronglyMeasurable
    · intro x
      filter_upwards [] with y
      simpa [p₁, a, b, Real.norm_eq_abs] using hM₁ (a * x + b * y)
    · exact integrable_const M₁
    · filter_upwards [] with y
      exact hf₁.continuous_deriv_one.comp
        (by fun_prop : Continuous (fun x : ℝ => a * x + b * y))
  have hp₂_cont : Continuous p₂ := by
    apply continuous_of_dominated (bound := fun _ : ℝ => M₂)
    · intro x
      exact (hf.deriv').continuous_deriv_one.measurable.comp
        (measurable_const.add (measurable_const.mul measurable_id)) |>.aestronglyMeasurable
    · intro x
      filter_upwards [] with y
      simpa [p₂, a, b, Real.norm_eq_abs] using hM₂ (a * x + b * y)
    · exact integrable_const M₂
    · filter_upwards [] with y
      exact (hf.deriv').continuous_deriv_one.comp
        (by fun_prop : Continuous (fun x : ℝ => a * x + b * y))
  have hfirst : ∀ x,
      HasDerivAt P (a * p₁ x) x := by
    intro x
    have h := LOOConcentration.Examples.GaussianMehlerCalculus.standardGaussianMehlerAverage_hasDerivAt
      hf₁ hf.continuous.measurable hf_bounded
      ⟨M₁, hM₁⟩ t ht x
    simpa [P, p₁, a, b] using h
  have hsecond : ∀ x, HasDerivAt (deriv P) (a ^ 2 * p₂ x) x := by
    intro x
    have h := LOOConcentration.Examples.GaussianMehlerCalculus.standardGaussianMehlerAverage_secondSpatial_hasDerivAt
      hf hf_bounded ⟨M₁, hM₁⟩ ⟨M₂, hM₂⟩ t ht x
    simpa [P, p₂, a, b] using h
  have hPdiff : Differentiable ℝ P := by
    intro x
    exact (hfirst x).differentiableAt
  have hP'cont : Continuous (deriv P) := by
    have hEq : deriv P = fun x => a * p₁ x := by
      funext x
      exact (hfirst x).deriv
    rw [hEq]
    exact continuous_const.mul hp₁_cont
  have hP_C1 : ContDiff ℝ 1 P := contDiff_one_iff_deriv.mpr ⟨hPdiff, hP'cont⟩
  have hP'diff : Differentiable ℝ (deriv P) := by
    intro x
    exact (hsecond x).differentiableAt
  have hP''cont : Continuous (deriv (deriv P)) := by
    have hEq : deriv (deriv P) = fun x => a ^ 2 * p₂ x := by
      funext x
      exact (hsecond x).deriv
    rw [hEq]
    exact continuous_const.mul hp₂_cont
  have hP'_C1 : ContDiff ℝ 1 (deriv P) :=
    contDiff_one_iff_deriv.mpr ⟨hP'diff, hP''cont⟩
  have hP_C2 : ContDiff ℝ 2 P := by
    have htemp : ContDiff ℝ (1 + 1) P := by
      exact (contDiff_succ_iff_deriv (𝕜 := ℝ) (n := 1) (f := P)).mpr
        ⟨hPdiff, by simp, hP'_C1⟩
    convert htemp using 1
    norm_num
  have hp₁_int : ∀ x, Integrable (fun y => deriv f (a * x + b * y)) γ := by
    intro x
    have hm : Measurable (deriv f) := hf₁.continuous_deriv_one.measurable
    simpa [a, b, γ] using
      LOOConcentration.Examples.GaussianMehlerCalculus.standardGaussianMehler_integrand_integrable
        hm ⟨M₁, hM₁⟩ t ht x
  have hp₂_int : ∀ x, Integrable (fun y => deriv (deriv f) (a * x + b * y)) γ := by
    intro x
    have hm : Measurable (deriv (deriv f)) := (hf.deriv').continuous_deriv_one.measurable
    simpa [a, b, γ] using
      LOOConcentration.Examples.GaussianMehlerCalculus.standardGaussianMehler_integrand_integrable
        hm ⟨M₂, hM₂⟩ t ht x
  have hp₁_bound : ∀ x, ‖p₁ x‖ ≤ M₁ := by
    intro x
    exact norm_integral_le_of_pointwise (hp₁_int x) (fun y => hM₁ _)
  have hp₂_bound : ∀ x, ‖p₂ x‖ ≤ M₂ := by
    intro x
    exact norm_integral_le_of_pointwise (hp₂_int x) (fun y => hM₂ _)
  have hresult : ContDiff ℝ 2 P ∧
      (∀ x, ‖deriv P x‖ ≤ M₁) ∧
      (∀ x, ‖deriv (deriv P) x‖ ≤ M₂) := by
    refine ⟨hP_C2, ?_, ?_⟩
    · intro x
      rw [(hfirst x).deriv]
      calc
        ‖a * p₁ x‖ = ‖a‖ * ‖p₁ x‖ := norm_mul _ _
        _ ≤ 1 * ‖p₁ x‖ := mul_le_mul_of_nonneg_right
          (by simpa [Real.norm_eq_abs, abs_of_nonneg ha_nonneg] using ha_le_one)
          (norm_nonneg _)
        _ ≤ 1 * M₁ := mul_le_mul_of_nonneg_left (hp₁_bound x) (by norm_num)
        _ = M₁ := by ring
    · intro x
      rw [(hsecond x).deriv]
      have ha_sq : ‖a ^ 2‖ ≤ 1 := by
        rw [norm_pow]
        calc
          ‖a‖ ^ 2 ≤ 1 ^ 2 := by
            have ha : ‖a‖ ≤ 1 := by
              simpa [Real.norm_eq_abs, abs_of_nonneg ha_nonneg] using ha_le_one
            nlinarith [norm_nonneg a]
          _ = 1 := by norm_num
      calc
        ‖a ^ 2 * p₂ x‖ = ‖a ^ 2‖ * ‖p₂ x‖ := norm_mul _ _
        _ ≤ 1 * ‖p₂ x‖ := mul_le_mul_of_nonneg_right ha_sq (norm_nonneg _)
        _ ≤ 1 * M₂ := mul_le_mul_of_nonneg_left (hp₂_bound x) (by norm_num)
        _ = M₂ := by ring
  have hsource_raw : ∀ x,
      LOOConcentration.standardGaussianMehlerAverage f hf.continuous.measurable hf_bounded t ht x =
        rawMehlerAverage f t x := by
    intro x
    simp [LOOConcentration.standardGaussianMehlerAverage, rawMehlerAverage,
      LOOConcentration.standardGaussianMehlerArgument, LOOConcentration.standardGaussianMehlerDrift,
      LOOConcentration.standardGaussianMehlerNoise, γ, LOOConcentration.standardGaussianIBPMeasure,
      LOOConcentration.standardGaussianMehler]
  have hP_eq : P = fun x => rawMehlerAverage f t x := by
    funext x
    exact (LOOConcentration.Examples.GaussianMehlerCalculus.standardGaussianMehlerAverage_eq_source
      f hf.continuous.measurable hf_bounded t ht x).trans (hsource_raw x)
  rw [hP_eq] at hresult
  exact hresult

/-- The canonical bounded Mehler average of a bounded `C²` input is `C²` in
space at every nonnegative time, and its first two spatial derivatives retain
the input's global bounds. -/
theorem standardGaussianMehlerAverage_spatial_regular
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hf_bounded : ∃ M₀ : ℝ, ∀ x, ‖f x‖ ≤ M₀)
    (M₁ M₂ : ℝ) (hderiv_bounded : ∀ x, ‖deriv f x‖ ≤ M₁)
    (hsecond_bounded : ∀ x, ‖deriv (deriv f) x‖ ≤ M₂)
    (t : ℝ) (ht : 0 ≤ t) :
    ContDiff ℝ 2 (LOOConcentration.standardGaussianMehlerAverage f
        hf.continuous.measurable hf_bounded t ht) ∧
      (∀ x, ‖deriv (LOOConcentration.standardGaussianMehlerAverage f
        hf.continuous.measurable hf_bounded t ht) x‖ ≤ M₁) ∧
      (∀ x, ‖deriv (deriv (LOOConcentration.standardGaussianMehlerAverage f
        hf.continuous.measurable hf_bounded t ht)) x‖ ≤ M₂) := by
  have hraw := rawMehlerAverage_spatial_regular hf hf_bounded M₁ M₂
    hderiv_bounded hsecond_bounded t ht
  have hbridge : (fun x => rawMehlerAverage f t x) =
      LOOConcentration.standardGaussianMehlerAverage f hf.continuous.measurable hf_bounded t ht := by
    funext x
    exact rawMehlerAverage_eq_source f hf.continuous.measurable hf_bounded t ht x
  constructor
  · rw [← hbridge]
    exact hraw.1
  constructor
  · intro x
    rw [← hbridge]
    exact hraw.2.1 x
  · intro x
    rw [← hbridge]
    exact hraw.2.2 x

/-- Entropy with respect to the actual standard Gaussian probability law. -/
private noncomputable def rawGaussianEntropy (u : ℝ → ℝ) : ℝ :=
  (∫ x, u x * Real.log (u x) ∂γ) -
    (∫ x, u x ∂γ) * Real.log (∫ x, u x ∂γ)

/-- Entropy of the literal Gaussian Mehler average. -/
private noncomputable def rawMehlerEntropy (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  rawGaussianEntropy (fun x => rawMehlerAverage f t x)

/-! The public entropy constructor is restricted to bounded positive inputs and
the canonical nonnegative-time Mehler average. -/

noncomputable def standardGaussianMehlerEntropy
    (f : ℝ → ℝ) (hf_meas : Measurable f) (M₀ ε : ℝ)
    (hbounded : ∀ x, ‖f x‖ ≤ M₀) (_hε : 0 < ε)
    (_hlower : ∀ x, ε ≤ f x) (t : ℝ) (ht : 0 ≤ t) : ℝ :=
  LOOConcentration.looconcentrationEntropy LOOConcentration.standardGaussianMehler
    (LOOConcentration.standardGaussianMehlerAverage f hf_meas ⟨M₀, hbounded⟩ t ht)

/-- The canonical bounded-positive Mehler average is measurable, stays
strictly positive, and has finite entropy integrals and positive mean. -/
theorem standardGaussianMehlerEntropy_facts
    {f : ℝ → ℝ} (hf_meas : Measurable f) (M₀ ε : ℝ)
    (hbounded : ∀ x, ‖f x‖ ≤ M₀) (hε : 0 < ε)
    (hlower : ∀ x, ε ≤ f x) (t : ℝ) (ht : 0 ≤ t) :
    Measurable (LOOConcentration.standardGaussianMehlerAverage f hf_meas
      ⟨M₀, hbounded⟩ t ht) ∧
    (∀ x, 0 < LOOConcentration.standardGaussianMehlerAverage f hf_meas
      ⟨M₀, hbounded⟩ t ht x) ∧
    Integrable (LOOConcentration.standardGaussianMehlerAverage f hf_meas
      ⟨M₀, hbounded⟩ t ht) γ ∧
    Integrable (fun x => LOOConcentration.standardGaussianMehlerAverage f hf_meas
      ⟨M₀, hbounded⟩ t ht x * Real.log
        (LOOConcentration.standardGaussianMehlerAverage f hf_meas ⟨M₀, hbounded⟩ t ht x)) γ ∧
    0 < ∫ x, LOOConcentration.standardGaussianMehlerAverage f hf_meas
      ⟨M₀, hbounded⟩ t ht x ∂γ := by
  let P : ℝ → ℝ := LOOConcentration.standardGaussianMehlerAverage f hf_meas
    ⟨M₀, hbounded⟩ t ht
  have hM₀_nonneg : 0 ≤ M₀ := le_trans (norm_nonneg (f 0)) (hbounded 0)
  have hεM₀ : ε ≤ M₀ := by
    have hupper : f 0 ≤ M₀ := (abs_le.mp (by
      simpa only [Real.norm_eq_abs] using hbounded 0)).2
    exact (hlower 0).trans hupper
  have hP_meas : Measurable P :=
    LOOConcentration.measurable_standardGaussianMehlerAverage hf_meas ⟨M₀, hbounded⟩ t ht
  have hP_bounds : ∀ x, ε ≤ P x ∧ P x ≤ M₀ := by
    intro x
    refine ⟨?_, ?_⟩
    · exact LOOConcentration.standardGaussianMehlerAverage_lower_bound hf_meas hbounded
        hlower t ht x
    · exact (LOOConcentration.standardGaussianMehlerAverage_bounds hf_meas hbounded t ht x).2
  have hP_pos : ∀ x, 0 < P x := fun x => lt_of_lt_of_le hε (hP_bounds x).1
  have hP_norm : ∀ x, ‖P x‖ ≤ M₀ := by
    intro x
    rw [Real.norm_eq_abs, abs_of_pos (hP_pos x)]
    exact (hP_bounds x).2
  have hP_integrable : Integrable P γ := by
    simpa [P, γ, LOOConcentration.standardGaussianIBPMeasure, LOOConcentration.standardGaussianMehler] using
      integrable_of_measurable_norm_le hP_meas hP_norm
  let L : ℝ := ‖Real.log ε‖ + ‖Real.log M₀‖
  have hlog_bound : ∀ x, ‖Real.log (P x)‖ ≤ L := by
    intro x
    have hlo := Real.log_le_log hε (hP_bounds x).1
    have hhi := Real.log_le_log (hP_pos x) (hP_bounds x).2
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · calc
        -L = -‖Real.log ε‖ - ‖Real.log M₀‖ := by dsimp [L]; ring
        _ ≤ -‖Real.log ε‖ := by linarith [norm_nonneg (Real.log M₀)]
        _ ≤ Real.log ε := neg_abs_le _
        _ ≤ Real.log (P x) := hlo
    · calc
        Real.log (P x) ≤ Real.log M₀ := hhi
        _ ≤ ‖Real.log M₀‖ := le_abs_self _
        _ ≤ L := by
          dsimp [L]
          exact le_add_of_nonneg_left (abs_nonneg (Real.log ε))
  have hPlog_meas : Measurable (fun x => P x * Real.log (P x)) :=
    Real.continuous_mul_log.measurable.comp hP_meas
  have hPlog_norm : ∀ x, ‖P x * Real.log (P x)‖ ≤ M₀ * L := by
    intro x
    rw [norm_mul]
    exact mul_le_mul (hP_norm x) (hlog_bound x) (norm_nonneg _) hM₀_nonneg
  have hPlog_integrable : Integrable (fun x => P x * Real.log (P x)) γ :=
    integrable_of_measurable_norm_le hPlog_meas hPlog_norm
  have hmean_lower : ε ≤ ∫ x, P x ∂γ := by
    calc
      ε = ∫ _ : ℝ, ε ∂γ := by simp [γ, LOOConcentration.standardGaussianIBPMeasure]
      _ ≤ ∫ x, P x ∂γ := integral_mono (integrable_const ε) hP_integrable
        (fun x => (hP_bounds x).1)
  refine ⟨hP_meas, hP_pos, hP_integrable, hPlog_integrable, ?_⟩
  exact lt_of_lt_of_le hε hmean_lower

private theorem rawMehlerEntropy_eq_standardGaussianMehlerEntropy
    (f : ℝ → ℝ) (hf_meas : Measurable f) (M₀ ε : ℝ)
    (hbounded : ∀ x, ‖f x‖ ≤ M₀) (hε : 0 < ε)
    (hlower : ∀ x, ε ≤ f x) (t : ℝ) (ht : 0 ≤ t) :
    rawMehlerEntropy f t =
      standardGaussianMehlerEntropy f hf_meas M₀ ε hbounded hε hlower t ht := by
  have hfun : (fun x => rawMehlerAverage f t x) =
      LOOConcentration.standardGaussianMehlerAverage f hf_meas ⟨M₀, hbounded⟩ t ht := by
    funext x
    exact rawMehlerAverage_eq_source f hf_meas ⟨M₀, hbounded⟩ t ht x
  unfold rawMehlerEntropy rawGaussianEntropy standardGaussianMehlerEntropy
    LOOConcentration.looconcentrationEntropy
  rw [hfun]

/-- The weighted Gaussian integration-by-parts identity for a positive bounded
`C²` function. This is the actual dissipation formula for the scalar OU
generator; the returned integrability facts justify both integrals. -/
theorem standardGaussian_boundedPositive_generator_entropy_dissipation
    {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u)
    (ε B : ℝ) (hε : 0 < ε)
    (hbounds : ∀ x, ε ≤ u x ∧ u x ≤ B)
    (hderiv_bounded : ∃ M₁ : ℝ, ∀ x, ‖deriv u x‖ ≤ M₁)
    (hsecond_bounded : ∃ M₂ : ℝ, ∀ x, ‖deriv (deriv u) x‖ ≤ M₂) :
    Integrable (fun x => (deriv (deriv u) x - x * deriv u x) *
      (Real.log (u x) + 1)) γ ∧
    Integrable (fun x => (deriv u x) ^ 2 / u x) γ ∧
    (∫ x, (deriv (deriv u) x - x * deriv u x) *
        (Real.log (u x) + 1) ∂γ) =
      -(∫ x, (deriv u x) ^ 2 / u x ∂γ) := by
  rcases hderiv_bounded with ⟨M₁, hM₁⟩
  rcases hsecond_bounded with ⟨M₂, hM₂⟩
  let hu₁ : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  let hu' : ContDiff ℝ 1 (deriv u) := hu.deriv'
  have hM₁_nonneg : 0 ≤ M₁ := le_trans (norm_nonneg (deriv u 0)) (hM₁ 0)
  have hM₂_nonneg : 0 ≤ M₂ := le_trans
    (norm_nonneg (deriv (deriv u) 0)) (hM₂ 0)
  have hBpos : 0 < B :=
    lt_of_lt_of_le hε ((hbounds 0).1.trans (hbounds 0).2)
  let L : ℝ := ‖Real.log ε‖ + ‖Real.log B‖
  have hL_nonneg : 0 ≤ L := by dsimp [L]; positivity
  have hlog_bound : ∀ x, ‖Real.log (u x)‖ ≤ L := by
    intro x
    have hx := hbounds x
    have hpos : 0 < u x := lt_of_lt_of_le hε hx.1
    have hlo := Real.log_le_log hε hx.1
    have hhi := Real.log_le_log hpos hx.2
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · calc
        -L = -‖Real.log ε‖ - ‖Real.log B‖ := by dsimp [L]; ring
        _ ≤ -‖Real.log ε‖ := by linarith [norm_nonneg (Real.log B)]
        _ ≤ Real.log ε := neg_abs_le _
        _ ≤ Real.log (u x) := hlo
    · calc
        Real.log (u x) ≤ Real.log B := hhi
        _ ≤ ‖Real.log B‖ := le_abs_self _
        _ ≤ L := by
          dsimp [L]
          exact le_add_of_nonneg_left (abs_nonneg (Real.log ε))
  have hu_nonzero : ∀ x, u x ≠ 0 := fun x => ne_of_gt
    (lt_of_lt_of_le hε (hbounds x).1)
  have hlog_cont : ContDiff ℝ 1 (fun x => Real.log (u x)) :=
    hu₁.log hu_nonzero
  let g : ℝ → ℝ := fun x => deriv u x * Real.log (u x)
  have hg_cont : ContDiff ℝ 1 g := by
    exact hu'.mul hlog_cont
  have hg_deriv : ∀ x,
      deriv g x = deriv (deriv u) x * Real.log (u x) +
        (deriv u x) ^ 2 / u x := by
    intro x
    have hux : 0 < u x := lt_of_lt_of_le hε (hbounds x).1
    have hu_at := (hu₁.differentiable_one x).hasDerivAt
    have hu'_at := (hu'.differentiable_one x).hasDerivAt
    have hlog_at := hu_at.log (ne_of_gt hux)
    have hproduct := hu'_at.mul hlog_at
    have hproduct' : HasDerivAt g
      (deriv (deriv u) x * Real.log (u x) +
          (deriv u x) ^ 2 / u x) x := by
      exact hproduct.congr_deriv (by
        field_simp [ne_of_gt hux])
    exact hproduct'.deriv
  let g_bound : ℝ := M₁ * L
  have hg_bounded : ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C := by
    refine ⟨g_bound, ?_⟩
    intro x
    change |deriv u x * Real.log (u x)| ≤ M₁ * L
    rw [abs_mul]
    exact mul_le_mul
      (by simpa [Real.norm_eq_abs] using hM₁ x)
      (by simpa [Real.norm_eq_abs] using hlog_bound x)
      (abs_nonneg _) hM₁_nonneg
  let gderiv_bound : ℝ := M₂ * L + M₁ ^ 2 / ε
  have hquot_bound : ∀ x, ‖(deriv u x) ^ 2 / u x‖ ≤ M₁ ^ 2 / ε := by
    intro x
    have hux : 0 < u x := lt_of_lt_of_le hε (hbounds x).1
    have hnormsq : ‖deriv u x‖ ^ 2 ≤ M₁ ^ 2 := by
      nlinarith [hM₁ x, norm_nonneg (deriv u x)]
    calc
      ‖(deriv u x) ^ 2 / u x‖ = ‖deriv u x‖ ^ 2 / u x := by
        simp [norm_div, norm_pow, Real.norm_eq_abs, abs_of_pos hux]
      _ ≤ M₁ ^ 2 / ε := div_le_div₀ (sq_nonneg M₁) hnormsq hε (hbounds x).1
  have hgderiv_bounded : ∃ C : ℝ, ∀ x, ‖deriv g x‖ ≤ C := by
    refine ⟨gderiv_bound, ?_⟩
    intro x
    rw [hg_deriv x]
    calc
      ‖deriv (deriv u) x * Real.log (u x) +
          (deriv u x) ^ 2 / u x‖
          ≤ ‖deriv (deriv u) x * Real.log (u x)‖ +
            ‖(deriv u x) ^ 2 / u x‖ := norm_add_le _ _
      _ ≤ M₂ * L + M₁ ^ 2 / ε := by
            apply add_le_add
            · rw [norm_mul]
              exact mul_le_mul (hM₂ x) (hlog_bound x) (norm_nonneg _) hM₂_nonneg
            · exact hquot_bound x
  have hIBP_u' := LOOConcentration.standardGaussian_integral_deriv_eq_mul_of_bounded
    hu' ⟨M₁, hM₁⟩ ⟨M₂, hM₂⟩
  have hIBP_g := LOOConcentration.standardGaussian_integral_deriv_eq_mul_of_bounded
    hg_cont hg_bounded hgderiv_bounded
  have hlogplus_bounded : ∀ x, ‖Real.log (u x) + 1‖ ≤ L + 1 := by
    intro x
    calc
      ‖Real.log (u x) + 1‖ ≤ ‖Real.log (u x)‖ + ‖(1 : ℝ)‖ := norm_add_le _ _
      _ ≤ L + 1 := add_le_add (hlog_bound x) (by norm_num)
  have hlogplus_meas : Measurable (fun x : ℝ => Real.log (u x) + 1) := by
    exact (hlog_cont.continuous.add continuous_const).measurable
  have hbase_integrable : Integrable
      (fun x => deriv (deriv u) x - x * deriv u x) γ :=
    hIBP_u'.1.sub hIBP_u'.2.1
  have hleft_integrable : Integrable
      (fun x => (deriv (deriv u) x - x * deriv u x) *
        (Real.log (u x) + 1)) γ := by
    exact hbase_integrable.mul_bdd hlogplus_meas.aestronglyMeasurable
      (ae_of_all γ fun x => hlogplus_bounded x)
  have henergy_bounded : ∀ x, ‖(deriv u x) ^ 2 / u x‖ ≤ M₁ ^ 2 / ε := hquot_bound
  have henergy_integrable : Integrable (fun x => (deriv u x) ^ 2 / u x) γ := by
    apply integrable_of_measurable_norm_le
    · have hnum : Measurable (fun x : ℝ => deriv u x * deriv u x) :=
        hu₁.continuous_deriv_one.measurable.mul hu₁.continuous_deriv_one.measurable
      have hdiv := hnum.div hu.continuous.measurable
      change Measurable (fun x : ℝ => (deriv u x * deriv u x) / u x) at hdiv
      simpa [pow_two] using hdiv
    · exact henergy_bounded
  have hu2log_integrable : Integrable
      (fun x => deriv (deriv u) x * Real.log (u x)) γ := by
    apply integrable_of_measurable_norm_le
    · exact (hu'.continuous_deriv_one.measurable.mul
        hlog_cont.continuous.measurable)
    · intro x
      rw [norm_mul]
      exact mul_le_mul (hM₂ x) (hlog_bound x) (norm_nonneg _) hM₂_nonneg
  have hmeanInt_u' : Integrable (fun x => x * deriv u x) γ := hIBP_u'.2.1
  have hxg_integrable : Integrable (fun x => x * g x) γ := hIBP_g.2.1
  let U₂log : ℝ → ℝ := fun x => deriv (deriv u) x * Real.log (u x)
  let U₂ : ℝ → ℝ := fun x => deriv (deriv u) x
  let Xg : ℝ → ℝ := fun x => x * g x
  let Xu' : ℝ → ℝ := fun x => x * deriv u x
  have hsum_integrable : Integrable (U₂log + U₂) γ :=
    hu2log_integrable.add hIBP_u'.1
  have hsum_sub_g_integrable : Integrable (U₂log + U₂ - Xg) γ :=
    hsum_integrable.sub hxg_integrable
  have hderiv_g_integral :
      (∫ x, deriv g x ∂γ) =
        (∫ x, deriv (deriv u) x * Real.log (u x) ∂γ) +
          (∫ x, (deriv u x) ^ 2 / u x ∂γ) := by
    calc
      (∫ x, deriv g x ∂γ) =
          ∫ x, (deriv (deriv u) x * Real.log (u x) +
            (deriv u x) ^ 2 / u x) ∂γ := by
              apply integral_congr_ae
              exact ae_of_all γ fun x => hg_deriv x
      _ = _ := by rw [integral_add hu2log_integrable henergy_integrable]
  have hxg_eq :
      (∫ x, x * g x ∂γ) =
        (∫ x, deriv (deriv u) x * Real.log (u x) ∂γ) +
          (∫ x, (deriv u x) ^ 2 / u x ∂γ) :=
    hIBP_g.2.2.symm.trans hderiv_g_integral
  have hLHS_expand :
      (∫ x, (deriv (deriv u) x - x * deriv u x) *
        (Real.log (u x) + 1) ∂γ) =
      (∫ x, deriv (deriv u) x * Real.log (u x) ∂γ) +
        (∫ x, deriv (deriv u) x ∂γ) -
        (∫ x, x * g x ∂γ) -
        (∫ x, x * deriv u x ∂γ) := by
    calc
      _ = ∫ x, (U₂log + U₂ - Xg - Xu') x ∂γ := by
            apply integral_congr_ae
            exact ae_of_all γ fun x => by dsimp [U₂log, U₂, Xg, Xu', g]; ring
      _ = (∫ x, (U₂log + U₂ - Xg) x ∂γ) - ∫ x, Xu' x ∂γ :=
            integral_sub hsum_sub_g_integrable hmeanInt_u'
      _ = ((∫ x, (U₂log + U₂) x ∂γ) - ∫ x, Xg x ∂γ) -
          ∫ x, Xu' x ∂γ := by
            have hsub := integral_sub hsum_integrable hxg_integrable
            exact congrArg (fun z : ℝ => z - ∫ x, Xu' x ∂γ) hsub
      _ = ((∫ x, U₂log x ∂γ) + ∫ x, U₂ x ∂γ) -
          ∫ x, Xg x ∂γ - ∫ x, Xu' x ∂γ := by
            have hadd := integral_add hu2log_integrable hIBP_u'.1
            exact congrArg (fun z : ℝ => z - ∫ x, Xg x ∂γ - ∫ x, Xu' x ∂γ) hadd
  refine ⟨hleft_integrable, henergy_integrable, ?_⟩
  rw [hLHS_expand, hxg_eq, hIBP_u'.2.2]
  ring

/-- Positive-time entropy dissipation for the actual standard Gaussian Mehler
kernel. The outer entropy integral is differentiated by dominated
differentiation on positive times; stationarity cancels the derivative of its
mean normalization, and the bounded Gaussian IBP identity gives the exact
coefficient-one energy. -/
private theorem rawMehlerEntropy_hasDerivAt
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (M₀ M₁ M₂ ε : ℝ)
    (hbounded : ∀ x, ‖f x‖ ≤ M₀)
    (hderiv_bounded : ∀ x, ‖deriv f x‖ ≤ M₁)
    (hsecond_bounded : ∀ x, ‖deriv (deriv f) x‖ ≤ M₂)
    (hε : 0 < ε) (hlower : ∀ x, ε ≤ f x)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => rawMehlerEntropy f s)
      (-(∫ x, (deriv (fun z => rawMehlerAverage f t z) x) ^ 2 /
        rawMehlerAverage f t x ∂γ)) t := by
  let hf_meas : Measurable f := hf.continuous.measurable
  let hf_bound : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := ⟨M₀, hbounded⟩
  have hM₀_nonneg : 0 ≤ M₀ := le_trans (norm_nonneg (f 0)) (hbounded 0)
  have hM₁_nonneg : 0 ≤ M₁ := le_trans (norm_nonneg (deriv f 0)) (hderiv_bounded 0)
  have hM₂_nonneg : 0 ≤ M₂ := le_trans
    (norm_nonneg (deriv (deriv f) 0)) (hsecond_bounded 0)
  have hεM₀ : ε ≤ M₀ := by
    have hle : f 0 ≤ M₀ := (abs_le.mp (by
      simpa only [Real.norm_eq_abs] using hbounded 0)).2
    exact (hlower 0).trans hle
  have hM₀_pos : 0 < M₀ := lt_of_lt_of_le hε hεM₀
  have hbridge : ∀ (s : ℝ) (hs : 0 ≤ s) (x : ℝ),
      rawMehlerAverage f s x =
        LOOConcentration.standardGaussianMehlerAverage f hf_meas hf_bound s hs x := by
    intro s hs x
    have h := LOOConcentration.Examples.GaussianMehlerCalculus.standardGaussianMehlerAverage_eq_source
      f hf_meas hf_bound s hs x
    have hraw_local : rawMehlerAverage f s x =
        LOOConcentration.Examples.GaussianMehlerCalculus.standardGaussianMehlerAverage
          f hf_meas hf_bound s hs x := by
      rfl
    exact hraw_local.trans h
  have hP_bounds : ∀ (s : ℝ) (hs : 0 ≤ s) (x : ℝ),
      ε ≤ rawMehlerAverage f s x ∧
        rawMehlerAverage f s x ≤ M₀ := by
    intro s hs x
    have hlow' := LOOConcentration.standardGaussianMehlerAverage_lower_bound
      hf_meas hbounded hlower s hs x
    have hb' := LOOConcentration.standardGaussianMehlerAverage_bounds
      hf_meas hbounded s hs x
    constructor
    · calc
        ε ≤ LOOConcentration.standardGaussianMehlerAverage f hf_meas hf_bound s hs x := hlow'
        _ = rawMehlerAverage f s x := (hbridge s hs x).symm
    · calc
        rawMehlerAverage f s x =
            LOOConcentration.standardGaussianMehlerAverage f hf_meas hf_bound s hs x := hbridge s hs x
        _ ≤ M₀ := hb'.2
  let L : ℝ := ‖Real.log ε‖ + ‖Real.log M₀‖
  have hL_nonneg : 0 ≤ L := by dsimp [L]; positivity
  have hlog_bound : ∀ (s : ℝ) (hs : 0 ≤ s) (x : ℝ),
      ‖Real.log (rawMehlerAverage f s x)‖ ≤ L := by
    intro s hs x
    have hx := hP_bounds s hs x
    have hpos : 0 < rawMehlerAverage f s x :=
      lt_of_lt_of_le hε hx.1
    have hlo := Real.log_le_log hε hx.1
    have hhi := Real.log_le_log hpos hx.2
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · calc
        -L = -‖Real.log ε‖ - ‖Real.log M₀‖ := by dsimp [L]; ring
        _ ≤ -‖Real.log ε‖ := by linarith [norm_nonneg (Real.log M₀)]
        _ ≤ Real.log ε := neg_abs_le _
        _ ≤ Real.log (rawMehlerAverage f s x) := hlo
    · calc
        Real.log (rawMehlerAverage f s x) ≤ Real.log M₀ := hhi
        _ ≤ ‖Real.log M₀‖ := le_abs_self _
        _ ≤ L := by
          dsimp [L]
          exact le_add_of_nonneg_left (abs_nonneg (Real.log ε))
  have hlogplus_bound : ∀ (s : ℝ) (hs : 0 ≤ s) (x : ℝ),
      ‖Real.log (rawMehlerAverage f s x) + 1‖ ≤ L + 1 := by
    intro s hs x
    calc
      ‖Real.log (rawMehlerAverage f s x) + 1‖
          ≤ ‖Real.log (rawMehlerAverage f s x)‖ + ‖(1 : ℝ)‖ := norm_add_le _ _
      _ ≤ L + 1 := add_le_add (hlog_bound s hs x) (by norm_num)
  let P : ℝ → ℝ := fun x => rawMehlerAverage f t x
  let F : ℝ → ℝ → ℝ := fun s x =>
    rawMehlerAverage f s x *
      Real.log (rawMehlerAverage f s x)
  let G : ℝ → ℝ → ℝ := fun s x =>
    (deriv (deriv (fun z => rawMehlerAverage f s z)) x -
      x * deriv (fun z => rawMehlerAverage f s z) x) *
      (Real.log (rawMehlerAverage f s x) + 1)
  let J : ℝ → ℝ := fun s => ∫ x, F s x ∂γ
  have hreg_t := rawMehlerAverage_spatial_regular hf hf_bound
    M₁ M₂ hderiv_bounded hsecond_bounded t (le_of_lt ht)
  have hP_C2 : ContDiff ℝ 2 P := hreg_t.1
  have hP'_bound : ∀ x, ‖deriv P x‖ ≤ M₁ := hreg_t.2.1
  have hP''_bound : ∀ x, ‖deriv (deriv P) x‖ ≤ M₂ := hreg_t.2.2
  have hP_bounds_t : ∀ x, ε ≤ P x ∧ P x ≤ M₀ := by
    intro x
    exact hP_bounds t (le_of_lt ht) x
  have hP_nonzero : ∀ x, P x ≠ 0 := fun x => ne_of_gt
    (lt_of_lt_of_le hε (hP_bounds_t x).1)
  let hP₁ : ContDiff ℝ 1 P := hP_C2.of_le (by norm_num)
  have hlogP : ContDiff ℝ 1 (fun x => Real.log (P x)) := hP₁.log hP_nonzero
  have hF_t_meas : Measurable (F t) := by
    exact (hP_C2.continuous.mul hlogP.continuous).measurable
  have hF_t_integrable : Integrable (F t) γ := by
    have hF_bound : ∀ x, ‖F t x‖ ≤ M₀ * L := by
      intro x
      change ‖P x * Real.log (P x)‖ ≤ M₀ * L
      rw [norm_mul]
      have hnormP : ‖P x‖ ≤ M₀ := by
        rw [Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le hε (hP_bounds_t x).1)]
        exact (hP_bounds_t x).2
      have hlogPbound : ‖Real.log (P x)‖ ≤ L := by
        simpa [P] using hlog_bound t (le_of_lt ht) x
      exact mul_le_mul hnormP hlogPbound (norm_nonneg _) hM₀_nonneg
    exact integrable_of_measurable_norm_le hF_t_meas hF_bound
  have hG_t_cont : Continuous (G t) := by
    have hsecond_cont : Continuous (deriv (deriv P)) :=
      hP_C2.deriv'.continuous_deriv_one
    have hfirst_cont : Continuous (deriv P) := hP₁.continuous_deriv_one
    have hlogplus_cont : Continuous (fun x => Real.log (P x) + 1) :=
      hlogP.continuous.add continuous_const
    convert (hsecond_cont.sub (continuous_id.mul hfirst_cont)).mul hlogplus_cont using 1
    funext x
    rfl
  have hG_t_meas : AEStronglyMeasurable (G t) γ := hG_t_cont.measurable.aestronglyMeasurable
  have hIdγ : Integrable (id : ℝ → ℝ) γ := by
    have hIBPconst := LOOConcentration.standardGaussian_integral_deriv_eq_mul_of_bounded
      (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => (1 : ℝ)))
      ⟨1, fun _ => by norm_num⟩ ⟨0, fun _ => by simp⟩
    change Integrable (fun x : ℝ => x) LOOConcentration.standardGaussianIBPMeasure
    simpa using hIBPconst.2.1
  have habsIdγ : Integrable (fun x : ℝ => |x|) γ := by
    simpa only [Real.norm_eq_abs, id_eq] using hIdγ.norm
  let bound : ℝ → ℝ := fun x => (M₂ + |x| * M₁) * (L + 1)
  have hbound_integrable : Integrable bound γ := by
    have hinner : Integrable (fun x : ℝ => M₂ + |x| * M₁) γ :=
      (integrable_const M₂).add (habsIdγ.mul_const M₁)
    exact hinner.const_mul (L + 1) |>.congr
      (ae_of_all γ fun x => by dsimp [bound]; ring)
  have hbound : ∀ᵐ x ∂γ, ∀ s ∈ (Set.Ioi 0 : Set ℝ), ‖G s x‖ ≤ bound x := by
    filter_upwards [] with x s hs
    have hreg := rawMehlerAverage_spatial_regular hf hf_bound
      M₁ M₂ hderiv_bounded hsecond_bounded s (le_of_lt hs)
    have hfirst_bound : ‖deriv
        (fun z => rawMehlerAverage f s z) x‖ ≤ M₁ := by
      exact hreg.2.1 x
    have hsecond_bound : ‖deriv (deriv
        (fun z => rawMehlerAverage f s z)) x‖ ≤ M₂ := by
      exact hreg.2.2 x
    have hgen_bound : ‖deriv (deriv
        (fun z => rawMehlerAverage f s z)) x -
        x * deriv (fun z => rawMehlerAverage f s z) x‖ ≤
          M₂ + |x| * M₁ := by
      calc
        _ ≤ ‖deriv (deriv
          (fun z => rawMehlerAverage f s z)) x‖ +
            ‖x * deriv (fun z => rawMehlerAverage f s z) x‖ := norm_sub_le _ _
        _ ≤ M₂ + |x| * M₁ := by
          calc
            ‖deriv (deriv
                (fun z => rawMehlerAverage f s z)) x‖ +
              ‖x * deriv (fun z => rawMehlerAverage f s z) x‖
                = ‖deriv (deriv
                    (fun z => rawMehlerAverage f s z)) x‖ +
                  |x| * ‖deriv (fun z => rawMehlerAverage f s z) x‖ := by
                    rw [norm_mul, show ‖x‖ = |x| by exact Real.norm_eq_abs x]
            _ ≤ M₂ + |x| * M₁ := add_le_add hsecond_bound
              (mul_le_mul_of_nonneg_left hfirst_bound (abs_nonneg x))
    have hlogplus := hlogplus_bound s (le_of_lt hs) x
    dsimp [G, bound]
    rw [abs_mul]
    have hgen_abs : abs ((deriv (deriv
        (fun z => rawMehlerAverage f s z)) x -
        x * deriv (fun z => rawMehlerAverage f s z) x)) ≤
        M₂ + |x| * M₁ := by simpa only [Real.norm_eq_abs] using hgen_bound
    have hlog_abs : abs (Real.log (rawMehlerAverage f s x) + 1) ≤ L + 1 :=
      by simpa only [Real.norm_eq_abs] using hlogplus
    exact mul_le_mul hgen_abs hlog_abs
      (abs_nonneg (Real.log (rawMehlerAverage f s x) + 1))
      (by positivity)
  have hpoint : ∀ᵐ x ∂γ, ∀ s ∈ (Set.Ioi 0 : Set ℝ),
      HasDerivAt (F · x) (G s x) s := by
    filter_upwards [] with x s hs
    let Ps : ℝ → ℝ := fun z => rawMehlerAverage f s z
    have htimeWithin :=
      LOOConcentration.Examples.GaussianMehlerCalculus.standardGaussianMehler_integral_hasDerivAt_of_pos
        hf hf_bound ⟨M₁, hderiv_bounded⟩ ⟨M₂, hsecond_bounded⟩ x hs
    have htime := htimeWithin.hasDerivAt (Ioi_mem_nhds hs)
    have hspatial1 :=
      LOOConcentration.Examples.GaussianMehlerCalculus.standardGaussianMehlerAverage_hasDerivAt
        (hf.of_le (by norm_num)) hf_meas hf_bound ⟨M₁, hderiv_bounded⟩
        s (le_of_lt hs) x
    have hspatial2 :=
      LOOConcentration.Examples.GaussianMehlerCalculus.standardGaussianMehlerAverage_secondSpatial_hasDerivAt
        hf hf_bound ⟨M₁, hderiv_bounded⟩ ⟨M₂, hsecond_bounded⟩ s (le_of_lt hs) x
    have hspatial1' : HasDerivAt Ps
        (Real.exp (-s) * ∫ y, deriv f
          (Real.exp (-s) * x + Real.sqrt (1 - Real.exp (-2 * s)) * y) ∂γ) x := by
      simpa [Ps, rawMehlerAverage, γ,
        LOOConcentration.standardGaussianIBPMeasure,
        LOOConcentration.Examples.GaussianMehlerCalculus.standardGaussianMehlerAverage] using hspatial1
    have hspatial2' : HasDerivAt (deriv Ps)
        (Real.exp (-s) ^ 2 * ∫ y, deriv (deriv f)
          (Real.exp (-s) * x + Real.sqrt (1 - Real.exp (-2 * s)) * y) ∂γ) x := by
      simpa [Ps, rawMehlerAverage, γ,
        LOOConcentration.standardGaussianIBPMeasure,
        LOOConcentration.Examples.GaussianMehlerCalculus.standardGaussianMehlerAverage] using hspatial2
    have hgen_eq :
        Real.exp (-s) ^ 2 * ∫ y, deriv (deriv f)
          (Real.exp (-s) * x + Real.sqrt (1 - Real.exp (-2 * s)) * y) ∂γ -
          x * (Real.exp (-s) * ∫ y, deriv f
            (Real.exp (-s) * x + Real.sqrt (1 - Real.exp (-2 * s)) * y) ∂γ) =
        deriv (deriv Ps) x - x * deriv Ps x := by
      rw [← hspatial2'.deriv, ← hspatial1'.deriv]
    have htime' := htime.congr_deriv hgen_eq
    have hpos : 0 < Ps x := by
      have hb := hP_bounds s (le_of_lt hs) x
      simpa [Ps] using lt_of_lt_of_le hε hb.1
    have hproduct := htime'.mul (htime'.log (ne_of_gt hpos))
    have hcoef :
        (deriv (deriv Ps) x - x * deriv Ps x) * Real.log (Ps x) +
          Ps x * ((deriv (deriv Ps) x - x * deriv Ps x) / Ps x) =
        (deriv (deriv Ps) x - x * deriv Ps x) * (Real.log (Ps x) + 1) := by
      field_simp [ne_of_gt hpos]
    have hresult := hproduct.congr_deriv hcoef
    have hresult' : HasDerivAt
        (fun r : ℝ => rawMehlerAverage f r x *
          Real.log (rawMehlerAverage f r x))
        ((deriv (deriv Ps) x - x * deriv Ps x) *
          (Real.log (Ps x) + 1)) s := by
      convert hresult using 1 <;> rfl
    change HasDerivAt
      (fun r : ℝ => rawMehlerAverage f r x *
        Real.log (rawMehlerAverage f r x))
      ((deriv (deriv Ps) x - x * deriv Ps x) *
        (Real.log (Ps x) + 1)) s
    simpa [Ps] using hresult'
  have hparam := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Set.Ioi 0) (x₀ := t) (F := F) (F' := G)
    (Ioi_mem_nhds ht) (by
      filter_upwards [eventually_gt_nhds ht] with s hs
      let Ps : ℝ → ℝ := fun x => rawMehlerAverage f s x
      have hreg := rawMehlerAverage_spatial_regular hf hf_bound
        M₁ M₂ hderiv_bounded hsecond_bounded s (le_of_lt hs)
      have hPs : ContDiff ℝ 2 Ps := by
        simpa [Ps] using hreg.1
      have hPs_nonzero : ∀ x, Ps x ≠ 0 := fun x => ne_of_gt
        (lt_of_lt_of_le hε (by simpa [Ps] using (hP_bounds s (le_of_lt hs) x).1))
      have hlogPs : ContDiff ℝ 1 (fun x => Real.log (Ps x)) :=
        (hPs.of_le (by norm_num)).log hPs_nonzero
      exact ((hPs.continuous.mul hlogPs.continuous).measurable).aestronglyMeasurable)
    hF_t_integrable hG_t_meas hbound hbound_integrable hpoint
  have hIBP := standardGaussian_boundedPositive_generator_entropy_dissipation
    hP_C2 ε M₀ hε hP_bounds_t ⟨M₁, hP'_bound⟩ ⟨M₂, hP''_bound⟩
  have hJ_deriv : HasDerivAt J
      (-(∫ x, (deriv P x) ^ 2 / P x ∂γ)) t := by
    have hderiv_eq : (∫ x, G t x ∂γ) =
        -(∫ x, (deriv P x) ^ 2 / P x ∂γ) := by
      simpa [G, P] using hIBP.2.2
    simpa [J, F] using hparam.2.congr_deriv hderiv_eq
  let m : ℝ := ∫ x, f x ∂γ
  have hmean : ∀ {s : ℝ}, 0 < s →
      (∫ x, rawMehlerAverage f s x ∂γ) = m := by
    intro s hs
    have hstationary := LOOConcentration.integral_standardGaussianMehlerAverage_eq
      hf_meas hf_bound s (le_of_lt hs)
    calc
      (∫ x, rawMehlerAverage f s x ∂γ) =
          ∫ x, LOOConcentration.standardGaussianMehlerAverage f hf_meas hf_bound s
            (le_of_lt hs) x ∂LOOConcentration.standardGaussianMehler := by
              simpa [γ, LOOConcentration.standardGaussianIBPMeasure,
                LOOConcentration.standardGaussianMehler] using
                (integral_congr_ae (ae_of_all γ fun x => hbridge s (le_of_lt hs) x))
      _ = ∫ x, f x ∂γ := by
            simpa [γ, LOOConcentration.standardGaussianIBPMeasure,
              LOOConcentration.standardGaussianMehler] using hstationary
      _ = m := by rfl
  have hEntropy_local : rawMehlerEntropy f =ᶠ[𝓝 t]
      (fun s => J s - m * Real.log m) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    have hmean_s := hmean hs
    change (∫ x, rawMehlerAverage f s x *
        Real.log (rawMehlerAverage f s x) ∂γ) -
      (∫ x, rawMehlerAverage f s x ∂γ) *
        Real.log (∫ x, rawMehlerAverage f s x ∂γ) =
      J s - m * Real.log m
    rw [hmean_s]
  have hresult := (hJ_deriv.sub_const (m * Real.log m)).congr_of_eventuallyEq
    hEntropy_local
  simpa [P] using hresult

/-- Any real-time trajectory that agrees with the canonical bounded-positive
Mehler entropy at every positive time has the exact positive-time entropy
dissipation derivative. The representation equality is the only trajectory
condition; the derivative is established by the internal analytic proof. -/
theorem standardGaussianMehler_entropy_dissipation_hasDerivAt
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (M₀ M₁ M₂ ε : ℝ)
    (hbounded : ∀ x, ‖f x‖ ≤ M₀)
    (hderiv_bounded : ∀ x, ‖deriv f x‖ ≤ M₁)
    (hsecond_bounded : ∀ x, ‖deriv (deriv f) x‖ ≤ M₂)
    (hε : 0 < ε) (hlower : ∀ x, ε ≤ f x)
    {t : ℝ} (ht : 0 < t) (ψ : ℝ → ℝ)
    (hψ : ∀ s (hs : 0 < s),
      ψ s = standardGaussianMehlerEntropy f hf.continuous.measurable
        M₀ ε hbounded hε hlower s (le_of_lt hs)) :
    HasDerivAt ψ
      (-(∫ x,
        (deriv (LOOConcentration.standardGaussianMehlerAverage f hf.continuous.measurable
          ⟨M₀, hbounded⟩ t (le_of_lt ht)) x) ^ 2 /
        LOOConcentration.standardGaussianMehlerAverage f hf.continuous.measurable
          ⟨M₀, hbounded⟩ t (le_of_lt ht) x ∂γ)) t := by
  have hraw := rawMehlerEntropy_hasDerivAt hf M₀ M₁ M₂ ε hbounded
    hderiv_bounded hsecond_bounded hε hlower ht
  let P : ℝ → ℝ := LOOConcentration.standardGaussianMehlerAverage f
    hf.continuous.measurable ⟨M₀, hbounded⟩ t (le_of_lt ht)
  have hpoint : ∀ x, rawMehlerAverage f t x = P x := by
    intro x
    exact rawMehlerAverage_eq_source f hf.continuous.measurable
      ⟨M₀, hbounded⟩ t (le_of_lt ht) x
  have hfun : (fun x => rawMehlerAverage f t x) = P := funext hpoint
  have hderiv : ∀ x,
      deriv (fun z => rawMehlerAverage f t z) x = deriv P x := by
    intro x
    exact congrArg (fun g : ℝ → ℝ => deriv g x) hfun
  have henergy :
      (∫ x, (deriv (fun z => rawMehlerAverage f t z) x) ^ 2 /
        rawMehlerAverage f t x ∂γ) =
      ∫ x, (deriv P x) ^ 2 / P x ∂γ := by
    apply integral_congr_ae
    filter_upwards [] with x
    rw [hderiv x, hpoint x]
  have hraw_canonical : HasDerivAt (fun s => rawMehlerEntropy f s)
      (-(∫ x, (deriv P x) ^ 2 / P x ∂γ)) t := by
    convert hraw using 1
    rw [henergy]
  have hlocal : ψ =ᶠ[𝓝 t] (fun s => rawMehlerEntropy f s) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    calc
      ψ s = standardGaussianMehlerEntropy f hf.continuous.measurable
          M₀ ε hbounded hε hlower s (le_of_lt hs) := hψ s hs
      _ = rawMehlerEntropy f s :=
        (rawMehlerEntropy_eq_standardGaussianMehlerEntropy f
          hf.continuous.measurable M₀ ε hbounded hε hlower s (le_of_lt hs)).symm
  have hresult := hraw_canonical.congr_of_eventuallyEq hlocal
  simpa [P] using hresult

#print axioms standardGaussianMehlerAverage_spatial_regular
#print axioms standardGaussianMehlerEntropy_facts
#print axioms standardGaussian_boundedPositive_generator_entropy_dissipation
#print axioms standardGaussianMehler_entropy_dissipation_hasDerivAt

end LOOConcentration.Examples.GaussianMehlerEntropy
