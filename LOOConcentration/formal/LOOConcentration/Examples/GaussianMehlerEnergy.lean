import LOOConcentration.Examples.GaussianMehler
import LOOConcentration.Examples.GaussianMehlerCalculus
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
# Weighted gradient estimates for the scalar Gaussian Mehler kernel

This module proves the weighted Cauchy--Schwarz estimate on the reviewed
standard Gaussian Mehler average.  The spatial derivative and integrated
decay consequences are kept separate from the still-audited calculus module.
-/

set_option autoImplicit false

namespace LOOConcentration

open MeasureTheory
open Filter
open scoped Topology

/-- Bounded positive functions satisfy the weighted integral
Cauchy--Schwarz inequality.  The proof uses the actual factors
`sqrt f` and `g / sqrt f`; boundedness supplies their `L²` admissions. -/
theorem integral_weighted_cauchy_schwarz
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {f g : α → ℝ} (hf : Measurable f) (hg : Measurable g)
    {ε B G : ℝ} (hε : 0 < ε)
    (hflower : ∀ x, ε ≤ f x) (hfupper : ∀ x, f x ≤ B)
    (hgbound : ∀ x, |g x| ≤ G) :
    (∫ x, g x ∂μ) ^ 2 ≤
      (∫ x, f x ∂μ) * (∫ x, g x ^ 2 / f x ∂μ) := by
  have huniv : (Set.univ : Set α) ≠ ∅ := by
    intro hempty
    have hzero : μ Set.univ = 0 := by rw [hempty]; simp
    rw [measure_univ] at hzero
    norm_num at hzero
  obtain ⟨x₀, _⟩ := Set.nonempty_iff_ne_empty.mpr huniv
  have hGnonneg : 0 ≤ G := le_trans (abs_nonneg (g x₀)) (hgbound x₀)
  have hfpos : ∀ x, 0 < f x := fun x => lt_of_lt_of_le hε (hflower x)
  let a : α → ℝ := fun x => Real.sqrt (f x)
  let b : α → ℝ := fun x => g x / Real.sqrt (f x)
  have ha_meas : Measurable a := Real.continuous_sqrt.measurable.comp hf
  have hb_meas : Measurable b := hg.div ha_meas
  have ha_bound : ∀ x, ‖a x‖ ≤ Real.sqrt B := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt (hfupper x)
  have hsqrtε : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hb_bound : ∀ x, ‖b x‖ ≤ G / Real.sqrt ε := by
    intro x
    have hsqrtfx : 0 < Real.sqrt (f x) := Real.sqrt_pos.2 (hfpos x)
    have hlow : Real.sqrt ε ≤ Real.sqrt (f x) := Real.sqrt_le_sqrt (hflower x)
    have hquot : |g x / Real.sqrt (f x)| ≤ G / Real.sqrt ε := by
      rw [abs_div, abs_of_pos hsqrtfx]
      rw [div_le_div_iff₀ hsqrtfx hsqrtε]
      have h₁ := mul_le_mul_of_nonneg_right (hgbound x) hsqrtε.le
      have h₂ := mul_le_mul_of_nonneg_left hlow hGnonneg
      nlinarith
    rw [Real.norm_eq_abs]
    exact hquot
  have ha_mem : MemLp a (ENNReal.ofReal (2 : ℝ)) μ :=
    MemLp.of_bound ha_meas.aestronglyMeasurable (Real.sqrt B)
      (ae_of_all μ fun x => ha_bound x)
  have hb_mem : MemLp b (ENNReal.ofReal (2 : ℝ)) μ :=
    MemLp.of_bound hb_meas.aestronglyMeasurable (G / Real.sqrt ε)
      (ae_of_all μ fun x => hb_bound x)
  have hprod : ∀ x, a x * b x = g x := by
    intro x
    dsimp [a, b]
    have hs : Real.sqrt (f x) ≠ 0 := (ne_of_gt (Real.sqrt_pos.2 (hfpos x)))
    field_simp
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    (μ := μ) (p := 2) (q := 2) Real.HolderConjugate.two_two ha_mem hb_mem
  have hnormprod : ∀ x, ‖a x‖ * ‖b x‖ = |g x| := by
    intro x
    calc
      ‖a x‖ * ‖b x‖ = ‖a x * b x‖ := (norm_mul _ _).symm
      _ = |g x| := by rw [hprod x, Real.norm_eq_abs]
  have hAint : (∫ x, ‖a x‖ ^ (2 : ℝ) ∂μ) = ∫ x, f x ∂μ := by
    apply integral_congr_ae
    exact ae_of_all μ fun x => by
      change ‖Real.sqrt (f x)‖ ^ (2 : ℝ) = f x
      rw [Real.rpow_ofNat]
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sq_sqrt (le_trans hε.le (hflower x))
  have hBint : (∫ x, ‖b x‖ ^ (2 : ℝ) ∂μ) = ∫ x, g x ^ 2 / f x ∂μ := by
    apply integral_congr_ae
    exact ae_of_all μ fun x => by
      change ‖g x / Real.sqrt (f x)‖ ^ (2 : ℝ) = g x ^ 2 / f x
      rw [Real.rpow_ofNat]
      rw [Real.norm_eq_abs, sq_abs, div_pow,
        Real.sq_sqrt (le_trans hε.le (hflower x))]
  have hholder' :
      (∫ x, |g x| ∂μ) ≤
        (∫ x, f x ∂μ) ^ (1 / 2 : ℝ) *
          (∫ x, g x ^ 2 / f x ∂μ) ^ (1 / 2 : ℝ) := by
    calc
      (∫ x, |g x| ∂μ) = ∫ x, ‖a x‖ * ‖b x‖ ∂μ := by
        symm
        exact integral_congr_ae (ae_of_all μ hnormprod)
      _ ≤ (∫ x, ‖a x‖ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) *
          (∫ x, ‖b x‖ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := hholder
      _ = (∫ x, f x ∂μ) ^ (1 / 2 : ℝ) *
          (∫ x, g x ^ 2 / f x ∂μ) ^ (1 / 2 : ℝ) := by
        rw [hAint, hBint]
  have hq_nonneg : 0 ≤ ∫ x, g x ^ 2 / f x ∂μ := by
    apply integral_nonneg_of_ae
    exact ae_of_all μ fun x => div_nonneg (sq_nonneg _) (le_of_lt (hfpos x))
  have hI_nonneg : 0 ≤ ∫ x, f x ∂μ := integral_nonneg_of_ae
    (ae_of_all μ fun x => le_of_lt (hfpos x))
  have hroot : |∫ x, g x ∂μ| ≤
      Real.sqrt (∫ x, f x ∂μ) * Real.sqrt (∫ x, g x ^ 2 / f x ∂μ) := by
    calc
      |∫ x, g x ∂μ| ≤ ∫ x, |g x| ∂μ := abs_integral_le_integral_abs
      _ ≤ Real.sqrt (∫ x, f x ∂μ) *
          Real.sqrt (∫ x, g x ^ 2 / f x ∂μ) := by
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
        exact hholder'
  have hsquare := mul_self_le_mul_self (abs_nonneg _) hroot
  calc
    (∫ x, g x ∂μ) ^ 2 = |∫ x, g x ∂μ| ^ 2 := (sq_abs _).symm
    _ ≤ (Real.sqrt (∫ x, f x ∂μ) *
        Real.sqrt (∫ x, g x ^ 2 / f x ∂μ)) ^ 2 := by
      simpa only [pow_two] using hsquare
    _ = (∫ x, f x ∂μ) * (∫ x, g x ^ 2 / f x ∂μ) := by
      rw [mul_pow, Real.sq_sqrt hI_nonneg, Real.sq_sqrt hq_nonneg]

/-- The actual standard Gaussian Mehler average preserves the weighted
Cauchy--Schwarz estimate for bounded positive inputs. -/
theorem standardGaussianMehlerAverage_weighted_cauchy_schwarz
    {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    {ε B G : ℝ} (hε : 0 < ε)
    (hflower : ∀ y, ε ≤ f y) (hfupper : ∀ y, f y ≤ B)
    (hgbound : ∀ y, |g y| ≤ G)
    (t : ℝ) (ht : 0 ≤ t) (x : ℝ) :
    (standardGaussianMehlerAverage g hg ⟨G, fun y => by
        simpa [Real.norm_eq_abs] using hgbound y⟩ t ht x) ^ 2 /
      standardGaussianMehlerAverage f hf ⟨B, fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_trans hε.le (hflower y))]
        exact hfupper y⟩ t ht x ≤
      standardGaussianMehlerAverage (fun y => g y ^ 2 / f y)
        (by fun_prop) ⟨G ^ 2 / ε, fun y => by
          have hfy : 0 < f y := lt_of_lt_of_le hε (hflower y)
          have hnum : g y ^ 2 ≤ G ^ 2 := by
            have h : |g y| ^ 2 ≤ G ^ 2 := by
              simpa only [pow_two] using
                (mul_self_le_mul_self (abs_nonneg (g y)) (hgbound y))
            calc
              g y ^ 2 = |g y| ^ 2 := (sq_abs _).symm
              _ ≤ G ^ 2 := h
          have hquot : g y ^ 2 / f y ≤ G ^ 2 / ε := by
            rw [div_le_div_iff₀ hfy hε]
            calc
              g y ^ 2 * ε ≤ G ^ 2 * ε := mul_le_mul_of_nonneg_right hnum hε.le
              _ ≤ G ^ 2 * f y := mul_le_mul_of_nonneg_left (hflower y) (sq_nonneg G)
          rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) hfy.le)]
          exact hquot⟩ t ht x := by
  let hfb : ∀ y, ‖f y‖ ≤ B := fun y => by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_trans hε.le (hflower y))]
    exact hfupper y
  let hgb : ∀ y, ‖g y‖ ≤ G := fun y => by
    simpa [Real.norm_eq_abs] using hgbound y
  let he : ℝ → ℝ := fun y => g y ^ 2 / f y
  let heb : ∀ y, ‖he y‖ ≤ G ^ 2 / ε := by
    intro y
    have hfy : 0 < f y := lt_of_lt_of_le hε (hflower y)
    have hnum : g y ^ 2 ≤ G ^ 2 := by
      have h : |g y| ^ 2 ≤ G ^ 2 := by
        simpa only [pow_two] using
          (mul_self_le_mul_self (abs_nonneg (g y)) (hgbound y))
      calc
        g y ^ 2 = |g y| ^ 2 := (sq_abs _).symm
        _ ≤ G ^ 2 := h
    have hquot : g y ^ 2 / f y ≤ G ^ 2 / ε := by
      rw [div_le_div_iff₀ hfy hε]
      calc
        g y ^ 2 * ε ≤ G ^ 2 * ε := mul_le_mul_of_nonneg_right hnum hε.le
        _ ≤ G ^ 2 * f y := mul_le_mul_of_nonneg_left (hflower y) (sq_nonneg G)
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) hfy.le)]
    exact hquot
  have he_meas : Measurable he := by
    dsimp [he]
    fun_prop
  have hdenpos : 0 < standardGaussianMehlerAverage f hf ⟨B, hfb⟩ t ht x := by
    have := standardGaussianMehlerAverage_lower_bound hf hfb hflower t ht x
    exact lt_of_lt_of_le hε this
  have hcross := integral_weighted_cauchy_schwarz
    (μ := standardGaussianMehler) (f := fun y => f (standardGaussianMehlerArgument t x y))
    (g := fun y => g (standardGaussianMehlerArgument t x y))
    (hf.comp (by fun_prop)) (hg.comp (by fun_prop)) hε
    (fun y => hflower _) (fun y => hfupper _) (fun y => hgbound _)
  have hcross' :
      (standardGaussianMehlerAverage g hg ⟨G, hgb⟩ t ht x) ^ 2 ≤
        standardGaussianMehlerAverage f hf ⟨B, hfb⟩ t ht x *
          standardGaussianMehlerAverage he he_meas ⟨G ^ 2 / ε, heb⟩ t ht x := by
    simpa [standardGaussianMehlerAverage, he, standardGaussianMehlerArgument,
      standardGaussianMehlerDrift, standardGaussianMehlerNoise] using hcross
  exact (div_le_iff₀ hdenpos).2 (by simpa [mul_comm] using hcross')

/-- Transfer the audited local-calculus spatial derivative to the canonical
standard Gaussian Mehler average using the reviewed operator equality. -/
theorem standardGaussianMehlerAverage_hasDerivAt_of_bounded
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hfmeas : Measurable f)
    (hfb : ∃ B : ℝ, ∀ y, ‖f y‖ ≤ B)
    (hdb : ∃ D : ℝ, ∀ y, ‖deriv f y‖ ≤ D)
    (t : ℝ) (ht : 0 ≤ t) (x : ℝ) :
    HasDerivAt (fun z => standardGaussianMehlerAverage f hfmeas hfb t ht z)
      (Real.exp (-t) * standardGaussianMehlerAverage (deriv f)
        hf.continuous_deriv_one.measurable hdb t ht x) x := by
  have hcalc := Examples.GaussianMehlerCalculus.standardGaussianMehlerAverage_hasDerivAt
    hf hfmeas hfb hdb t ht x
  have hfun : (fun z => standardGaussianMehlerAverage f hfmeas hfb t ht z) =ᶠ[𝓝 x]
      (fun z => Examples.GaussianMehlerCalculus.standardGaussianMehlerAverage
        f hfmeas hfb t ht z) := by
    apply Filter.Eventually.of_forall
    intro z
    exact (Examples.GaussianMehlerCalculus.standardGaussianMehlerAverage_eq_source
      f hfmeas hfb t ht z).symm
  have hsourceAt := hcalc.congr_of_eventuallyEq hfun.symm
  have hrhs : Real.exp (-t) * ∫ y, deriv f
          (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y)
            ∂Examples.GaussianMehlerCalculus.γ =
      Real.exp (-t) * Examples.GaussianMehlerCalculus.standardGaussianMehlerAverage
          (deriv f) hf.continuous_deriv_one.measurable hdb t ht x := rfl
  have hrhs' : Real.exp (-t) * Examples.GaussianMehlerCalculus.standardGaussianMehlerAverage
          (deriv f) hf.continuous_deriv_one.measurable hdb t ht x =
      Real.exp (-t) * standardGaussianMehlerAverage (deriv f)
          hf.continuous_deriv_one.measurable hdb t ht x := by
    rw [Examples.GaussianMehlerCalculus.standardGaussianMehlerAverage_eq_source]
  exact hsourceAt.congr_deriv (hrhs.trans hrhs')

/-- The reviewed actual spatial derivative of the scalar Mehler average
turns weighted Cauchy--Schwarz into the pointwise `exp(-2t)` gradient bound.
The derivative provider is the audited
`GaussianMehlerCalculus.standardGaussianMehlerAverage_hasDerivAt`; its local
operator is identified with the canonical source operator by the reviewed
`standardGaussianMehlerAverage_eq_source` bridge. -/
theorem standardGaussianMehlerAverage_deriv_weighted_bound
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    {ε B D : ℝ} (hε : 0 < ε)
    (hflower : ∀ y, ε ≤ f y) (hfupper : ∀ y, f y ≤ B)
    (hderiv_bound : ∀ y, ‖deriv f y‖ ≤ D)
    (t : ℝ) (ht : 0 ≤ t) (x : ℝ) :
    (deriv (fun z => standardGaussianMehlerAverage f hf.continuous.measurable
      ⟨B, fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_trans hε.le (hflower y))]
        exact hfupper y⟩ t ht z) x) ^ 2 /
      standardGaussianMehlerAverage f hf.continuous.measurable
        ⟨B, fun y => by
          rw [Real.norm_eq_abs, abs_of_nonneg (le_trans hε.le (hflower y))]
          exact hfupper y⟩ t ht x ≤
      Real.exp (-2 * t) *
        standardGaussianMehlerAverage (fun y => (deriv f y) ^ 2 / f y)
          (by
            let g : ℝ → ℝ := deriv f
            have hg : Measurable g := hf.continuous_deriv_one.measurable
            have hmf : Measurable f := hf.continuous.measurable
            change Measurable (fun y => g y ^ 2 / f y)
            fun_prop)
          ⟨D ^ 2 / ε, fun y => by
            have hfy : 0 < f y := lt_of_lt_of_le hε (hflower y)
            have hnum : (deriv f y) ^ 2 ≤ D ^ 2 := by
              have h := (hderiv_bound y)
              rw [Real.norm_eq_abs] at h
              have habs : |deriv f y| ≤ D := h
              have hsq : |deriv f y| ^ 2 ≤ D ^ 2 := by
                simpa only [pow_two] using
                  (mul_self_le_mul_self (abs_nonneg _) habs)
              calc
                (deriv f y) ^ 2 = |deriv f y| ^ 2 := (sq_abs _).symm
                _ ≤ D ^ 2 := hsq
            have hquot : (deriv f y) ^ 2 / f y ≤ D ^ 2 / ε := by
              rw [div_le_div_iff₀ hfy hε]
              calc
                (deriv f y) ^ 2 * ε ≤ D ^ 2 * ε :=
                  mul_le_mul_of_nonneg_right hnum hε.le
                _ ≤ D ^ 2 * f y :=
                  mul_le_mul_of_nonneg_left (hflower y) (sq_nonneg D)
            rw [Real.norm_eq_abs,
              abs_of_nonneg (div_nonneg (sq_nonneg _) hfy.le)]
            exact hquot⟩ t ht x := by
  let hfb : ∀ y, ‖f y‖ ≤ B := fun y => by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_trans hε.le (hflower y))]
    exact hfupper y
  let hdb : ∀ y, ‖deriv f y‖ ≤ D := hderiv_bound
  let hdf : Measurable (deriv f) := hf.continuous_deriv_one.measurable
  let hda : ∀ y, |deriv f y| ≤ D := fun y => by
    simpa [Real.norm_eq_abs] using hderiv_bound y
  let A : ℝ → ℝ := standardGaussianMehlerAverage f
    hf.continuous.measurable ⟨B, hfb⟩ t ht
  let A' : ℝ → ℝ := standardGaussianMehlerAverage (deriv f)
    hdf ⟨D, hdb⟩ t ht
  have hspatial : deriv A x = Real.exp (-t) * A' x :=
    (standardGaussianMehlerAverage_hasDerivAt_of_bounded
      hf hf.continuous.measurable ⟨B, hfb⟩ ⟨D, hdb⟩ t ht x).deriv
  have hbase := standardGaussianMehlerAverage_weighted_cauchy_schwarz
    (f := f) (g := deriv f) hf.continuous.measurable hdf hε hflower hfupper
    hda t ht x
  have hApos : 0 < A x := by
    dsimp [A]
    exact lt_of_lt_of_le hε
      (standardGaussianMehlerAverage_lower_bound hf.continuous.measurable hfb
        hflower t ht x)
  have hexp : Real.exp (-t) ^ 2 = Real.exp (-2 * t) := by
    calc
      Real.exp (-t) ^ 2 = Real.exp (-t) * Real.exp (-t) := by rw [pow_two]
      _ = Real.exp ((-t) + (-t)) := (Real.exp_add _ _).symm
      _ = Real.exp (-2 * t) := by congr 1; ring
  calc
    (deriv A x) ^ 2 / A x =
        (Real.exp (-t) * A' x) ^ 2 / A x := by rw [hspatial]
    _ = Real.exp (-2 * t) * ((A' x) ^ 2 / A x) := by
      rw [mul_pow, hexp]
      field_simp [ne_of_gt hApos]
    _ ≤ Real.exp (-2 * t) *
            standardGaussianMehlerAverage (fun y => (deriv f y) ^ 2 / f y)
          (by
            let g : ℝ → ℝ := deriv f
            have hg : Measurable g := hf.continuous_deriv_one.measurable
            have hmf : Measurable f := hf.continuous.measurable
            change Measurable (fun y => g y ^ 2 / f y)
            fun_prop)
          ⟨D ^ 2 / ε, fun y => by
            have hfy : 0 < f y := lt_of_lt_of_le hε (hflower y)
            have hnum : (deriv f y) ^ 2 ≤ D ^ 2 := by
              have h := hderiv_bound y
              rw [Real.norm_eq_abs] at h
              have hsq : |deriv f y| ^ 2 ≤ D ^ 2 := by
                simpa only [pow_two] using
                  (mul_self_le_mul_self (abs_nonneg _) h)
              calc
                (deriv f y) ^ 2 = |deriv f y| ^ 2 := (sq_abs _).symm
                _ ≤ D ^ 2 := hsq
            have hquot : (deriv f y) ^ 2 / f y ≤ D ^ 2 / ε := by
              rw [div_le_div_iff₀ hfy hε]
              calc
                (deriv f y) ^ 2 * ε ≤ D ^ 2 * ε :=
                  mul_le_mul_of_nonneg_right hnum hε.le
                _ ≤ D ^ 2 * f y :=
                  mul_le_mul_of_nonneg_left (hflower y) (sq_nonneg D)
            rw [Real.norm_eq_abs,
              abs_of_nonneg (div_nonneg (sq_nonneg _) hfy.le)]
            exact hquot⟩ t ht x :=
      mul_le_mul_of_nonneg_left hbase (Real.exp_nonneg _)

/-- Integrate the weighted gradient estimate against the actual stationary
standard Gaussian law.  Both the source quotient `(f')²/f` and the quotient
of the actual spatial derivative are admitted as integrable from their
bounded-positive estimates; neither integrability fact is a premise. -/
theorem standardGaussianMehlerAverage_weighted_energy_decay
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    {ε B D : ℝ} (hε : 0 < ε)
    (hflower : ∀ y, ε ≤ f y) (hfupper : ∀ y, f y ≤ B)
    (hderiv_bound : ∀ y, ‖deriv f y‖ ≤ D)
    (t : ℝ) (ht : 0 ≤ t) :
    let P : ℝ → ℝ := standardGaussianMehlerAverage f
      hf.continuous.measurable ⟨B, fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_trans hε.le (hflower y))]
        exact hfupper y⟩ t ht
    let E : ℝ → ℝ := fun y => (deriv f y) ^ 2 / f y
    Integrable E standardGaussianMehler ∧
      Integrable (fun x => (deriv P x) ^ 2 / P x) standardGaussianMehler ∧
      (∫ x, (deriv P x) ^ 2 / P x ∂standardGaussianMehler) ≤
        Real.exp (-2 * t) * (∫ x, E x ∂standardGaussianMehler) := by
  let hfb : ∀ y, ‖f y‖ ≤ B := fun y => by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_trans hε.le (hflower y))]
    exact hfupper y
  let hdb : ∀ y, ‖deriv f y‖ ≤ D := hderiv_bound
  let hdf : Measurable (deriv f) := hf.continuous_deriv_one.measurable
  let hEmax : ℝ := D ^ 2 / ε
  let E : ℝ → ℝ := fun y => (deriv f y) ^ 2 / f y
  let P : ℝ → ℝ := standardGaussianMehlerAverage f
    hf.continuous.measurable ⟨B, hfb⟩ t ht
  let P' : ℝ → ℝ := standardGaussianMehlerAverage (deriv f)
    hdf ⟨D, hdb⟩ t ht
  have hEmeas : Measurable E := by
    change Measurable (fun y => (deriv f y) ^ 2 / f y)
    let g : ℝ → ℝ := deriv f
    have hg : Measurable g := hf.continuous_deriv_one.measurable
    have hmf : Measurable f := hf.continuous.measurable
    change Measurable (fun y => g y ^ 2 / f y)
    fun_prop
  have hDnonneg : 0 ≤ D := le_trans (norm_nonneg (deriv f 0)) (hderiv_bound 0)
  have hEmax_nonneg : 0 ≤ hEmax := div_nonneg (sq_nonneg D) hε.le
  have hE_nonneg : ∀ y, 0 ≤ E y := fun y =>
    div_nonneg (sq_nonneg _) (le_of_lt (lt_of_lt_of_le hε (hflower y)))
  have hEbound : ∀ y, ‖E y‖ ≤ hEmax := by
    intro y
    have hfy : 0 < f y := lt_of_lt_of_le hε (hflower y)
    have habs : |deriv f y| ≤ D := by
      simpa [Real.norm_eq_abs] using hderiv_bound y
    have hsq : |deriv f y| ^ 2 ≤ D ^ 2 := by
      simpa only [pow_two] using (mul_self_le_mul_self (abs_nonneg _) habs)
    have hnum : (deriv f y) ^ 2 ≤ D ^ 2 := by
      calc
        (deriv f y) ^ 2 = |deriv f y| ^ 2 := (sq_abs _).symm
        _ ≤ D ^ 2 := hsq
    have hquot : (deriv f y) ^ 2 / f y ≤ hEmax := by
      dsimp [hEmax]
      rw [div_le_div_iff₀ hfy hε]
      calc
        (deriv f y) ^ 2 * ε ≤ D ^ 2 * ε :=
          mul_le_mul_of_nonneg_right hnum hε.le
        _ ≤ D ^ 2 * f y := mul_le_mul_of_nonneg_left (hflower y) (sq_nonneg D)
    rw [Real.norm_eq_abs, abs_of_nonneg (hE_nonneg y)]
    exact hquot
  let hEwit : ∃ M : ℝ, ∀ y, ‖E y‖ ≤ M := ⟨hEmax, hEbound⟩
  let PE : ℝ → ℝ := standardGaussianMehlerAverage E hEmeas hEwit t ht
  have hEint : Integrable E standardGaussianMehler := by
    apply Integrable.of_bound hEmeas.aestronglyMeasurable hEmax
    exact ae_of_all standardGaussianMehler hEbound
  have hPmeas : Measurable P :=
    measurable_standardGaussianMehlerAverage hf.continuous.measurable ⟨B, hfb⟩ t ht
  have hP'meas : Measurable P' :=
    measurable_standardGaussianMehlerAverage hdf ⟨D, hdb⟩ t ht
  have hPEmeas : Measurable PE :=
    measurable_standardGaussianMehlerAverage hEmeas hEwit t ht
  have hPpos : ∀ x, 0 < P x := by
    intro x
    dsimp [P]
    exact lt_of_lt_of_le hε
      (standardGaussianMehlerAverage_lower_bound hf.continuous.measurable hfb
        hflower t ht x)
  have hPderiv_eq : (fun x => deriv P x) = fun x => Real.exp (-t) * P' x := by
    funext x
    exact (standardGaussianMehlerAverage_hasDerivAt_of_bounded hf
      hf.continuous.measurable ⟨B, hfb⟩ ⟨D, hdb⟩ t ht x).deriv
  have hPderiv_meas : Measurable (fun x => deriv P x) := by
    rw [hPderiv_eq]
    exact measurable_const.mul hP'meas
  have hQmeas : Measurable (fun x => (deriv P x) ^ 2 / P x) := by
    let d : ℝ → ℝ := fun x => deriv P x
    have hd : Measurable d := hPderiv_meas
    change Measurable (fun x => d x ^ 2 / P x)
    fun_prop
  have hPElower : ∀ x, 0 ≤ PE x := by
    intro x
    dsimp [PE]
    exact standardGaussianMehlerAverage_lower_bound hEmeas hEbound hE_nonneg t ht x
  have hPEupper : ∀ x, PE x ≤ hEmax := by
    intro x
    dsimp [PE]
    exact (standardGaussianMehlerAverage_bounds hEmeas hEbound t ht x).2
  have hPEint : Integrable PE standardGaussianMehler := by
    apply Integrable.of_bound hPEmeas.aestronglyMeasurable hEmax
    exact ae_of_all standardGaussianMehler fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hPElower x)]
      exact hPEupper x
  have hpoint : ∀ x, (deriv P x) ^ 2 / P x ≤ Real.exp (-2 * t) * PE x := by
    intro x
    exact standardGaussianMehlerAverage_deriv_weighted_bound hf hε
      hflower hfupper hderiv_bound t ht x
  have hQnonneg : ∀ x, 0 ≤ (deriv P x) ^ 2 / P x := by
    intro x
    exact div_nonneg (sq_nonneg _) (le_of_lt (hPpos x))
  have hQupper : ∀ x, (deriv P x) ^ 2 / P x ≤ Real.exp (-2 * t) * hEmax := by
    intro x
    exact (hpoint x).trans (mul_le_mul_of_nonneg_left (hPEupper x)
      (Real.exp_nonneg _))
  have hQint : Integrable (fun x => (deriv P x) ^ 2 / P x) standardGaussianMehler := by
    apply Integrable.of_bound hQmeas.aestronglyMeasurable (Real.exp (-2 * t) * hEmax)
    exact ae_of_all standardGaussianMehler fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hQnonneg x)]
      exact hQupper x
  change Integrable E standardGaussianMehler ∧
      Integrable (fun x => (deriv P x) ^ 2 / P x) standardGaussianMehler ∧
      (∫ x, (deriv P x) ^ 2 / P x ∂standardGaussianMehler) ≤
        Real.exp (-2 * t) * (∫ x, E x ∂standardGaussianMehler)
  refine ⟨hEint, hQint, ?_⟩
  calc
    (∫ x, (deriv P x) ^ 2 / P x ∂standardGaussianMehler) ≤
        ∫ x, Real.exp (-2 * t) * PE x ∂standardGaussianMehler :=
      integral_mono hQint (hPEint.const_mul (Real.exp (-2 * t)))
        hpoint
    _ = Real.exp (-2 * t) * (∫ x, E x ∂standardGaussianMehler) := by
      rw [integral_const_mul,
        integral_standardGaussianMehlerAverage_eq hEmeas hEwit t ht]

end LOOConcentration
