import LOOConcentration.Examples.GaussianLipschitzMehlerCalculus
import LOOConcentration.Examples.GaussianMehlerBoundedSmoothing
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic

/-!
# C² regularization of bounded Lipschitz Gaussian Mehler data

The first spatial derivative commutes with the actual Gaussian Mehler average.
The derivative of a Lipschitz input is measurable and bounded, so the bounded
measurable smoothing theorem applies to that derivative and supplies the
second spatial derivative.
-/

set_option autoImplicit false

namespace LOOConcentration

open MeasureTheory
open scoped NNReal Topology

private theorem standardGaussianMehler_noise_pos_wave16 {t : ℝ} (ht : 0 < t) :
    0 < Real.sqrt (1 - Real.exp (-2 * t)) := by
  apply Real.sqrt_pos.2
  have harg : -2 * t < 0 := by nlinarith
  have hexp : Real.exp (-2 * t) < 1 := Real.exp_lt_one_iff.mpr harg
  linarith

/-- The canonical positive-time Gaussian Mehler average of a signed bounded
globally Lipschitz scalar input is C² in space, with global bounds on its value
and first two derivatives. The only regularity hypothesis on the input is its
actual global Lipschitz bound. -/
theorem standardGaussianMehlerAverage_boundedLipschitz_C2
    {u : ℝ → ℝ} {B K : ℝ≥0}
    (hu : LipschitzWith K u)
    (hu_bounded : ∀ x, ‖u x‖ ≤ (B : ℝ))
    {t : ℝ} (ht : 0 < t) :
    let P := standardGaussianMehlerAverage u hu.continuous.measurable
      ⟨(B : ℝ), hu_bounded⟩ t (le_of_lt ht)
    ContDiff ℝ 2 P ∧
      (∀ x, ‖P x‖ ≤ (B : ℝ)) ∧
      (∀ x, ‖deriv P x‖ ≤ Real.exp (-t) * (K : ℝ)) ∧
      (∀ x, ‖deriv (deriv P) x‖ ≤
        (Real.exp (-t) ^ 2 / Real.sqrt (1 - Real.exp (-2 * t))) *
          (K : ℝ) * ∫ y, |y| ∂standardGaussianMehler) := by
  dsimp
  let P : ℝ → ℝ := standardGaussianMehlerAverage u hu.continuous.measurable
    ⟨(B : ℝ), hu_bounded⟩ t (le_of_lt ht)
  let D : ℝ → ℝ := deriv u
  let Kreal : ℝ := (K : ℝ)
  let a : ℝ := Real.exp (-t)
  let b : ℝ := Real.sqrt (1 - Real.exp (-2 * t))
  let Q : ℝ → ℝ := standardGaussianMehlerAverage D (measurable_deriv u)
    ⟨Kreal, by
      intro x
      dsimp [D, Kreal]
      exact norm_deriv_le_of_lipschitz hu⟩ t (le_of_lt ht)
  have ha : 0 < a := by
    dsimp [a]
    exact Real.exp_pos _
  have hb : 0 < b := by
    dsimp [b]
    exact standardGaussianMehler_noise_pos_wave16 ht
  have hKnonneg : 0 ≤ Kreal := by
    dsimp [Kreal]
    exact K.coe_nonneg
  have hDmeas : Measurable D := by
    dsimp [D]
    exact measurable_deriv u
  have hD_bounded (x : ℝ) : ‖D x‖ ≤ Kreal := by
    dsimp [D, Kreal]
    exact norm_deriv_le_of_lipschitz hu
  have hQsmooth :=
    standardGaussianMehlerAverage_boundedMeasurable_C1 hDmeas hD_bounded ht
  have hQ_C1 : ContDiff ℝ 1 Q := by
    simpa [Q] using hQsmooth.1
  have hQ_interval (x : ℝ) : -Kreal ≤ Q x ∧ Q x ≤ Kreal := by
    simpa [Q] using
      (standardGaussianMehlerAverage_bounds hDmeas hD_bounded t (le_of_lt ht) x)
  have hQ_bound (x : ℝ) : ‖Q x‖ ≤ Kreal := by
    rw [Real.norm_eq_abs]
    exact abs_le.mpr (hQ_interval x)
  have hQ_second_bound (x : ℝ) :
      ‖deriv Q x‖ ≤
        (a / b) * Kreal * ∫ y, |y| ∂standardGaussianMehler := by
    simpa [Q, a, b, Kreal] using hQsmooth.2.2 x
  have hQ_integral (x : ℝ) :
      Q x = ∫ y, deriv u (standardGaussianMehlerArgument t x y)
        ∂Examples.GaussianLipschitzMehlerCalculus.γ := by
    dsimp [Q, D, standardGaussianMehlerAverage]
  have hcommute_has (x : ℝ) : HasDerivAt P (a * Q x) x := by
    have h :=
      (Examples.GaussianLipschitzMehlerCalculus.standardGaussianMehlerAverage_hasDerivAt_of_lipschitz
        hu ⟨(B : ℝ), hu_bounded⟩ ht x).2
    have hvalue :
        Real.exp (-t) *
            ∫ y, deriv u (standardGaussianMehlerArgument t x y)
              ∂Examples.GaussianLipschitzMehlerCalculus.γ = a * Q x := by
      have hmul := congrArg (fun z : ℝ => a * z) (hQ_integral x).symm
      simpa [a] using hmul
    simpa only [P] using h.congr_deriv hvalue
  have hcommute : deriv P = fun x => a * Q x := by
    funext x
    exact (hcommute_has x).deriv
  have hPdiff : Differentiable ℝ P := by
    intro x
    exact (hcommute_has x).differentiableAt
  have hscaledQ_C1 : ContDiff ℝ 1 (fun x => a * Q x) :=
    contDiff_const.mul hQ_C1
  have hderivP_C1 : ContDiff ℝ 1 (deriv P) := by
    rw [hcommute]
    exact hscaledQ_C1
  have hP_C2 : ContDiff ℝ 2 P := by
    have htemp : ContDiff ℝ (1 + 1) P := by
      exact (contDiff_succ_iff_deriv (𝕜 := ℝ) (n := 1) (f := P)).mpr
        ⟨hPdiff, by simp, hderivP_C1⟩
    convert htemp using 1
    norm_num
  have hP_bound (x : ℝ) : ‖P x‖ ≤ (B : ℝ) := by
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    exact standardGaussianMehlerAverage_bounds hu.continuous.measurable
      hu_bounded t (le_of_lt ht) x
  have hfirst_deriv_bound (x : ℝ) :
      ‖deriv P x‖ ≤ a * Kreal := by
    rw [hcommute, norm_mul, Real.norm_eq_abs, abs_of_pos ha]
    exact mul_le_mul_of_nonneg_left (hQ_bound x) ha.le
  have hQ_hasDerivAt (x : ℝ) : HasDerivAt Q (deriv Q x) x :=
    ((contDiff_one_iff_deriv.mp hQ_C1).1 x).hasDerivAt
  have hsecond_hasDerivAt (x : ℝ) :
      HasDerivAt (deriv P) (a * deriv Q x) x := by
    rw [hcommute]
    exact HasDerivAt.const_mul a (hQ_hasDerivAt x)
  have hsecond_formula (x : ℝ) :
      deriv (deriv P) x = a * deriv Q x := (hsecond_hasDerivAt x).deriv
  have hsecond_deriv_bound (x : ℝ) :
      ‖deriv (deriv P) x‖ ≤ (a ^ 2 / b) * Kreal *
        ∫ y, |y| ∂standardGaussianMehler := by
    rw [hsecond_formula, norm_mul, Real.norm_eq_abs, abs_of_pos ha]
    calc
      a * ‖deriv Q x‖ ≤ a * ((a / b) * Kreal *
          ∫ y, |y| ∂standardGaussianMehler) :=
        mul_le_mul_of_nonneg_left (hQ_second_bound x) ha.le
      _ = (a ^ 2 / b) * Kreal * ∫ y, |y| ∂standardGaussianMehler := by ring
  refine ⟨hP_C2, ?_, ?_, ?_⟩
  · exact hP_bound
  · intro x
    simpa [a, Kreal] using hfirst_deriv_bound x
  · intro x
    simpa [a, b, Kreal] using hsecond_deriv_bound x

#print axioms standardGaussianMehlerAverage_boundedLipschitz_C2

end LOOConcentration
