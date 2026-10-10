import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

set_option autoImplicit false

namespace LOOConcentration

open MeasureTheory
open scoped NNReal

noncomputable abbrev standardGaussian : Measure ℝ :=
  ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0)

/-- The unnormalised squared Euclidean norm on a finite Gaussian coordinate
space. -/
def standardGaussianSqSum {r : ℕ} (x : Fin r → ℝ) : ℝ :=
  ∑ i : Fin r, x i ^ 2

/-- The quadratic exponential is integrable under the standard real Gaussian
whenever its exponent is below the Gaussian decay rate. -/
theorem integrable_exp_sq_standardGaussian {t : ℝ} (ht : t < 1 / 2) :
    Integrable (fun x : ℝ => Real.exp (t * x ^ 2)) standardGaussian := by
  have hdecay : 0 < (1 / 2 : ℝ) - t := by linarith
  have hdensity : ∀ x : ℝ,
      Real.exp (t * x ^ 2) * ProbabilityTheory.gaussianPDFReal 0 (1 : ℝ≥0) x =
        (Real.sqrt (2 * Real.pi))⁻¹ *
          Real.exp (-((1 / 2 : ℝ) - t) * x ^ 2) := by
    intro x
    rw [ProbabilityTheory.gaussianPDFReal_def]
    simp only [sub_zero, NNReal.coe_one, mul_one]
    calc
      Real.exp (t * x ^ 2) *
          ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2)) =
          (Real.sqrt (2 * Real.pi))⁻¹ *
            (Real.exp (t * x ^ 2) * Real.exp (-x ^ 2 / 2)) := by ring
      _ = (Real.sqrt (2 * Real.pi))⁻¹ *
          Real.exp (t * x ^ 2 + (-x ^ 2 / 2)) := by rw [← Real.exp_add]
      _ = (Real.sqrt (2 * Real.pi))⁻¹ *
          Real.exp (-((1 / 2 : ℝ) - t) * x ^ 2) := by congr 2; ring
  have hweighted : Integrable
      (fun x : ℝ => Real.exp (t * x ^ 2) *
        ProbabilityTheory.gaussianPDFReal 0 (1 : ℝ≥0) x) volume := by
    rw [show (fun x : ℝ => Real.exp (t * x ^ 2) *
        ProbabilityTheory.gaussianPDFReal 0 (1 : ℝ≥0) x) =
        fun x => (Real.sqrt (2 * Real.pi))⁻¹ *
          Real.exp (-((1 / 2 : ℝ) - t) * x ^ 2) from funext hdensity]
    exact (integrable_exp_neg_mul_sq hdecay).const_mul _
  have hweighted' : Integrable
      (fun x : ℝ => Real.exp (t * x ^ 2) *
        (ProbabilityTheory.gaussianPDF 0 (1 : ℝ≥0) x).toReal) volume := by
    convert hweighted using 1
    funext x
    rw [ProbabilityTheory.toReal_gaussianPDF]
  rw [show standardGaussian =
      volume.withDensity (ProbabilityTheory.gaussianPDF 0 (1 : ℝ≥0)) from
        ProbabilityTheory.gaussianReal_of_var_ne_zero 0 (by norm_num)]
  apply (integrable_withDensity_iff
      (ProbabilityTheory.measurable_gaussianPDF 0 (1 : ℝ≥0))
      (ae_of_all volume fun x => ProbabilityTheory.gaussianPDF_lt_top)).2
  exact hweighted'

/-- Exact quadratic MGF for one standard real Gaussian coordinate.  The
right-hand side is written as an inverse square root, equivalently
`(1 - 2*t)^(-1/2)`. -/
theorem integral_exp_sq_standardGaussian {t : ℝ} (ht : t < 1 / 2) :
    (∫ x : ℝ, Real.exp (t * x ^ 2) ∂standardGaussian) =
      1 / Real.sqrt (1 - 2 * t) := by
  have hdecay : 0 < (1 / 2 : ℝ) - t := by linarith
  have hq : 0 < 1 - 2 * t := by linarith
  have hformula : ∀ x : ℝ,
      ProbabilityTheory.gaussianPDFReal 0 (1 : ℝ≥0) x * Real.exp (t * x ^ 2) =
        (Real.sqrt (2 * Real.pi))⁻¹ *
          Real.exp (-((1 / 2 : ℝ) - t) * x ^ 2) := by
    intro x
    rw [ProbabilityTheory.gaussianPDFReal_def]
    simp only [sub_zero, NNReal.coe_one, mul_one]
    calc
      ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2)) *
          Real.exp (t * x ^ 2) =
          (Real.sqrt (2 * Real.pi))⁻¹ *
            (Real.exp (-x ^ 2 / 2) * Real.exp (t * x ^ 2)) := by ring
      _ = (Real.sqrt (2 * Real.pi))⁻¹ *
          Real.exp (-x ^ 2 / 2 + t * x ^ 2) := by rw [← Real.exp_add]
      _ = (Real.sqrt (2 * Real.pi))⁻¹ *
          Real.exp (-((1 / 2 : ℝ) - t) * x ^ 2) := by congr 2; ring
  calc
    (∫ x : ℝ, Real.exp (t * x ^ 2) ∂standardGaussian)
        = ∫ x : ℝ,
            ProbabilityTheory.gaussianPDFReal 0 (1 : ℝ≥0) x *
              Real.exp (t * x ^ 2) := by
          rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul
            (v := (1 : ℝ≥0)) (by norm_num)]
          simp only [smul_eq_mul]
    _ = (Real.sqrt (2 * Real.pi))⁻¹ *
          ∫ x : ℝ, Real.exp (-((1 / 2 : ℝ) - t) * x ^ 2) := by
          rw [show (fun x : ℝ => ProbabilityTheory.gaussianPDFReal 0 (1 : ℝ≥0) x *
              Real.exp (t * x ^ 2)) =
              fun x => (Real.sqrt (2 * Real.pi))⁻¹ *
                Real.exp (-((1 / 2 : ℝ) - t) * x ^ 2) from funext hformula]
          rw [integral_const_mul]
    _ = 1 / Real.sqrt (1 - 2 * t) := by
          rw [integral_gaussian]
          have hcoeff : (1 / 2 : ℝ) - t = (1 - 2 * t) / 2 := by ring
          rw [hcoeff]
          have harg : Real.pi / ((1 - 2 * t) / 2) =
              (2 * Real.pi) / (1 - 2 * t) := by
            field_simp
          rw [harg, Real.sqrt_div (by positivity)]
          have hroot1 : Real.sqrt (2 * Real.pi) ≠ 0 :=
            ne_of_gt (Real.sqrt_pos.2 (by positivity))
          have hroot2 : Real.sqrt (1 - 2 * t) ≠ 0 :=
            ne_of_gt (Real.sqrt_pos.2 hq)
          field_simp

/-- The finite one-coordinate MGF is strictly positive on its domain. -/
theorem integral_exp_sq_standardGaussian_pos {t : ℝ} (ht : t < 1 / 2) :
    0 < ∫ x : ℝ, Real.exp (t * x ^ 2) ∂standardGaussian := by
  rw [integral_exp_sq_standardGaussian ht]
  have hq : 0 < 1 - 2 * t := by linarith
  exact div_pos one_pos (Real.sqrt_pos.2 hq)

/-- The exponential of the squared Euclidean norm is integrable for the
actual finite product law of independent standard Gaussian coordinates. -/
theorem integrable_exp_sqSum_standardGaussian_pi {r : ℕ} {t : ℝ}
    (ht : t < 1 / 2) :
    Integrable (fun x : Fin r → ℝ =>
      Real.exp (t * standardGaussianSqSum x))
      (Measure.pi fun _ : Fin r => standardGaussian) := by
  have hfactor : ∀ x : Fin r → ℝ,
      Real.exp (t * standardGaussianSqSum x) =
        ∏ i : Fin r, Real.exp (t * x i ^ 2) := by
    intro x
    rw [standardGaussianSqSum, Finset.mul_sum, Real.exp_sum]
  rw [show (fun x : Fin r → ℝ => Real.exp (t * standardGaussianSqSum x)) =
      fun x => ∏ i : Fin r, Real.exp (t * x i ^ 2) from funext hfactor]
  exact Integrable.fintype_prod (fun _ => integrable_exp_sq_standardGaussian ht)

/-- The squared norm of `r` independent standard real Gaussian coordinates
has MGF `(1 - 2*t)^(-r/2)`, represented by `Real.rpow`.  This uses the
actual `Measure.pi` product law. -/
theorem integral_exp_sqSum_standardGaussian_pi {r : ℕ} {t : ℝ}
    (ht : t < 1 / 2) :
    (∫ x : Fin r → ℝ, Real.exp (t * standardGaussianSqSum x)
      ∂(Measure.pi fun _ : Fin r => standardGaussian)) =
        (1 - 2 * t) ^ (-(r : ℝ) / 2) := by
  have hq : 0 < 1 - 2 * t := by linarith
  have hfactor : ∀ x : Fin r → ℝ,
      Real.exp (t * standardGaussianSqSum x) =
        ∏ i : Fin r, Real.exp (t * x i ^ 2) := by
    intro x
    rw [standardGaussianSqSum, Finset.mul_sum, Real.exp_sum]
  calc
    (∫ x : Fin r → ℝ, Real.exp (t * standardGaussianSqSum x)
      ∂(Measure.pi fun _ : Fin r => standardGaussian)) =
        ∫ x : Fin r → ℝ, ∏ i : Fin r, Real.exp (t * x i ^ 2)
          ∂(Measure.pi fun _ : Fin r => standardGaussian) := by
            apply integral_congr_ae
            exact ae_of_all _ hfactor
    _ = ∏ i : Fin r, ∫ x : ℝ, Real.exp (t * x ^ 2) ∂standardGaussian :=
          by
            simpa only [standardGaussian] using
              (integral_fintype_prod_eq_prod
                (f := fun _ : Fin r => fun x : ℝ => Real.exp (t * x ^ 2))
                (μ := fun _ : Fin r => standardGaussian))
    _ = (1 / Real.sqrt (1 - 2 * t)) ^ r := by
          simp_rw [integral_exp_sq_standardGaussian ht]
          simp
    _ = (1 - 2 * t) ^ (-(r : ℝ) / 2) := by
          have hp : (1 - 2 * t) ^ (-(r : ℝ) / 2) =
              (1 / Real.sqrt (1 - 2 * t)) ^ r := by
            calc
              (1 - 2 * t) ^ (-(r : ℝ) / 2) =
                  (1 - 2 * t) ^ (-((r : ℝ) / 2)) := by
                    congr 1
                    ring
              _ = ((1 - 2 * t) ^ ((r : ℝ) / 2))⁻¹ :=
                    Real.rpow_neg hq.le _
              _ = (Real.sqrt (1 - 2 * t) ^ r)⁻¹ := by
                    simpa only [Real.rpow_natCast] using congrArg (fun z : ℝ => z⁻¹)
                      (Real.rpow_div_two_eq_sqrt (r : ℝ) hq.le)
              _ = (1 / Real.sqrt (1 - 2 * t)) ^ r := by
                    rw [one_div, inv_pow]
          exact hp.symm

#print axioms integrable_exp_sq_standardGaussian
#print axioms integral_exp_sq_standardGaussian
#print axioms integral_exp_sq_standardGaussian_pos
#print axioms integrable_exp_sqSum_standardGaussian_pi
#print axioms integral_exp_sqSum_standardGaussian_pi

end LOOConcentration
