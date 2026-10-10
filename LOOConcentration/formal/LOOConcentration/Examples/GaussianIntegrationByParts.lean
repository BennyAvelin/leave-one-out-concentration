import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

set_option autoImplicit false

namespace LOOConcentration

open MeasureTheory
open scoped NNReal

noncomputable abbrev standardGaussianIBPMeasure : Measure ℝ :=
  ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0)

/-- The literal density used by Mathlib for the standard real Gaussian. -/
noncomputable abbrev standardGaussianIBPDensity (x : ℝ) : ℝ :=
  ProbabilityTheory.gaussianPDFReal 0 (1 : ℝ≥0) x

/-- The standard Gaussian density has derivative `-x` times the density. -/
theorem standardGaussianIBPDensity_hasDerivAt (x : ℝ) :
    HasDerivAt standardGaussianIBPDensity
      (-x * standardGaussianIBPDensity x) x := by
  have hformula : ∀ y : ℝ,
      standardGaussianIBPDensity y =
        (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-y ^ 2 / 2) := by
    intro y
    rw [standardGaussianIBPDensity, ProbabilityTheory.gaussianPDFReal_def]
    simp only [sub_zero, NNReal.coe_one, mul_one]
  have harg0 := ((hasDerivAt_id x).pow 2).neg.div_const (2 : ℝ)
  have harg : HasDerivAt (fun y : ℝ => -y ^ 2 / 2) (-x) x := by
    have hderiv : -(2 * x ^ (2 - 1) * 1) / 2 = -x := by
      norm_num
      ring
    exact harg0.congr_deriv hderiv
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (-y ^ 2 / 2))
      (Real.exp (-x ^ 2 / 2) * (-x)) x := by
    exact harg.exp
  have hmul := hexp.const_mul ((Real.sqrt (2 * Real.pi))⁻¹)
  rw [show standardGaussianIBPDensity = (fun y : ℝ =>
    (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-y ^ 2 / 2)) from funext hformula]
  exact hmul.congr_deriv (by ring)

/-- Bounded `C¹` functions satisfy Gaussian integration by parts. The proof
uses the literal Gaussian density, Lebesgue integration by parts, and the
actual finite first moment of the Gaussian law. -/
theorem standardGaussian_integral_deriv_eq_mul_of_bounded
    {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hg_bounded : ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C)
    (hderiv_bounded : ∃ C : ℝ, ∀ x, ‖deriv g x‖ ≤ C) :
    Integrable (deriv g) standardGaussianIBPMeasure ∧
      Integrable (fun x : ℝ => x * g x) standardGaussianIBPMeasure ∧
      (∫ x, deriv g x ∂standardGaussianIBPMeasure) =
        (∫ x, x * g x ∂standardGaussianIBPMeasure) := by
  rcases hg_bounded with ⟨Cg, hCg⟩
  rcases hderiv_bounded with ⟨Cd, hCd⟩
  let ρ : ℝ → ℝ := standardGaussianIBPDensity
  let γ : Measure ℝ := standardGaussianIBPMeasure
  have hρ : Integrable ρ volume := by
    simpa [ρ, standardGaussianIBPDensity] using
      ProbabilityTheory.integrable_gaussianPDFReal 0 (1 : ℝ≥0)
  have hIdγ : Integrable id γ := by
    apply memLp_one_iff_integrable.mp
    exact ProbabilityTheory.memLp_id_gaussianReal (μ := 0) (v := (1 : ℝ≥0))
      (1 : ℝ≥0)
  have hγ_density : γ = volume.withDensity
      (ProbabilityTheory.gaussianPDF 0 (1 : ℝ≥0)) := by
    exact ProbabilityTheory.gaussianReal_of_var_ne_zero 0 (by norm_num)
  have hIdρ : Integrable (fun x : ℝ => x * ρ x) volume := by
    have hIdDensity : Integrable
        (fun x : ℝ => id x * (ProbabilityTheory.gaussianPDF 0 (1 : ℝ≥0) x).toReal)
        volume := by
      have hIdγ' : Integrable id
          (volume.withDensity (ProbabilityTheory.gaussianPDF 0 (1 : ℝ≥0))) :=
        hγ_density ▸ hIdγ
      exact (integrable_withDensity_iff
        (ProbabilityTheory.measurable_gaussianPDF 0 (1 : ℝ≥0))
        (ae_of_all volume fun _ => ProbabilityTheory.gaussianPDF_lt_top)).mp hIdγ'
    convert hIdDensity using 1 with x
    simp [ρ, standardGaussianIBPDensity, ProbabilityTheory.toReal_gaussianPDF]
  have hderiv_cont : Continuous (deriv g) := hg.continuous_deriv_one
  have hderivγ : Integrable (deriv g) γ := by
    refine (integrable_const Cd).mono' hderiv_cont.aestronglyMeasurable ?_
    exact ae_of_all γ fun x => hCd x
  have hxgγ : Integrable (fun x : ℝ => x * g x) γ := by
    exact hIdγ.mul_bdd hg.continuous.aestronglyMeasurable
      (ae_of_all γ fun x => hCg x)
  have hρg : Integrable (fun x : ℝ => g x * ρ x) volume := by
    exact hρ.bdd_mul hg.continuous.aestronglyMeasurable
      (ae_of_all volume fun x => hCg x)
  have hderivρ : Integrable (fun x : ℝ => deriv g x * ρ x) volume := by
    exact hρ.bdd_mul hderiv_cont.aestronglyMeasurable
      (ae_of_all volume fun x => hCd x)
  have hnegIdρ : Integrable (fun x : ℝ => -(x * ρ x)) volume := hIdρ.neg
  have hgnegIdρ : Integrable (fun x : ℝ => g x * (-(x * ρ x))) volume := by
    exact hnegIdρ.bdd_mul hg.continuous.aestronglyMeasurable
      (ae_of_all volume fun x => hCg x)
  have hwhole := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := g) (u' := deriv g) (v := ρ) (v' := fun x => -(x * ρ x))
    (fun x _ => (hg.differentiable_one x).hasDerivAt)
    (fun x _ => by simpa [ρ] using standardGaussianIBPDensity_hasDerivAt x)
    hgnegIdρ hderivρ hρg
  have hdensity :
      (∫ x : ℝ, deriv g x * ρ x) =
        (∫ x : ℝ, (x * g x) * ρ x) := by
    apply neg_injective
    calc
      - (∫ x : ℝ, deriv g x * ρ x) =
          ∫ x : ℝ, g x * (-(x * ρ x)) := hwhole.symm
      _ = ∫ x : ℝ, -((x * g x) * ρ x) := by
          apply integral_congr_ae
          exact ae_of_all volume fun x => by ring
      _ = - (∫ x : ℝ, (x * g x) * ρ x) := by rw [integral_neg]
  refine ⟨?_, ?_, ?_⟩
  · simpa [γ] using hderivγ
  · simpa [γ] using hxgγ
  · calc
      (∫ x, deriv g x ∂standardGaussianIBPMeasure) =
          ∫ x : ℝ, ρ x * deriv g x := by
            rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul
              (μ := 0) (v := (1 : ℝ≥0)) (by norm_num)]
            rfl
      _ = ∫ x : ℝ, deriv g x * ρ x := by
            apply integral_congr_ae
            exact ae_of_all volume fun x => mul_comm _ _
      _ = ∫ x : ℝ, (x * g x) * ρ x := hdensity
      _ = ∫ x : ℝ, ρ x * (x * g x) := by
            apply integral_congr_ae
            exact ae_of_all volume fun x => mul_comm _ _
      _ = (∫ x, x * g x ∂standardGaussianIBPMeasure) := by
            symm
            rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul
              (μ := 0) (v := (1 : ℝ≥0)) (by norm_num)]
            rfl

end LOOConcentration
