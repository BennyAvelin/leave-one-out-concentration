import LOOConcentration.Examples.GaussianMehler
import LOOConcentration.Examples.GaussianMehlerEnergy
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic

/-!
# Spatial differentiation for bounded Lipschitz Mehler data

This module obtains scalar almost-everywhere differentiability from
Rademacher's theorem, transfers it along the actual nondegenerate Gaussian
affine kernel, and proves differentiation under the source integral using
the global Lipschitz bound.
-/

set_option autoImplicit false

namespace LOOConcentration.Examples.GaussianLipschitzMehlerCalculus

open MeasureTheory
open Filter
open scoped Topology NNReal

noncomputable abbrev γ : Measure ℝ := LOOConcentration.standardGaussianMehler

private lemma mehlerVariance_pos {t : ℝ} (ht : 0 < t) :
    0 < 1 - Real.exp (-2 * t) := by
  have harg : -2 * t < 0 := by nlinarith
  have hexp : Real.exp (-2 * t) < 1 := Real.exp_lt_one_iff.mpr harg
  linarith

private lemma mehlerAffine_lipschitz (a c : ℝ) :
    LipschitzWith (Real.nnabs a) (fun x : ℝ => a * x + c) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, Real.dist_eq]
  calc
    |a * x + c - (a * y + c)| = |a| * |x - y| := by
      rw [← abs_mul]
      congr 1
      ring
    _ ≤ (Real.nnabs a : ℝ) * |x - y| := by
      simpa only [Real.coe_nnabs] using
        (le_rfl : |a| * |x - y| ≤ |a| * |x - y|)

private theorem ae_differentiableAt_mehlerAffine
    {f : ℝ → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ∀ᵐ y ∂γ, DifferentiableAt ℝ f
      (LOOConcentration.standardGaussianMehlerArgument t x y) := by
  let a : ℝ := Real.exp (-t)
  let b : ℝ := Real.sqrt (1 - Real.exp (-2 * t))
  let v : ℝ≥0 := ⟨b ^ 2, sq_nonneg b⟩
  have hbpos : 0 < b := by
    dsimp [b]
    exact Real.sqrt_pos.2 (mehlerVariance_pos ht)
  have hv : v ≠ 0 := by
    intro hvzero
    have hval : (v : ℝ) = 0 := congrArg (fun q : ℝ≥0 => (q : ℝ)) hvzero
    change b ^ 2 = 0 at hval
    nlinarith
  have hmul :
      γ.map (fun y : ℝ => b * y) = ProbabilityTheory.gaussianReal 0 v := by
    change (ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0)).map
      (fun y : ℝ => b * y) = ProbabilityTheory.gaussianReal 0 v
    rw [ProbabilityTheory.gaussianReal_map_const_mul]
    simp only [mul_zero, mul_one]
    rfl
  have hargMeas : Measurable (fun y : ℝ => a * x + b * y) := by fun_prop
  have hpush :
      γ.map (fun y : ℝ => a * x + b * y) =
        ProbabilityTheory.gaussianReal (a * x) v := by
    calc
      γ.map (fun y : ℝ => a * x + b * y) =
          γ.map (fun y : ℝ => (b * y) + a * x) := by
            congr 1
            funext y
            ring
      _ = (γ.map (fun y : ℝ => b * y)).map (fun z : ℝ => z + a * x) := by
            rw [Measure.map_map (by fun_prop) (by fun_prop)]
            congr 1
      _ = (ProbabilityTheory.gaussianReal 0 v).map (fun z : ℝ => z + a * x) := by
            rw [hmul]
      _ = ProbabilityTheory.gaussianReal (a * x) v := by
            simpa using
              (ProbabilityTheory.gaussianReal_map_add_const
                (μ := 0) (v := v) (a * x))
  have hAC : γ.map (fun y : ℝ => a * x + b * y) ≪ (volume : Measure ℝ) := by
    rw [hpush]
    exact ProbabilityTheory.gaussianReal_absolutelyContinuous (a * x) hv
  have hRademacher :
      ∀ᵐ z ∂(volume : Measure ℝ), DifferentiableAt ℝ f z :=
    hf.ae_differentiableAt_of_real (μ := (volume : Measure ℝ))
  have hmap :
      ∀ᵐ z ∂(γ.map (fun y : ℝ => a * x + b * y)), DifferentiableAt ℝ f z :=
    hAC.ae_le hRademacher
  have hdiff :
    ∀ᵐ y ∂γ, DifferentiableAt ℝ f (a * x + b * y) :=
    (MeasureTheory.ae_map_iff hargMeas.aemeasurable
      (measurableSet_of_differentiableAt ℝ (f := f))).mp hmap
  filter_upwards [hdiff] with y hy
  simpa [LOOConcentration.standardGaussianMehlerArgument, LOOConcentration.standardGaussianMehlerDrift,
    LOOConcentration.standardGaussianMehlerNoise, a, b] using hy

/-- At every positive time, a bounded globally Lipschitz scalar input has the
actual spatial derivative given by the Mehler average of its a.e. derivative.
The derivative section is integrable, and the only coefficient is the exact
drift `exp (-t)`. -/
theorem standardGaussianMehlerAverage_hasDerivAt_of_lipschitz
    {f : ℝ → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f)
    (hf_bounded : ∃ M : ℝ, ∀ y, ‖f y‖ ≤ M)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Integrable (fun y => deriv f
      (LOOConcentration.standardGaussianMehlerArgument t x y)) γ ∧
    HasDerivAt
      (fun z => LOOConcentration.standardGaussianMehlerAverage f hf.continuous.measurable
        hf_bounded t ht.le z)
      (Real.exp (-t) * ∫ y, deriv f
        (LOOConcentration.standardGaussianMehlerArgument t x y) ∂γ) x := by
  let a : ℝ := Real.exp (-t)
  let b : ℝ := Real.sqrt (1 - Real.exp (-2 * t))
  let F : ℝ → ℝ → ℝ := fun z y => f (a * z + b * y)
  let F' : ℝ → ℝ := fun y => a * deriv f (a * x + b * y)
  have hargMeas (z : ℝ) : Measurable (fun y : ℝ => a * z + b * y) := by
    fun_prop
  have hsection_meas :
      Measurable (fun y : ℝ => deriv f (a * x + b * y)) :=
    (measurable_deriv f).comp (hargMeas x)
  have hderiv_bound (u : ℝ) : ‖deriv f u‖ ≤ (C : ℝ) :=
    norm_deriv_le_of_lipschitz hf
  have hC_nonneg : 0 ≤ (C : ℝ) := C.coe_nonneg
  have hsection_int : Integrable (fun y : ℝ => deriv f (a * x + b * y)) γ := by
    refine (integrable_const (C : ℝ)).mono' hsection_meas.aestronglyMeasurable ?_
    filter_upwards [] with y
    simpa [Real.norm_eq_abs, abs_of_nonneg hC_nonneg] using hderiv_bound (a * x + b * y)
  have hF_meas : ∀ᶠ z in 𝓝 x, AEStronglyMeasurable (F z) γ := by
    filter_upwards [] with z
    exact ((hf.continuous.measurable.comp (hargMeas z)).aestronglyMeasurable)
  have hF_int : Integrable (F x) γ := by
    simpa [F, a, b, LOOConcentration.standardGaussianMehlerArgument,
      LOOConcentration.standardGaussianMehlerDrift, LOOConcentration.standardGaussianMehlerNoise] using
      LOOConcentration.integrable_standardGaussianMehler_section
        (t := t) hf.continuous.measurable hf_bounded x
  have hF'_meas : AEStronglyMeasurable F' γ := by
    exact (measurable_const.mul ((measurable_deriv f).comp (hargMeas x))).aestronglyMeasurable
  let B : ℝ := ((C * Real.nnabs a : ℝ≥0) : ℝ)
  have hbound_int : Integrable (fun _ : ℝ => B) γ := integrable_const B
  have h_lipsch :
      ∀ᵐ y ∂γ, LipschitzOnWith (Real.nnabs B) (F · y) (Set.univ : Set ℝ) := by
    filter_upwards [] with y
    have hcomp : LipschitzWith (C * Real.nnabs a) (fun z : ℝ => f (a * z + b * y)) := by
      change LipschitzWith (C * ‖a‖₊) (f ∘ fun z : ℝ => a * z + b * y)
      exact hf.comp (mehlerAffine_lipschitz a (b * y))
    simpa [B] using hcomp.lipschitzOnWith (s := Set.univ)
  have h_diff :
      ∀ᵐ y ∂γ, HasDerivAt (F · y) (F' y) x := by
    filter_upwards [ae_differentiableAt_mehlerAffine hf ht x] with y hy
    have harg : HasDerivAt (fun z : ℝ => a * z + b * y) a x := by
      simpa [a, b, mul_comm] using
        (((hasDerivAt_id x).const_mul a).add_const (b * y))
    have hfpoint : HasDerivAt f (deriv f (a * x + b * y)) (a * x + b * y) :=
      hy.hasDerivAt
    have hcomp := hfpoint.comp x harg
    exact hcomp.congr_deriv (by dsimp [F']; ring)
  have hparam := hasDerivAt_integral_of_dominated_loc_of_lip
    (s := Set.univ) (x₀ := x) (F := F) (F' := F')
    (show (Set.univ : Set ℝ) ∈ 𝓝 x from Filter.univ_mem)
    hF_meas hF_int hF'_meas h_lipsch hbound_int h_diff
  have hfactor :
      (∫ y, a * deriv f (a * x + b * y) ∂γ) =
        a * ∫ y, deriv f (a * x + b * y) ∂γ := by
    rw [integral_const_mul]
  have hresult := hparam.2.congr_deriv (by simpa [F', a, b] using hfactor)
  refine ⟨?_, ?_⟩
  · simpa [a, b, LOOConcentration.standardGaussianMehlerArgument,
      LOOConcentration.standardGaussianMehlerDrift, LOOConcentration.standardGaussianMehlerNoise] using hsection_int
  · simpa [LOOConcentration.standardGaussianMehlerAverage, F, a, b,
      LOOConcentration.standardGaussianMehlerArgument, LOOConcentration.standardGaussianMehlerDrift,
      LOOConcentration.standardGaussianMehlerNoise, γ, LOOConcentration.standardGaussianMehler] using hresult

/-- A bounded positive globally Lipschitz input satisfies weighted Mehler
energy contraction. The pointwise estimate comes from the actual Lipschitz
spatial derivative formula and weighted Cauchy--Schwarz; integration then uses
the canonical stationary Gaussian Mehler average. -/
theorem standardGaussianMehlerAverage_weighted_energy_decay_of_lipschitz
    {f : ℝ → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f)
    {ε : ℝ} (hε : 0 < ε) (hflower : ∀ y, ε ≤ f y)
    (hbounded : ∃ M : ℝ, ∀ y, ‖f y‖ ≤ M)
    {t : ℝ} (ht : 0 < t) :
    let P : ℝ → ℝ := LOOConcentration.standardGaussianMehlerAverage f
      hf.continuous.measurable hbounded t ht.le
    let E : ℝ → ℝ := fun y => (deriv f y) ^ 2 / f y
    Integrable E γ ∧
      Integrable (fun x => (deriv P x) ^ 2 / P x) γ ∧
      (∫ x, (deriv P x) ^ 2 / P x ∂γ) ≤
        Real.exp (-2 * t) * (∫ x, E x ∂γ) := by
  rcases hbounded with ⟨M, hM⟩
  let P : ℝ → ℝ := LOOConcentration.standardGaussianMehlerAverage f
    hf.continuous.measurable ⟨M, hM⟩ t ht.le
  let E : ℝ → ℝ := fun y => (deriv f y) ^ 2 / f y
  let K : ℝ := (C : ℝ) ^ 2 / ε
  let hdf : Measurable (deriv f) := measurable_deriv f
  have hCnonneg : 0 ≤ (C : ℝ) := C.coe_nonneg
  have hKnonneg : 0 ≤ K := by
    dsimp [K]
    exact div_nonneg (sq_nonneg _) hε.le
  have hfpos (y : ℝ) : 0 < f y := lt_of_lt_of_le hε (hflower y)
  have hfupper : ∀ y, f y ≤ M := by
    intro y
    have hnonneg : 0 ≤ f y := le_of_lt (hfpos y)
    have habs : |f y| ≤ M := by simpa [Real.norm_eq_abs] using hM y
    simpa [abs_of_nonneg hnonneg] using habs
  have hderiv_abs (y : ℝ) : |deriv f y| ≤ (C : ℝ) := by
    simpa [Real.norm_eq_abs] using (norm_deriv_le_of_lipschitz hf :
      ‖deriv f y‖ ≤ (C : ℝ))
  have hEmeas : Measurable E := by
    have hmul : Measurable (fun y => deriv f y * deriv f y / f y) :=
      (hdf.mul hdf).div hf.continuous.measurable
    simpa only [E, pow_two] using hmul
  have hEnonneg (y : ℝ) : 0 ≤ E y := by
    dsimp [E]
    exact div_nonneg (sq_nonneg _) (hfpos y).le
  have hEnum (y : ℝ) : (deriv f y) ^ 2 ≤ (C : ℝ) ^ 2 := by
    have hsquare : |deriv f y| ^ 2 ≤ (C : ℝ) ^ 2 := by
      simpa only [pow_two] using
        (mul_self_le_mul_self (abs_nonneg _) (hderiv_abs y))
    calc
      (deriv f y) ^ 2 = |deriv f y| ^ 2 := (sq_abs _).symm
      _ ≤ (C : ℝ) ^ 2 := hsquare
  have hEupper (y : ℝ) : E y ≤ K := by
    dsimp [E, K]
    rw [div_le_div_iff₀ (hfpos y) hε]
    calc
      (deriv f y) ^ 2 * ε ≤ (C : ℝ) ^ 2 * ε :=
        mul_le_mul_of_nonneg_right (hEnum y) hε.le
      _ ≤ (C : ℝ) ^ 2 * f y :=
        mul_le_mul_of_nonneg_left (hflower y) (sq_nonneg (C : ℝ))
  have hEnorm (y : ℝ) : ‖E y‖ ≤ K := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hEnonneg y)]
    exact hEupper y
  have hEint : Integrable E γ := by
    refine (integrable_const K).mono' hEmeas.aestronglyMeasurable ?_
    filter_upwards [] with y
    simpa [Real.norm_eq_abs, abs_of_nonneg hKnonneg] using hEnorm y
  let Ebound : ∃ B : ℝ, ∀ y, ‖E y‖ ≤ B := ⟨K, hEnorm⟩
  let PE : ℝ → ℝ := LOOConcentration.standardGaussianMehlerAverage E hEmeas Ebound t ht.le
  have hPEbounds (x : ℝ) : -K ≤ PE x ∧ PE x ≤ K := by
    dsimp [PE, Ebound]
    exact LOOConcentration.standardGaussianMehlerAverage_bounds hEmeas hEnorm t ht.le x
  have hPEnorm (x : ℝ) : ‖PE x‖ ≤ K := by
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨hPEbounds x |>.1, hPEbounds x |>.2⟩
  have hPEmeas : Measurable PE := by
    dsimp [PE, Ebound]
    exact LOOConcentration.measurable_standardGaussianMehlerAverage hEmeas Ebound t ht.le
  have hPEint : Integrable PE γ := by
    refine (integrable_const K).mono' hPEmeas.aestronglyMeasurable ?_
    filter_upwards [] with x
    simpa [Real.norm_eq_abs, abs_of_nonneg hKnonneg] using hPEnorm x
  have hP_lower (x : ℝ) : ε ≤ P x := by
    dsimp [P]
    simpa [LOOConcentration.standardGaussianMehlerAverage] using
      (LOOConcentration.standardGaussianMehlerAverage_lower_bound hf.continuous.measurable
        hM hflower t ht.le x)
  have hPmeas : Measurable P := by
    dsimp [P]
    exact LOOConcentration.measurable_standardGaussianMehlerAverage
      hf.continuous.measurable ⟨M, hM⟩ t ht.le
  have hderivBound : ∀ y, |deriv f y| ≤ (C : ℝ) := hderiv_abs
  let hderivWitness : ∃ D : ℝ, ∀ y, ‖deriv f y‖ ≤ D :=
    ⟨C, fun y => by simpa [Real.norm_eq_abs] using hderiv_abs y⟩
  let Pderiv : ℝ → ℝ := LOOConcentration.standardGaussianMehlerAverage (deriv f)
    hdf hderivWitness t ht.le
  have hspatial (x : ℝ) : deriv P x = Real.exp (-t) * Pderiv x := by
    have h := (standardGaussianMehlerAverage_hasDerivAt_of_lipschitz
      hf ⟨M, hM⟩ ht x).2.deriv
    have havg :
        (∫ y, deriv f (LOOConcentration.standardGaussianMehlerArgument t x y) ∂γ) = Pderiv x := rfl
    change deriv (fun z => LOOConcentration.standardGaussianMehlerAverage f
      hf.continuous.measurable ⟨M, hM⟩ t ht.le z) x =
      Real.exp (-t) * Pderiv x
    rw [← havg]
    exact h
  have hweighted (x : ℝ) : (Pderiv x) ^ 2 / P x ≤ PE x := by
    dsimp [P, Pderiv, PE, Ebound]
    exact LOOConcentration.standardGaussianMehlerAverage_weighted_cauchy_schwarz
      hf.continuous.measurable hdf hε hflower hfupper hderiv_abs t ht.le x
  have hcoeff : Real.exp (-t) ^ 2 = Real.exp (-2 * t) := by
    calc
      Real.exp (-t) ^ 2 = Real.exp (-t) * Real.exp (-t) := by rw [pow_two]
      _ = Real.exp ((-t) + (-t)) := (Real.exp_add _ _).symm
      _ = Real.exp (-2 * t) := by congr 1; ring
  have hPpos (x : ℝ) : 0 < P x := lt_of_lt_of_le hε (hP_lower x)
  have hpoint (x : ℝ) :
      (deriv P x) ^ 2 / P x ≤ Real.exp (-2 * t) * PE x := by
    calc
      (deriv P x) ^ 2 / P x = (Real.exp (-t) * Pderiv x) ^ 2 / P x := by
        rw [hspatial x]
      _ = Real.exp (-2 * t) * ((Pderiv x) ^ 2 / P x) := by
        rw [mul_pow, hcoeff]
        field_simp [ne_of_gt (hPpos x)]
      _ ≤ Real.exp (-2 * t) * PE x :=
        mul_le_mul_of_nonneg_left (hweighted x) (Real.exp_nonneg _)
  have hexp_le_one : Real.exp (-2 * t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [ht])
  have hQupper (x : ℝ) : (deriv P x) ^ 2 / P x ≤ K := by
    calc
      (deriv P x) ^ 2 / P x ≤ Real.exp (-2 * t) * PE x := hpoint x
      _ ≤ Real.exp (-2 * t) * K :=
        mul_le_mul_of_nonneg_left (hPEbounds x |>.2) (Real.exp_nonneg _)
      _ ≤ K := by nlinarith [hKnonneg, hexp_le_one]
  have hQnonneg (x : ℝ) : 0 ≤ (deriv P x) ^ 2 / P x :=
    div_nonneg (sq_nonneg _) (hPpos x).le
  let Q : ℝ → ℝ := fun x => (deriv P x) ^ 2 / P x
  have hQmeas : Measurable Q := by
    dsimp [Q]
    fun_prop
  have hQint : Integrable Q γ := by
    refine (integrable_const K).mono' hQmeas.aestronglyMeasurable ?_
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hQnonneg x)]
    exact hQupper x
  have hscaledInt : Integrable (fun x => Real.exp (-2 * t) * PE x) γ :=
    hPEint.const_mul (Real.exp (-2 * t))
  have hstationary :
      (∫ x, PE x ∂γ) = ∫ x, E x ∂γ := by
    dsimp [PE, Ebound]
    exact LOOConcentration.integral_standardGaussianMehlerAverage_eq hEmeas Ebound t ht.le
  have henergy :
      (∫ x, Q x ∂γ) ≤ Real.exp (-2 * t) * (∫ x, E x ∂γ) := by
    calc
      (∫ x, Q x ∂γ) ≤ ∫ x, Real.exp (-2 * t) * PE x ∂γ :=
        integral_mono hQint hscaledInt (fun x => by simpa [Q] using hpoint x)
      _ = Real.exp (-2 * t) * ∫ x, PE x ∂γ := integral_const_mul _ _
      _ = Real.exp (-2 * t) * ∫ x, E x ∂γ := by rw [hstationary]
  refine ⟨?_, ?_, ?_⟩
  · simpa [E] using hEint
  · simpa [Q, P] using hQint
  · simpa [Q, P, E] using henergy

#print axioms standardGaussianMehlerAverage_hasDerivAt_of_lipschitz
#print axioms standardGaussianMehlerAverage_weighted_energy_decay_of_lipschitz

end LOOConcentration.Examples.GaussianLipschitzMehlerCalculus
