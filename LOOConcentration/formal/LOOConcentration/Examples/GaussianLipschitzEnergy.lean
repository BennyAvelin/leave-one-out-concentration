import LOOConcentration.Examples.GaussianLipschitzMehlerCalculus
import LOOConcentration.Examples.GaussianMehlerBoundedLSI
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic

/-!
# Signed square energy and endpoint continuity for bounded Lipschitz Mehler data

This module proves the unweighted derivative-square contraction for the
canonical scalar Gaussian Mehler average, and its zero-time square and entropy
limits. The input may change sign or vanish.
-/

set_option autoImplicit false

namespace LOOConcentration.Examples.GaussianLipschitzEnergy

open MeasureTheory
open Filter
open scoped Topology NNReal

noncomputable abbrev γ : Measure ℝ := LOOConcentration.standardGaussianMehler

private noncomputable def squareLogSquare (z : ℝ) : ℝ :=
  z ^ 2 * Real.log (z ^ 2)

private lemma continuous_squareLogSquare :
    Continuous squareLogSquare := by
  unfold squareLogSquare
  exact Real.continuous_mul_log.comp (by fun_prop)

/-- The actual squared derivative energy of a bounded globally Lipschitz
function is integrable, and the canonical Mehler average contracts it by the
exact factor `exp (-2t)`. The input is signed and may vanish. -/
theorem standardGaussianMehlerAverage_signed_square_energy_decay_of_lipschitz
    {f : ℝ → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f)
    (hbounded : ∃ M : ℝ, ∀ y, ‖f y‖ ≤ M)
    {t : ℝ} (ht : 0 < t) :
    let P : ℝ → ℝ := LOOConcentration.standardGaussianMehlerAverage f
      hf.continuous.measurable hbounded t ht.le
    let E : ℝ → ℝ := fun y => (deriv f y) ^ 2
    Integrable E γ ∧
      Integrable (fun x => (deriv P x) ^ 2) γ ∧
      (∫ x, (deriv P x) ^ 2 ∂γ) ≤
        Real.exp (-2 * t) * (∫ x, E x ∂γ) := by
  rcases hbounded with ⟨M, hM⟩
  let hb : ∃ M : ℝ, ∀ y, ‖f y‖ ≤ M := ⟨M, hM⟩
  let P : ℝ → ℝ := LOOConcentration.standardGaussianMehlerAverage f
    hf.continuous.measurable hb t ht.le
  let E : ℝ → ℝ := fun y => (deriv f y) ^ 2
  let PE : ℝ → ℝ := LOOConcentration.standardGaussianMehlerAverage E
    ((measurable_deriv f).pow_const 2) ⟨(C : ℝ) ^ 2, by
      intro y
      have hC : 0 ≤ (C : ℝ) := C.coe_nonneg
      have hd : |deriv f y| ≤ (C : ℝ) := by
        simpa [Real.norm_eq_abs] using
          (norm_deriv_le_of_lipschitz hf : ‖deriv f y‖ ≤ (C : ℝ))
      have hsquare : (deriv f y) ^ 2 ≤ (C : ℝ) ^ 2 := by
        simpa [pow_two] using
          (mul_self_le_mul_self (abs_nonneg (deriv f y)) hd)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hsquare⟩ t ht.le
  have hC2nonneg : 0 ≤ (C : ℝ) ^ 2 := sq_nonneg _
  have hderiv_abs (y : ℝ) : |deriv f y| ≤ (C : ℝ) := by
    simpa [Real.norm_eq_abs] using
      (norm_deriv_le_of_lipschitz hf : ‖deriv f y‖ ≤ (C : ℝ))
  have hEmeas : Measurable E := (measurable_deriv f).pow_const 2
  have hEbound (y : ℝ) : ‖E y‖ ≤ (C : ℝ) ^ 2 := by
    have hsquare : (deriv f y) ^ 2 ≤ (C : ℝ) ^ 2 := by
      simpa [pow_two] using
        (mul_self_le_mul_self (abs_nonneg (deriv f y)) (hderiv_abs y))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hsquare
  have hEint : Integrable E γ := by
    refine (integrable_const ((C : ℝ) ^ 2)).mono' hEmeas.aestronglyMeasurable ?_
    exact ae_of_all γ hEbound
  have hPEmeas : Measurable PE :=
    LOOConcentration.measurable_standardGaussianMehlerAverage hEmeas
      ⟨(C : ℝ) ^ 2, hEbound⟩ t ht.le
  have hPEbounds (x : ℝ) : -(C : ℝ) ^ 2 ≤ PE x ∧ PE x ≤ (C : ℝ) ^ 2 := by
    exact LOOConcentration.standardGaussianMehlerAverage_bounds hEmeas hEbound t ht.le x
  have hPEnonneg (x : ℝ) : 0 ≤ PE x := by
    dsimp [PE, E]
    exact integral_nonneg_of_ae (ae_of_all γ fun y => sq_nonneg (deriv f
      (LOOConcentration.standardGaussianMehlerArgument t x y)))
  have hPEint : Integrable PE γ := by
    refine (integrable_const ((C : ℝ) ^ 2)).mono' hPEmeas.aestronglyMeasurable ?_
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hPEnonneg x)]
    exact hPEbounds x |>.2
  have hformula (x : ℝ) :
      deriv P x = Real.exp (-t) *
        ∫ y, deriv f (LOOConcentration.standardGaussianMehlerArgument t x y) ∂γ := by
    have h :=
      LOOConcentration.Examples.GaussianLipschitzMehlerCalculus.standardGaussianMehlerAverage_hasDerivAt_of_lipschitz
      hf hb ht x
    simpa [P, γ] using h.2.deriv
  have hExpSq : Real.exp (-t) ^ 2 = Real.exp (-2 * t) := by
    calc
      Real.exp (-t) ^ 2 = Real.exp (-t) * Real.exp (-t) := by ring
      _ = Real.exp ((-t) + (-t)) := (Real.exp_add _ _).symm
      _ = Real.exp (-2 * t) := by congr 1; ring
  have hExpLe : Real.exp (-2 * t) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith
  have hpoint (x : ℝ) : (deriv P x) ^ 2 ≤ Real.exp (-2 * t) * PE x := by
    let g : ℝ → ℝ := fun y =>
      deriv f (LOOConcentration.standardGaussianMehlerArgument t x y)
    have hargMeas : Measurable (fun y : ℝ =>
        LOOConcentration.standardGaussianMehlerArgument t x y) := by
      unfold LOOConcentration.standardGaussianMehlerArgument
        LOOConcentration.standardGaussianMehlerDrift LOOConcentration.standardGaussianMehlerNoise
      fun_prop
    have hgmeas : Measurable g := (measurable_deriv f).comp hargMeas
    have hgbound (y : ℝ) : |g y| ≤ (C : ℝ) := hderiv_abs _
    have hcs := LOOConcentration.integral_weighted_cauchy_schwarz
      (μ := γ) (f := fun _ : ℝ => (1 : ℝ)) (g := g)
      (by fun_prop) hgmeas (ε := 1) (B := 1) (G := (C : ℝ))
      (by norm_num) (by intro y; norm_num) (by intro y; norm_num) hgbound
    have hcs' : (∫ y, g y ∂γ) ^ 2 ≤ ∫ y, g y ^ 2 ∂γ := by
      simpa [g] using hcs
    have havg : (∫ y, g y ^ 2 ∂γ) = PE x := by
      simp [g, PE, E, LOOConcentration.standardGaussianMehlerAverage,
        LOOConcentration.standardGaussianMehlerArgument, LOOConcentration.standardGaussianMehlerDrift,
        LOOConcentration.standardGaussianMehlerNoise, γ]
    calc
      (deriv P x) ^ 2 =
          (Real.exp (-t) * ∫ y, g y ∂γ) ^ 2 := by rw [hformula]
      _ = Real.exp (-2 * t) * (∫ y, g y ∂γ) ^ 2 := by rw [mul_pow, hExpSq]
      _ ≤ Real.exp (-2 * t) * ∫ y, g y ^ 2 ∂γ :=
        mul_le_mul_of_nonneg_left hcs' (Real.exp_nonneg _)
      _ = Real.exp (-2 * t) * PE x := by rw [havg]
  have hDmeas : Measurable (fun x : ℝ => (deriv P x) ^ 2) :=
    (measurable_deriv P).pow_const 2
  have hDint : Integrable (fun x : ℝ => (deriv P x) ^ 2) γ := by
    refine (integrable_const ((C : ℝ) ^ 2)).mono' hDmeas.aestronglyMeasurable ?_
    filter_upwards [] with x
    have hupper : (deriv P x) ^ 2 ≤ (C : ℝ) ^ 2 := by
      calc
        (deriv P x) ^ 2 ≤ Real.exp (-2 * t) * PE x := hpoint x
        _ ≤ 1 * (C : ℝ) ^ 2 :=
          mul_le_mul hExpLe (hPEbounds x).2 (hPEnonneg x) (by norm_num)
        _ = (C : ℝ) ^ 2 := by ring
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hupper
  change Integrable E γ ∧
    Integrable (fun x => (deriv P x) ^ 2) γ ∧
    (∫ x, (deriv P x) ^ 2 ∂γ) ≤
      Real.exp (-2 * t) * (∫ x, E x ∂γ)
  refine ⟨hEint, hDint, ?_⟩
  calc
    (∫ x, (deriv P x) ^ 2 ∂γ) ≤
        ∫ x, Real.exp (-2 * t) * PE x ∂γ :=
      integral_mono hDint (hPEint.const_mul (Real.exp (-2 * t))) hpoint
    _ = Real.exp (-2 * t) * (∫ x, E x ∂γ) := by
      rw [integral_const_mul]
      change Real.exp (-2 * t) *
        (∫ x, LOOConcentration.standardGaussianMehlerAverage E hEmeas
          ⟨(C : ℝ) ^ 2, hEbound⟩ t ht.le x ∂γ) = _
      rw [LOOConcentration.integral_standardGaussianMehlerAverage_eq hEmeas
        ⟨(C : ℝ) ^ 2, hEbound⟩ t ht.le]

/-- At zero time, the actual square and square-log-square integrals of the
canonical Mehler average converge to those of the signed bounded Lipschitz
input. Consequently its actual entropy converges as well, including when the
input vanishes. -/
theorem tendsto_standardGaussianMehlerAverage_signed_square_entropy_nhds_zero
    {f : ℝ → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f)
    (hbounded : ∃ M : ℝ, ∀ y, ‖f y‖ ≤ M) :
    let P : ℝ≥0 → ℝ → ℝ := fun t =>
      LOOConcentration.standardGaussianMehlerAverage f hf.continuous.measurable
        hbounded (t : ℝ) t.property
    Tendsto (fun t => ∫ x, (P t x) ^ 2 ∂γ)
      (𝓝 (0 : ℝ≥0)) (𝓝 (∫ x, (f x) ^ 2 ∂γ)) ∧
    Tendsto (fun t => ∫ x, squareLogSquare (P t x) ∂γ)
      (𝓝 (0 : ℝ≥0)) (𝓝 (∫ x, squareLogSquare (f x) ∂γ)) ∧
    Tendsto (fun t => LOOConcentration.looconcentrationEntropy γ (fun x => (P t x) ^ 2))
      (𝓝 (0 : ℝ≥0))
      (𝓝 (LOOConcentration.looconcentrationEntropy γ (fun x => (f x) ^ 2))) := by
  rcases hbounded with ⟨M, hM⟩
  let hb : ∃ M : ℝ, ∀ y, ‖f y‖ ≤ M := ⟨M, hM⟩
  let P : ℝ≥0 → ℝ → ℝ := fun t =>
    LOOConcentration.standardGaussianMehlerAverage f hf.continuous.measurable hb
      (t : ℝ) t.property
  let A : ℝ≥0 → ℝ := fun t => ∫ x, (P t x) ^ 2 ∂γ
  let B : ℝ≥0 → ℝ := fun t => ∫ x, squareLogSquare (P t x) ∂γ
  have hPmeas (t : ℝ≥0) : Measurable (P t) := by
    exact LOOConcentration.measurable_standardGaussianMehlerAverage hf.continuous.measurable
      hb (t : ℝ) t.property
  have hPbounds (t : ℝ≥0) (x : ℝ) : -M ≤ P t x ∧ P t x ≤ M := by
    simpa [P, hb] using
      LOOConcentration.standardGaussianMehlerAverage_bounds hf.continuous.measurable hM
        (t : ℝ) t.property x
  have hPabs (t : ℝ≥0) (x : ℝ) : |P t x| ≤ M :=
    abs_le.mpr (hPbounds t x)
  have hpoint (x : ℝ) : Tendsto (fun t : ℝ≥0 => P t x)
      (𝓝 (0 : ℝ≥0)) (𝓝 (f x)) := by
    simpa [P, hb] using
      LOOConcentration.tendsto_standardGaussianMehlerAverage_nhds_zero
        hf.continuous hb x
  have hsqContinuous : Continuous (fun z : ℝ => z ^ 2) := by fun_prop
  have hsqMeas (t : ℝ≥0) :
      AEStronglyMeasurable (fun x : ℝ => (P t x) ^ 2) γ := by
    exact ((hPmeas t).pow_const 2).aestronglyMeasurable
  have hsqBound (t : ℝ≥0) (x : ℝ) : ‖(P t x) ^ 2‖ ≤ M ^ 2 := by
    have hsquare : (P t x) ^ 2 ≤ M ^ 2 := by
      simpa [pow_two] using (mul_self_le_mul_self (abs_nonneg (P t x))
        (hPabs t x))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hsquare
  have hsqPoint (x : ℝ) : Tendsto (fun t : ℝ≥0 => (P t x) ^ 2)
      (𝓝 (0 : ℝ≥0)) (𝓝 ((f x) ^ 2)) :=
    (hsqContinuous.continuousAt).tendsto.comp (hpoint x)
  have hsqLimit := tendsto_integral_filter_of_dominated_convergence
    (μ := γ) (F := fun t x => (P t x) ^ 2) (f := fun x => (f x) ^ 2)
    (bound := fun _ => M ^ 2)
    (by filter_upwards [] with t; exact hsqMeas t)
    (by
      filter_upwards [] with t
      exact ae_of_all γ (hsqBound t))
    (integrable_const (M ^ 2))
    (by filter_upwards [] with x; exact hsqPoint x)
  have hφcont : Continuous squareLogSquare := continuous_squareLogSquare
  have hφnormcont : ContinuousOn (fun z : ℝ => ‖squareLogSquare z‖)
      (Set.Icc (-M) M) := hφcont.norm.continuousOn
  obtain ⟨K, hK⟩ := isCompact_Icc.bddAbove_image hφnormcont
  have hφbound (z : ℝ) (hz : z ∈ Set.Icc (-M) M) :
      ‖squareLogSquare z‖ ≤ K := hK (Set.mem_image_of_mem _ hz)
  have hφMeas (t : ℝ≥0) :
      AEStronglyMeasurable (fun x : ℝ => squareLogSquare (P t x)) γ := by
    exact (hφcont.measurable.comp (hPmeas t)).aestronglyMeasurable
  have hφBound (t : ℝ≥0) (x : ℝ) :
      ‖squareLogSquare (P t x)‖ ≤ K :=
    hφbound (P t x) ⟨(hPbounds t x).1, (hPbounds t x).2⟩
  have hφPoint (x : ℝ) :
      Tendsto (fun t : ℝ≥0 => squareLogSquare (P t x))
        (𝓝 (0 : ℝ≥0)) (𝓝 (squareLogSquare (f x))) :=
    hφcont.continuousAt.tendsto.comp (hpoint x)
  have hφLimit := tendsto_integral_filter_of_dominated_convergence
    (μ := γ)
    (F := fun t x => squareLogSquare (P t x))
    (f := fun x => squareLogSquare (f x)) (bound := fun _ => K)
    (by filter_upwards [] with t; exact hφMeas t)
    (by
      filter_upwards [] with t
      exact ae_of_all γ (hφBound t))
    (integrable_const K)
    (by filter_upwards [] with x; exact hφPoint x)
  have hA : Tendsto A (𝓝 (0 : ℝ≥0))
      (𝓝 (∫ x, (f x) ^ 2 ∂γ)) := by
    simpa [A] using hsqLimit
  have hB : Tendsto B (𝓝 (0 : ℝ≥0))
      (𝓝 (∫ x, squareLogSquare (f x) ∂γ)) := by
    simpa [B] using hφLimit
  have hAlog : Tendsto (fun t : ℝ≥0 => A t * Real.log (A t))
      (𝓝 (0 : ℝ≥0))
      (𝓝 ((∫ x, (f x) ^ 2 ∂γ) * Real.log (∫ x, (f x) ^ 2 ∂γ))) :=
    Real.continuous_mul_log.continuousAt.tendsto.comp hA
  have hEntropyP (t : ℝ≥0) :
      LOOConcentration.looconcentrationEntropy γ (fun x => (P t x) ^ 2) =
        B t - A t * Real.log (A t) := by
    simp [LOOConcentration.looconcentrationEntropy, A, B, squareLogSquare]
  have hEntropyF :
      LOOConcentration.looconcentrationEntropy γ (fun x => (f x) ^ 2) =
        (∫ x, squareLogSquare (f x) ∂γ) -
          (∫ x, (f x) ^ 2 ∂γ) * Real.log (∫ x, (f x) ^ 2 ∂γ) := by
    simp [LOOConcentration.looconcentrationEntropy, squareLogSquare]
  refine ⟨hA, hB, ?_⟩
  have hcombined := hB.sub hAlog
  change Tendsto
    (fun t : ℝ≥0 => LOOConcentration.looconcentrationEntropy γ (fun x => (P t x) ^ 2))
    (𝓝 (0 : ℝ≥0))
    (𝓝 (LOOConcentration.looconcentrationEntropy γ (fun x => (f x) ^ 2)))
  have hfun : (fun t : ℝ≥0 => LOOConcentration.looconcentrationEntropy γ
      (fun x => (P t x) ^ 2)) =
      (fun t => B t - A t * Real.log (A t)) := by
    funext t
    exact hEntropyP t
  rw [hfun]
  simpa only [hEntropyF] using hcombined

#print axioms standardGaussianMehlerAverage_signed_square_energy_decay_of_lipschitz
#print axioms tendsto_standardGaussianMehlerAverage_signed_square_entropy_nhds_zero

end LOOConcentration.Examples.GaussianLipschitzEnergy
