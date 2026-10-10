import LOOConcentration.Examples.GaussianBoundedSmoothLSI
import LOOConcentration.Examples.GaussianLipschitzEnergy
import LOOConcentration.Examples.GaussianLipschitzMehlerC2
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic

/-!
# The scalar Gaussian log-Sobolev inequality for bounded Lipschitz data

Positive-time canonical Mehler averages are treated by the accepted C²
regularizer and bounded smooth inequality. The signed energy contraction and
actual entropy endpoint then pass the estimate to the original bounded
Lipschitz input, including inputs with zeros.
-/

set_option autoImplicit false

namespace LOOConcentration.Examples.GaussianBoundedLipschitzLSI

open MeasureTheory
open Filter
open scoped Topology NNReal

noncomputable abbrev γ : Measure ℝ := LOOConcentration.standardGaussianMehler

private noncomputable def xLogX (z : ℝ) : ℝ := z * Real.log z

/-- The actual standard Gaussian scalar log-Sobolev inequality for a signed
bounded globally Lipschitz function. The displayed integrability conclusions
are proved as part of the theorem, and no nonzero or positive-lower-bound
condition is imposed. -/
theorem standardGaussian_boundedLipschitz_square_logSobolev
    {u : ℝ → ℝ} {B K : ℝ≥0}
    (hu : LipschitzWith K u)
    (hu_bounded : ∀ x, ‖u x‖ ≤ (B : ℝ)) :
    Integrable (fun x => (u x) ^ 2) γ ∧
      Integrable (fun x => (u x) ^ 2 * Real.log ((u x) ^ 2)) γ ∧
      Integrable (fun x => (deriv u x) ^ 2) γ ∧
      LOOConcentration.looconcentrationEntropy γ (fun x => (u x) ^ 2) ≤
        2 * (∫ x, (deriv u x) ^ 2 ∂γ) := by
  let hb : ∃ M : ℝ, ∀ x, ‖u x‖ ≤ M := ⟨(B : ℝ), hu_bounded⟩
  let P : ℝ≥0 → ℝ → ℝ := fun t =>
    LOOConcentration.standardGaussianMehlerAverage u hu.continuous.measurable hb
      (t : ℝ) t.property
  let sourceEnergy : ℝ := ∫ x, (deriv u x) ^ 2 ∂γ
  have hBnonneg : 0 ≤ (B : ℝ) := B.coe_nonneg
  have huAbs (x : ℝ) : |u x| ≤ (B : ℝ) := by
    simpa [Real.norm_eq_abs] using hu_bounded x
  have huSqBound (x : ℝ) : (u x) ^ 2 ≤ (B : ℝ) ^ 2 := by
    simpa [pow_two] using
      (mul_self_le_mul_self (abs_nonneg (u x)) (huAbs x))
  have huSqMeas : Measurable (fun x : ℝ => (u x) ^ 2) :=
    (hu.continuous.pow 2).measurable
  have huSqInt : Integrable (fun x : ℝ => (u x) ^ 2) γ := by
    refine (integrable_const ((B : ℝ) ^ 2)).mono'
      huSqMeas.aestronglyMeasurable ?_
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact huSqBound x
  have hlogCont : Continuous xLogX := by
    unfold xLogX
    exact Real.continuous_mul_log
  have hlogNormCont : ContinuousOn (fun z : ℝ => ‖xLogX z‖)
      (Set.Icc (0 : ℝ) ((B : ℝ) ^ 2)) :=
    hlogCont.norm.continuousOn
  obtain ⟨L, hL⟩ :=
    isCompact_Icc.bddAbove_image hlogNormCont
  have hlogRange (x : ℝ) :
      (u x) ^ 2 ∈ Set.Icc (0 : ℝ) ((B : ℝ) ^ 2) :=
    ⟨sq_nonneg _, huSqBound x⟩
  have hlogMeas : Measurable (fun x : ℝ => xLogX ((u x) ^ 2)) :=
    hlogCont.measurable.comp huSqMeas
  have hlogBound (x : ℝ) : ‖xLogX ((u x) ^ 2)‖ ≤ L :=
    hL (Set.mem_image_of_mem _ (hlogRange x))
  have huLogSqInt :
      Integrable (fun x : ℝ => (u x) ^ 2 * Real.log ((u x) ^ 2)) γ := by
    have h := Integrable.of_bound hlogMeas.aestronglyMeasurable L
      (ae_of_all γ hlogBound)
    simpa [xLogX] using h
  have hEnergyOne :=
    LOOConcentration.Examples.GaussianLipschitzEnergy.standardGaussianMehlerAverage_signed_square_energy_decay_of_lipschitz
      hu hb (t := 1) (by norm_num)
  have huDerivSqInt : Integrable (fun x : ℝ => (deriv u x) ^ 2) γ := by
    simpa [γ] using hEnergyOne.1
  have hpositiveSmoothLSI (t : ℝ≥0) (ht : 0 < t) :
      LOOConcentration.looconcentrationEntropy γ (fun x => (P t x) ^ 2) ≤
        2 * (∫ x, (deriv (P t) x) ^ 2 ∂γ) := by
    have hC2 := LOOConcentration.standardGaussianMehlerAverage_boundedLipschitz_C2
      (u := u) (B := B) (K := K) hu hu_bounded
      (t := (t : ℝ)) (by exact_mod_cast ht)
    have hC2' : ContDiff ℝ 2 (P t) ∧
        (∀ x, ‖P t x‖ ≤ (B : ℝ)) ∧
        (∀ x, ‖deriv (P t) x‖ ≤ Real.exp (-(t : ℝ)) * (K : ℝ)) ∧
        (∀ x, ‖deriv (deriv (P t)) x‖ ≤
          (Real.exp (-(t : ℝ)) ^ 2 /
            Real.sqrt (1 - Real.exp (-2 * (t : ℝ)))) *
              (K : ℝ) * ∫ y, |y| ∂LOOConcentration.standardGaussianMehler) := by
      simpa [P, hb, γ] using hC2
    have hsmooth := LOOConcentration.standardGaussian_boundedSmooth_square_logSobolev
      hC2'.1 hC2'.2.1 hC2'.2.2.1 hC2'.2.2.2
    simpa [γ] using hsmooth.2.2.2
  have henergyAt (t : ℝ≥0) (ht : 0 < t) :
      (∫ x, (deriv (P t) x) ^ 2 ∂γ) ≤
        Real.exp (-2 * (t : ℝ)) * sourceEnergy := by
    have h :=
      LOOConcentration.Examples.GaussianLipschitzEnergy.standardGaussianMehlerAverage_signed_square_energy_decay_of_lipschitz
        hu hb (t := (t : ℝ)) (by exact_mod_cast ht)
    simpa [P, hb, sourceEnergy, γ] using h.2.2
  have hentropyBound (t : ℝ≥0) (ht : 0 < t) :
      LOOConcentration.looconcentrationEntropy γ (fun x => (P t x) ^ 2) ≤
        2 * (Real.exp (-2 * (t : ℝ)) * sourceEnergy) := by
    calc
      LOOConcentration.looconcentrationEntropy γ (fun x => (P t x) ^ 2) ≤
          2 * (∫ x, (deriv (P t) x) ^ 2 ∂γ) :=
        hpositiveSmoothLSI t ht
      _ ≤ 2 * (Real.exp (-2 * (t : ℝ)) * sourceEnergy) :=
        mul_le_mul_of_nonneg_left (henergyAt t ht) (by norm_num)
  have hEndpoint :=
    LOOConcentration.Examples.GaussianLipschitzEnergy.tendsto_standardGaussianMehlerAverage_signed_square_entropy_nhds_zero
      hu hb
  have hEntropyLimit :
      Tendsto (fun t : ℝ≥0 => LOOConcentration.looconcentrationEntropy γ
        (fun x => (P t x) ^ 2)) (𝓝 (0 : ℝ≥0))
        (𝓝 (LOOConcentration.looconcentrationEntropy γ (fun x => (u x) ^ 2))) := by
    simpa [P, hb, γ] using hEndpoint.2.2
  have hcoe : Tendsto (fun t : ℝ≥0 => (t : ℝ))
      (𝓝 (0 : ℝ≥0)) (𝓝 0) := continuous_subtype_val.continuousAt.tendsto
  have hexpArg : Tendsto (fun t : ℝ≥0 => -2 * (t : ℝ))
      (𝓝 (0 : ℝ≥0)) (𝓝 0) := by
    simpa using hcoe.const_mul (-2 : ℝ)
  have hexp : Tendsto (fun t : ℝ≥0 => Real.exp (-2 * (t : ℝ)))
      (𝓝 (0 : ℝ≥0)) (𝓝 (1 : ℝ)) := by
    convert Real.continuous_exp.continuousAt.tendsto.comp hexpArg using 1
    · ext t
      congr 1
    · simp
  have hright : Tendsto
      (fun t : ℝ≥0 => 2 * (Real.exp (-2 * (t : ℝ)) * sourceEnergy))
      (𝓝 (0 : ℝ≥0)) (𝓝 (2 * sourceEnergy)) := by
    simpa using (hexp.mul_const sourceEnergy).const_mul (2 : ℝ)
  have hEntropyPos := hEntropyLimit.mono_left
    (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ≥0)))
  have hrightPos := hright.mono_left
    (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ≥0)))
  have hboundEventually :
      (fun t : ℝ≥0 => LOOConcentration.looconcentrationEntropy γ (fun x => (P t x) ^ 2)) ≤ᶠ[
        𝓝[>] (0 : ℝ≥0)]
        (fun t => 2 * (Real.exp (-2 * (t : ℝ)) * sourceEnergy)) := by
    filter_upwards
      [eventually_mem_nhdsWithin (a := (0 : ℝ≥0))
        (s := Set.Ioi (0 : ℝ≥0))] with t ht
    exact hentropyBound t ht
  have hfinal :=
    le_of_tendsto_of_tendsto hEntropyPos hrightPos hboundEventually
  refine ⟨huSqInt, huLogSqInt, huDerivSqInt, ?_⟩
  simpa [sourceEnergy] using hfinal

#print axioms standardGaussian_boundedLipschitz_square_logSobolev

end LOOConcentration.Examples.GaussianBoundedLipschitzLSI
