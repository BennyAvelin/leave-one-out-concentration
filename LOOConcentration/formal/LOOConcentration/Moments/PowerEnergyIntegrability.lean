import LOOConcentration.Moments.PowerTestEnergy
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Finite energy for regularized power tests

On a probability space, an integrable `p`-power of a nonnegative measurable
slope controls its square for `p ≥ 2`. The reviewed regularized-power chain
bound then gives a concrete squared-slope majorant on the bounded range of the
original test function. Measurability of the transformed squared slope is an
explicit predecessor, as its smooth-slope producer is handled separately.
-/

set_option autoImplicit false

open MeasureTheory
open scoped Topology

namespace LOOConcentration

private theorem sq_le_one_add_rpow {x p : ℝ} (hx : 0 ≤ x) (hp : 2 ≤ p) :
    x ^ 2 ≤ 1 + x ^ p := by
  by_cases hxle : x ≤ 1
  · have hx2 : x ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg hx (sub_nonneg.mpr hxle)]
    have hpow : 0 ≤ x ^ p := Real.rpow_nonneg hx p
    nlinarith
  · have hxone : 1 ≤ x := le_of_not_ge hxle
    calc
      x ^ 2 = x ^ (2 : ℝ) := (Real.rpow_two x).symm
      _ ≤ x ^ p := Real.rpow_le_rpow_of_exponent_le hxone hp
      _ ≤ 1 + x ^ p := by nlinarith [Real.rpow_nonneg hx p]

/-- On a probability space, finite `p`-energy of a nonnegative measurable
slope implies finite squared energy whenever `p ≥ 2`. The proof uses the
actual input integrability through the majorant `1 + S^p`. -/
theorem integrable_sq_of_integrable_rpow
    {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsProbabilityMeasure ν]
    (S : α → ℝ) (hSmeas : Measurable S) (hSnonneg : ∀ x, 0 ≤ S x)
    (p : ℝ) (hp : 2 ≤ p)
    (hLp : Integrable (fun x => S x ^ p) ν) :
    Integrable (fun x => S x ^ 2) ν := by
  have hconstant : Integrable (fun _ : α => (1 : ℝ)) ν := integrable_const 1
  have hmajor : Integrable (fun x => 1 + S x ^ p) ν := hconstant.add hLp
  apply hmajor.mono' (hSmeas.pow_const 2).aestronglyMeasurable
  filter_upwards with x
  have hpoint := sq_le_one_add_rpow (hSnonneg x) hp
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (S x))]
  exact hpoint

/-- The exact scalar multiplier in the reviewed wave-6 local-slope chain
bound for the regularized power test. -/
noncomputable def regularizedPowerChainMultiplier (q ε x : ℝ) : ℝ :=
  q / 2 * |x| * (x ^ 2 + ε) ^ (q / 4 - 1)

private theorem continuous_regularizedPowerChainMultiplier (q ε : ℝ)
    (hε : 0 < ε) : Continuous (regularizedPowerChainMultiplier q ε) := by
  unfold regularizedPowerChainMultiplier
  have hbase : Continuous (fun x : ℝ => x ^ 2 + ε) :=
    (continuous_id.pow 2).add continuous_const
  have hpow : Continuous (fun x : ℝ => (x ^ 2 + ε) ^ (q / 4 - 1)) :=
    hbase.rpow_const (fun x => Or.inl (ne_of_gt (by positivity)))
  have hcoeff : Continuous (fun _ : ℝ => q / 2) := continuous_const
  exact (hcoeff.mul continuous_abs).mul hpow

/-- The exact multiplier has a finite nonnegative uniform bound on every
bounded interval when `ε > 0` and `q ≥ 2`. In particular this includes `q=2`
and the point `x=0`. -/
theorem regularizedPowerChainMultiplier_bounded_on_Icc
    (q ε B : ℝ) (hq : 2 ≤ q) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ x ∈ Set.Icc (-B) B,
        0 ≤ regularizedPowerChainMultiplier q ε x ∧
          regularizedPowerChainMultiplier q ε x ≤ K := by
  let f : ℝ → ℝ := regularizedPowerChainMultiplier q ε
  have hf : Continuous f := by
    simpa [f] using continuous_regularizedPowerChainMultiplier q ε hε
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Set.Icc (-B) B) hf.continuousOn
  let K := max C 0
  refine ⟨K, le_max_right _ _, ?_⟩
  intro x hx
  have hqnonneg : 0 ≤ q / 2 := by linarith
  have hpow : 0 ≤ (x ^ 2 + ε) ^ (q / 4 - 1) :=
    Real.rpow_nonneg (by positivity) _
  have hmultnonneg : 0 ≤ regularizedPowerChainMultiplier q ε x := by
    unfold regularizedPowerChainMultiplier
    exact mul_nonneg (mul_nonneg hqnonneg (abs_nonneg _)) hpow
  have hfx : ‖f x‖ ≤ K := (hC x hx).trans (le_max_left C 0)
  exact ⟨hmultnonneg, (Real.le_norm_self (f x)).trans hfx⟩

/-- Finite-energy admission for the regularized power test, conditional only
on the explicit AE measurability predecessor for its transformed squared
slope. The source slope's actual `L^p` integrability is converted to `L^2`
energy here; the reviewed wave-6 chain rule and compact multiplier bound then
give the displayed concrete energy majorant. -/
theorem integrable_regularizedPowerTest_slope_sq_of_aestronglyMeasurable
    {k m n : ℕ} (g : LocallyLipschitzDataFunction k m n)
    {ν : Measure (DataCarrier k m n)} [IsProbabilityMeasure ν]
    (p q ε B : ℝ) (hB : 0 ≤ B) (hBound : ∀ D, |g.1 D| ≤ B)
    (hε : 0 < ε) (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hSlopeMeas : Measurable (fun D => datasetLocalSlope g D))
    (hLp : Integrable (fun D => datasetLocalSlope g D ^ p) ν)
    (hPowerSlopeAEStronglyMeasurable :
      AEStronglyMeasurable
        (fun D => datasetLocalSlope
          (regularizedPowerTestFunction g q ε B hB hBound hε) D ^ 2) ν) :
    Integrable
      (fun D => datasetLocalSlope
        (regularizedPowerTestFunction g q ε B hB hBound hε) D ^ 2) ν := by
  let S : DataCarrier k m n → ℝ := fun D => datasetLocalSlope g D
  let T : DataCarrier k m n → ℝ := fun D =>
    datasetLocalSlope (regularizedPowerTestFunction g q ε B hB hBound hε) D
  obtain ⟨K, hK, hMultiplierBound⟩ :=
    regularizedPowerChainMultiplier_bounded_on_Icc q ε B hq hε
  have hSsq : Integrable (fun D => S D ^ 2) ν := by
    apply integrable_sq_of_integrable_rpow S ?_ ?_ p hp ?_
    · simpa [S] using hSlopeMeas
    · intro D
      exact datasetLocalSlope_nonneg g D
    · simpa [S] using hLp
  have hmajor : Integrable (fun D => K ^ 2 * S D ^ 2) ν := by
    exact hSsq.const_mul (K ^ 2)
  have hpoint : ∀ D, T D ^ 2 ≤ K ^ 2 * S D ^ 2 := by
    intro D
    have hD : g.1 D ∈ Set.Icc (-B) B := by
      rw [Set.mem_Icc, ← abs_le]
      exact hBound D
    have hmult := (hMultiplierBound (g.1 D) hD).2
    have hchain := datasetLocalSlope_regularizedPowerTestFunction_le
      g q ε B hB hBound hε hq D
    have hSnonneg : 0 ≤ S D := by
      exact datasetLocalSlope_nonneg g D
    have hTnonneg : 0 ≤ T D := by
      exact datasetLocalSlope_nonneg
        (regularizedPowerTestFunction g q ε B hB hBound hε) D
    have hupper : T D ≤ K * S D := by
      calc
        T D ≤ regularizedPowerChainMultiplier q ε (g.1 D) * S D := by
          simpa [T, S, regularizedPowerChainMultiplier] using hchain
        _ ≤ K * S D := mul_le_mul_of_nonneg_right hmult hSnonneg
    calc
      T D ^ 2 ≤ (K * S D) ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hupper)
          (add_nonneg (mul_nonneg hK hSnonneg) hTnonneg)]
      _ = K ^ 2 * S D ^ 2 := by ring
  apply hmajor.mono' hPowerSlopeAEStronglyMeasurable
  filter_upwards with D
  have hnonneg : 0 ≤ T D ^ 2 := sq_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact hpoint D

#print axioms integrable_sq_of_integrable_rpow
#print axioms regularizedPowerChainMultiplier_bounded_on_Icc
#print axioms integrable_regularizedPowerTest_slope_sq_of_aestronglyMeasurable

end LOOConcentration
