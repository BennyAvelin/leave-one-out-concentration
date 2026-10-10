import LOOConcentration.Examples.GaussianMehlerBoundedLSI
import LOOConcentration.Examples.GaussianMehlerEntropy
import LOOConcentration.Examples.GaussianMehlerEnergy
import Mathlib.Tactic

set_option autoImplicit false

namespace LOOConcentration

open MeasureTheory
open scoped NNReal

/-- The bounded-positive smooth scalar Gaussian log-Sobolev inequality, with
the entropy and Gaussian law in the source normalization. The proof uses the
canonical Mehler entropy only at nonnegative times. Its private real-time
trajectory is totalized through `Real.toNNReal`; negative inputs therefore
use the valid time zero kernel and carry no negative-time Mehler semantics. -/
theorem standardGaussian_boundedPositive_scalar_logSobolev
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {ε B M₁ M₂ : ℝ} (hε : 0 < ε)
    (hsource : ∀ x, ε ≤ f x ∧ f x ≤ B)
    (hderiv_bound : ∀ x, ‖deriv f x‖ ≤ M₁)
    (hsecond_bound : ∀ x, ‖deriv (deriv f) x‖ ≤ M₂) :
    Integrable (fun x => (deriv f x) ^ 2 / f x) standardGaussianMehler ∧
      looconcentrationEntropy standardGaussianMehler f ≤
        (1 / 2 : ℝ) *
          (∫ x, (deriv f x) ^ 2 / f x ∂standardGaussianMehler) := by
  have hbounded : ∀ x, ‖f x‖ ≤ B := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (le_trans hε.le (hsource x).1)]
    exact (hsource x).2
  let P : ℝ → ℝ → ℝ := fun t x =>
    standardGaussianMehlerAverage f hf.continuous.measurable ⟨B, hbounded⟩
      (Real.toNNReal t) (Real.toNNReal t).property x
  let ψ : ℝ → ℝ := fun t =>
    looconcentrationEntropy standardGaussianMehler (P t)
  let energy : ℝ → ℝ := fun t =>
    ∫ x, (deriv (P t) x) ^ 2 / P t x ∂standardGaussianMehler
  let sourceEnergy : ℝ :=
    ∫ x, (deriv f x) ^ 2 / f x ∂standardGaussianMehler

  have hPvalid (t : ℝ) (ht : 0 ≤ t) :
      P t = standardGaussianMehlerAverage f hf.continuous.measurable
        ⟨B, hbounded⟩ t ht := by
    have htime : (Real.toNNReal t : ℝ) = t := Real.coe_toNNReal t ht
    funext x
    unfold P standardGaussianMehlerAverage
    apply integral_congr_ae
    filter_upwards [] with y
    rw [htime]

  have hvalidPath (t : ℝ) (ht : 0 ≤ t) :
      ψ t = looconcentrationEntropy standardGaussianMehler
        (standardGaussianMehlerAverage f hf.continuous.measurable
          ⟨B, hbounded⟩ t ht) := by
    change looconcentrationEntropy standardGaussianMehler (P t) = _
    exact congrArg (looconcentrationEntropy standardGaussianMehler) (hPvalid t ht)

  have htopPath (t : ℝ) (_ht : 0 ≤ t) :
      ψ t = looconcentrationEntropy standardGaussianMehler
        (standardGaussianMehlerAverage f hf.continuous.measurable
          ⟨B, hbounded⟩ (Real.toNNReal t) (Real.toNNReal t).property) := by
    rfl

  have hweighted (t : ℝ) (ht : 0 ≤ t) :=
    standardGaussianMehlerAverage_weighted_energy_decay
      (hf.of_le (by norm_num)) hε
      (fun x => (hsource x).1) (fun x => (hsource x).2)
      hderiv_bound t ht

  have hsourceEnergy_integrable :
      Integrable (fun x => (deriv f x) ^ 2 / f x) standardGaussianMehler := by
    simpa using (hweighted 0 le_rfl).1

  have hcanonicalPath (s : ℝ) (hs : 0 < s) :
      ψ s = Examples.GaussianMehlerEntropy.standardGaussianMehlerEntropy
        f hf.continuous.measurable
        B ε hbounded hε (fun x => (hsource x).1) s (le_of_lt hs) := by
    simpa [Examples.GaussianMehlerEntropy.standardGaussianMehlerEntropy] using
      hvalidPath s hs.le

  have henergyEq (t : ℝ) (ht : 0 ≤ t) :
      energy t =
        (∫ x,
          (deriv (standardGaussianMehlerAverage f hf.continuous.measurable
            ⟨B, hbounded⟩ t ht) x) ^ 2 /
            standardGaussianMehlerAverage f hf.continuous.measurable
              ⟨B, hbounded⟩ t ht x ∂standardGaussianMehler) := by
    change (∫ x, (deriv (P t) x) ^ 2 / P t x
      ∂standardGaussianMehler) = _
    rw [hPvalid t ht]

  have hdissipation (t : ℝ) (ht : 0 < t) :
      HasDerivAt ψ (-energy t) t := by
    have hactual :=
      Examples.GaussianMehlerEntropy.standardGaussianMehler_entropy_dissipation_hasDerivAt
      hf B M₁ M₂ ε hbounded hderiv_bound hsecond_bound hε
      (fun x => (hsource x).1) ht ψ hcanonicalPath
    have hvalue :
        -(∫ x,
          (deriv (standardGaussianMehlerAverage f hf.continuous.measurable
            ⟨B, hbounded⟩ t (le_of_lt ht)) x) ^ 2 /
            standardGaussianMehlerAverage f hf.continuous.measurable
              ⟨B, hbounded⟩ t (le_of_lt ht) x ∂standardGaussianMehler) =
          -energy t := by
      rw [← henergyEq t (le_of_lt ht)]
    exact hactual.congr_deriv hvalue

  have henergy_decay (t : ℝ) (ht : 0 < t) :
      energy t ≤ Real.exp (-2 * t) * sourceEnergy := by
    have hdecay := (hweighted t ht.le).2.2
    calc
      energy t =
          (∫ x,
            (deriv (standardGaussianMehlerAverage f hf.continuous.measurable
              ⟨B, hbounded⟩ t (le_of_lt ht)) x) ^ 2 /
              standardGaussianMehlerAverage f hf.continuous.measurable
                ⟨B, hbounded⟩ t (le_of_lt ht) x ∂standardGaussianMehler) :=
        henergyEq t (le_of_lt ht)
      _ ≤ Real.exp (-2 * t) * sourceEnergy := by
        simpa [sourceEnergy] using hdecay

  obtain ⟨htrajectory_continuous, hinitial⟩ :=
    standardGaussianMehlerEntropyTrajectory_continuousOn_nonneg
      hf.continuous hε (fun x => (hsource x).1) (fun x => (hsource x).2)
      ψ hvalidPath (fun t ht => (hdissipation t ht).differentiableAt)

  have hequilibrium := tendsto_standardGaussianMehlerEntropyTrajectory_atTop
    hf.continuous hε (fun x => (hsource x).1) (fun x => (hsource x).2)
    ψ htopPath

  have hscalar := scalarEntropy_le_half_of_dissipation_and_energy_decay
    htrajectory_continuous hdissipation henergy_decay hequilibrium
  refine ⟨hsourceEnergy_integrable, ?_⟩
  calc
    looconcentrationEntropy standardGaussianMehler f = ψ 0 := hinitial.symm
    _ ≤ sourceEnergy / 2 := hscalar
    _ = (1 / 2 : ℝ) *
        (∫ x, (deriv f x) ^ 2 / f x ∂standardGaussianMehler) := by
          simp only [sourceEnergy]
          ring

#print axioms standardGaussian_boundedPositive_scalar_logSobolev

end LOOConcentration
