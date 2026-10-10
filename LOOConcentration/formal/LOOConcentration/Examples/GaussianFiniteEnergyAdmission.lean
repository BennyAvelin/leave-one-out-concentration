import LOOConcentration.Examples.GaussianSlopeTruncationAdmission
import LOOConcentration.FunctionalInequalities.BoundedTestPoincare
import LOOConcentration.Analysis.TruncationSquareAdmission
import LOOConcentration.Analysis.TruncationEntropyAdmission
import LOOConcentration.Frozen.FunctionalInequalities.HasLogSobolev
import Mathlib.Tactic

set_option autoImplicit false

open Filter MeasureTheory
open scoped Topology

namespace LOOConcentration

/-- The literal clip subtype and the scalar truncation used by the square
admission module have exactly the same underlying function at radius `n+1`.
-/
private theorem clippedObservationFunction_eq_finiteEnergyTruncation
    (u : GaussianObservationTest) (n : ℕ) (z : Observation 1 1) :
    (clippedObservationFunction u ((n : ℝ) + 1)).1 z =
      finiteEnergyTruncation u.1 n z := by
  rfl

/-- The entropy admission module's literal squared clip is the square of that
same `n+1` finite-energy truncation.
-/
private theorem entropyClipSquare_eq_finiteEnergyTruncation_sq
    (u : GaussianObservationTest) (n : ℕ) :
    entropyClipSquare u.1 n = fun z => finiteEnergyTruncation u.1 n z ^ 2 := by
  funext z
  rfl

/-- Conditional finite-energy admission on the actual frozen Observation(1,1)
Gaussian carrier. The only analytic premise is the literal bounded locally
Lipschitz entropy inequality at constant one. This assembles the accepted
bounded Poincaré, square admission, and entropy admission steps; it does not
produce that bounded-class inequality.
-/
theorem gaussianObservationLaw_hasLogSobolev_of_boundedEntropy
    (hBoundedEntropy :
      ∀ (v : {g : Observation 1 1 → ℝ //
        ∀ z, ∃ U ∈ 𝓝 z, ∃ K : ℝ, 0 ≤ K ∧
          ∀ w ∈ U, ∀ y ∈ U,
            |g w - g y| ≤ K * observationNorm (w - y)}) (B : ℝ),
        (∀ z, |v.1 z| ≤ B) →
        Integrable (fun z => observationLocalSlope v z ^ 2)
          gaussianObservationLaw →
        (∫ z, v.1 z ^ 2 * Real.log (v.1 z ^ 2) ∂gaussianObservationLaw) -
            (∫ z, v.1 z ^ 2 ∂gaussianObservationLaw) *
              Real.log (∫ z, v.1 z ^ 2 ∂gaussianObservationLaw) ≤
          2 * 1 *
            (∫ z, observationLocalSlope v z ^ 2 ∂gaussianObservationLaw)) :
    @HasLogSobolev 0 0 gaussianObservationLaw
      gaussianObservationLaw_isProbability 1 := by
  unfold HasLogSobolev
  refine ⟨by norm_num, ?_⟩
  intro u hEnergy
  let E : ℝ := ∫ z, observationLocalSlope u z ^ 2 ∂gaussianObservationLaw
  have hE_nonneg : 0 ≤ E := by
    dsimp [E]
    exact integral_nonneg fun z => sq_nonneg _
  have huMeas : Measurable u.1 := (oneObservationLip_continuous u).measurable
  have hPoincare := @boundedTestPoincare_of_boundedEntropy
    0 0 gaussianObservationLaw gaussianObservationLaw_isProbability 1
    (by norm_num) hBoundedEntropy
  have hVariance : ∀ n,
      finiteEnergyTruncationVariance gaussianObservationLaw u.1 n ≤ E := by
    intro n
    let cap : ℝ := (n : ℝ) + 1
    let v : GaussianObservationTest := clippedObservationFunction u cap
    have hcap : 0 < cap := by
      dsimp [cap]
      positivity
    have hvBound : ∀ z, |v.1 z| ≤ cap := by
      intro z
      simpa [v] using clippedObservationFunction_abs_le u hcap z
    have hClipEnergy := clippedObservationFunction_energy_admission
      u (A := cap) hEnergy
    have hvEnergy : Integrable
        (fun z => observationLocalSlope v z ^ 2) gaussianObservationLaw := by
      simpa [v, cap] using hClipEnergy.1
    have hvEnergyLe :
        (∫ z, observationLocalSlope v z ^ 2 ∂gaussianObservationLaw) ≤ E := by
      simpa [v, cap, E] using hClipEnergy.2
    have hvEq (z : Observation 1 1) :
        v.1 z = finiteEnergyTruncation u.1 n z := by
      simpa [v, cap] using
        clippedObservationFunction_eq_finiteEnergyTruncation u n z
    have hp := hPoincare v cap hvBound hvEnergy
    have hmeanEq :
        (∫ z, finiteEnergyTruncation u.1 n z ∂gaussianObservationLaw) =
          ∫ z, v.1 z ∂gaussianObservationLaw := by
      apply integral_congr_ae
      filter_upwards [] with z
      exact (hvEq z).symm
    change
      (∫ z, (finiteEnergyTruncation u.1 n z -
        ∫ y, finiteEnergyTruncation u.1 n y ∂gaussianObservationLaw) ^ 2
        ∂gaussianObservationLaw) ≤ E
    calc
      _ = ∫ z, (v.1 z - ∫ y, v.1 y ∂gaussianObservationLaw) ^ 2
          ∂gaussianObservationLaw := by
        apply integral_congr_ae
        filter_upwards [] with z
        rw [hvEq z, hmeanEq]
      _ ≤ 1 *
          (∫ z, observationLocalSlope v z ^ 2 ∂gaussianObservationLaw) := hp.2
      _ = ∫ z, observationLocalSlope v z ^ 2 ∂gaussianObservationLaw := by ring
      _ ≤ E := hvEnergyLe
  have huSq : Integrable (fun z => u.1 z ^ 2) gaussianObservationLaw :=
    @integrable_sq_of_uniform_finiteEnergyTruncationVariance
      (Observation 1 1) inferInstance gaussianObservationLaw
      gaussianObservationLaw_isProbability u.1 huMeas E hE_nonneg hVariance
  have hClipEntropy : ∀ n,
      looconcentrationEntropy gaussianObservationLaw (entropyClipSquare u.1 n) ≤ 2 * E := by
    intro n
    let cap : ℝ := (n : ℝ) + 1
    let v : GaussianObservationTest := clippedObservationFunction u cap
    have hcap : 0 < cap := by
      dsimp [cap]
      positivity
    have hvBound : ∀ z, |v.1 z| ≤ cap := by
      intro z
      simpa [v] using clippedObservationFunction_abs_le u hcap z
    have hClipEnergy := clippedObservationFunction_energy_admission
      u (A := cap) hEnergy
    have hvEnergy : Integrable
        (fun z => observationLocalSlope v z ^ 2) gaussianObservationLaw := by
      simpa [v, cap] using hClipEnergy.1
    have hvEnergyLe :
        (∫ z, observationLocalSlope v z ^ 2 ∂gaussianObservationLaw) ≤ E := by
      simpa [v, cap, E] using hClipEnergy.2
    have hRaw := hBoundedEntropy v cap hvBound hvEnergy
    have hRaw' :
        (∫ z, v.1 z ^ 2 * Real.log (v.1 z ^ 2) ∂gaussianObservationLaw) -
            (∫ z, v.1 z ^ 2 ∂gaussianObservationLaw) *
              Real.log (∫ z, v.1 z ^ 2 ∂gaussianObservationLaw) ≤
          2 * (∫ z, observationLocalSlope v z ^ 2 ∂gaussianObservationLaw) := by
      norm_num at hRaw ⊢
      exact hRaw
    have hvEq (z : Observation 1 1) :
        v.1 z = finiteEnergyTruncation u.1 n z := by
      simpa [v, cap] using
        clippedObservationFunction_eq_finiteEnergyTruncation u n z
    have hEntropyEq :
        looconcentrationEntropy gaussianObservationLaw (entropyClipSquare u.1 n) =
          (∫ z, v.1 z ^ 2 * Real.log (v.1 z ^ 2) ∂gaussianObservationLaw) -
            (∫ z, v.1 z ^ 2 ∂gaussianObservationLaw) *
              Real.log (∫ z, v.1 z ^ 2 ∂gaussianObservationLaw) := by
      unfold looconcentrationEntropy
      have hSqEq : entropyClipSquare u.1 n = fun z => v.1 z ^ 2 := by
        rw [entropyClipSquare_eq_finiteEnergyTruncation_sq]
        funext z
        rw [hvEq z]
      rw [hSqEq]
    rw [hEntropyEq]
    calc
      _ ≤ 2 *
          (∫ z, observationLocalSlope v z ^ 2 ∂gaussianObservationLaw) := hRaw'
      _ ≤ 2 * E := mul_le_mul_of_nonneg_left hvEnergyLe (by norm_num)
  have hEntropyAdmission :=
    @integrable_mulLogKernel_of_uniform_entropyClip_bound
      (Observation 1 1) inferInstance gaussianObservationLaw
      gaussianObservationLaw_isProbability u.1 huMeas huSq (2 * E) hClipEntropy
  refine ⟨huSq, hEntropyAdmission.1, ?_⟩
  simpa [looconcentrationEntropy, E] using hEntropyAdmission.2

#print axioms gaussianObservationLaw_hasLogSobolev_of_boundedEntropy

end LOOConcentration
