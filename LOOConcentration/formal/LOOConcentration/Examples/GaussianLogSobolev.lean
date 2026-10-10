import LOOConcentration.Examples.GaussianBoundedProductLSI
import LOOConcentration.Examples.GaussianBoundedLocalLSI
import LOOConcentration.Examples.GaussianFiniteEnergyAdmission

set_option autoImplicit false

open MeasureTheory
open scoped NNReal

namespace LOOConcentration

/-- The standard Gaussian law on the frozen `Observation 1 1` carrier has the
full finite-energy log-Sobolev property with constant one. The bounded
globally Lipschitz product core supplies the cutoff producer, and that actual
bounded-local inequality supplies finite-energy admission.
-/
theorem gaussianObservationLaw_hasLogSobolev :
    @HasLogSobolev 0 0 gaussianObservationLaw
      gaussianObservationLaw_isProbability 1 := by
  have hCore :
      ∀ (f : observation11EuclideanSpace → ℝ) (K : ℝ≥0) (B : ℝ),
        0 ≤ B → LipschitzWith K f → (∀ x, |f x| ≤ B) →
          looconcentrationEntropy standardGaussianObservationEuclideanLaw
              (fun x => f x ^ 2) ≤
            2 * (∫ x, ‖fderiv ℝ f x‖ ^ 2
              ∂standardGaussianObservationEuclideanLaw) := by
    intro f K B hB hf hbounded
    let Bnn : ℝ≥0 := ⟨B, hB⟩
    have hnormBound : ∀ x, ‖f x‖ ≤ (Bnn : ℝ) := by
      intro x
      change ‖f x‖ ≤ B
      rw [Real.norm_eq_abs]
      exact hbounded x
    have hProduct :=
      Examples.standardGaussian_observation_boundedLipschitz_square_logSobolev
        (B := Bnn) hf hnormBound
    simpa [standardGaussianObservationEuclideanLaw,
      observation11EuclideanSpace] using hProduct.2.2.2
  apply gaussianObservationLaw_hasLogSobolev_of_boundedEntropy
  intro u B huBound hEnergy
  have hLocal := gaussianObservation_boundedEntropy_of_boundedGlobalCore
    hCore u B huBound hEnergy
  simpa only [mul_one] using hLocal

#print axioms gaussianObservationLaw_hasLogSobolev

end LOOConcentration
