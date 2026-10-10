import LOOConcentration.Examples.GaussianSlopeTruncationAdmission
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Gaussian energy and entropy transport to Euclidean coordinates

The source carrier `Observation 1 1` is continuously linearly equivalent to
its flattened Euclidean coordinates. This module transports actual frozen
local-slope energy and the source square / square-log-square integrands through
the actual Gaussian pushforward. It does not assert square integrability of
an arbitrary unbounded test.
-/

set_option autoImplicit false

open MeasureTheory
open scoped Topology

namespace LOOConcentration

abbrev observation11EuclideanSpace :=
  EuclideanSpace ℝ (ObservationCoordinate 1 1)

noncomputable abbrev standardGaussianObservationEuclideanLaw : Measure observation11EuclideanSpace :=
  ProbabilityTheory.stdGaussian observation11EuclideanSpace

private def observation11Square (u : GaussianObservationTest) :
    Observation 1 1 → ℝ := fun z => u.1 z ^ 2

private def observation11EuclideanSquare (u : GaussianObservationTest) :
    observation11EuclideanSpace → ℝ := fun x =>
      (observation11EuclideanPullback u x) ^ 2

private noncomputable def observation11SquareLogSquare (u : GaussianObservationTest) :
    Observation 1 1 → ℝ := fun z => u.1 z ^ 2 * Real.log (u.1 z ^ 2)

private noncomputable def observation11EuclideanSquareLogSquare (u : GaussianObservationTest) :
    observation11EuclideanSpace → ℝ := fun x =>
      (observation11EuclideanPullback u x) ^ 2 *
        Real.log ((observation11EuclideanPullback u x) ^ 2)

private theorem observation11_gaussian_map_eq_standardGaussian :
    gaussianObservationLaw.map
        (observationToEuclidean : Observation 1 1 → observation11EuclideanSpace) =
      standardGaussianObservationEuclideanLaw := by
  exact gaussianObservationLaw_map_observationToEuclidean

private theorem observation11_integrable_pullback_iff
    {g : observation11EuclideanSpace → ℝ} (hg : Measurable g) :
    Integrable (fun z : Observation 1 1 =>
      g (observationToEuclidean z)) gaussianObservationLaw ↔
      Integrable g standardGaussianObservationEuclideanLaw := by
  have hmapMeas : AEStronglyMeasurable g
      (gaussianObservationLaw.map
        (observationToEuclidean : Observation 1 1 → observation11EuclideanSpace)) := by
    rw [observation11_gaussian_map_eq_standardGaussian]
    exact hg.aestronglyMeasurable
  calc
    Integrable (fun z : Observation 1 1 => g (observationToEuclidean z))
        gaussianObservationLaw ↔
      Integrable g (gaussianObservationLaw.map
        (observationToEuclidean : Observation 1 1 → observation11EuclideanSpace)) :=
      (integrable_map_measure hmapMeas
        observationCoordinateContinuousLinearEquiv.continuous.measurable.aemeasurable).symm
    _ ↔ Integrable g standardGaussianObservationEuclideanLaw := by
      rw [observation11_gaussian_map_eq_standardGaussian]

private theorem observation11_integral_pullback_eq
    {g : observation11EuclideanSpace → ℝ} (hg : Measurable g) :
    (∫ z : Observation 1 1, g (observationToEuclidean z) ∂gaussianObservationLaw) =
      ∫ x : observation11EuclideanSpace, g x ∂standardGaussianObservationEuclideanLaw := by
  have hmapMeas : AEStronglyMeasurable g
      (gaussianObservationLaw.map
        (observationToEuclidean : Observation 1 1 → observation11EuclideanSpace)) := by
    rw [observation11_gaussian_map_eq_standardGaussian]
    exact hg.aestronglyMeasurable
  calc
    (∫ z : Observation 1 1, g (observationToEuclidean z)
        ∂gaussianObservationLaw) =
      ∫ x : observation11EuclideanSpace, g x ∂gaussianObservationLaw.map
        (observationToEuclidean : Observation 1 1 → observation11EuclideanSpace) :=
      (integral_map
        observationCoordinateContinuousLinearEquiv.continuous.measurable.aemeasurable
        hmapMeas).symm
    _ = ∫ x : observation11EuclideanSpace, g x ∂standardGaussianObservationEuclideanLaw := by
      rw [observation11_gaussian_map_eq_standardGaussian]

/-- A locally Lipschitz Euclidean test pulls back to the exact frozen
observation test class, and flattening it recovers the original function. -/
theorem observation11EuclideanPullback_roundTrip
    (f : observation11EuclideanSpace → ℝ) (hf : LocallyLipschitz f) :
    observation11EuclideanPullback (locallyLipschitzObservationPullback f hf) = f := by
  funext x
  simp [observation11EuclideanPullback, locallyLipschitzObservationPullback]

/-- Pulling a frozen observation test back to coordinates and then using the
literal inverse coordinate map recovers its actual values on the observation
carrier. -/
theorem locallyLipschitzObservationPullback_roundTrip
    (u : GaussianObservationTest) :
    locallyLipschitzObservationPullback
      (observation11EuclideanPullback u)
      (observation11EuclideanPullback_locallyLipschitz u) = u := by
  apply Subtype.ext
  funext z
  simp [locallyLipschitzObservationPullback, observation11EuclideanPullback]

private theorem measurable_observation11EuclideanPullback_deriv
    (u : GaussianObservationTest) :
    Measurable (fun x : observation11EuclideanSpace =>
      fderiv ℝ (observation11EuclideanPullback u) x) := by
  have hobs := measurable_observation11EuclideanFDeriv u
  have hcomp := hobs.comp
    observationCoordinateContinuousLinearEquiv.symm.continuous.measurable
  have hinv (x : observation11EuclideanSpace) :
      observationToEuclidean (observationCoordinateContinuousLinearEquiv.symm x) = x :=
    observationCoordinateContinuousLinearEquiv.apply_symm_apply x
  have hEq :
      ((fun z : Observation 1 1 =>
        fderiv ℝ (observation11EuclideanPullback u)
          (observationToEuclidean z)) ∘
        observationCoordinateContinuousLinearEquiv.symm) =
      (fun x : observation11EuclideanSpace =>
        fderiv ℝ (observation11EuclideanPullback u) x) := by
    funext x
    change fderiv ℝ (observation11EuclideanPullback u)
        (observationToEuclidean (observationCoordinateContinuousLinearEquiv.symm x)) = _
    rw [hinv]
  rw [hEq] at hcomp
  exact hcomp

private theorem measurable_observation11Euclidean_deriv_sq
    (u : GaussianObservationTest) :
    Measurable (fun x : observation11EuclideanSpace =>
      ‖fderiv ℝ (observation11EuclideanPullback u) x‖ ^ 2) := by
  exact (continuous_norm.measurable.comp
    (measurable_observation11EuclideanPullback_deriv u)).pow_const 2

/-- Finite source squared-slope energy alone admits the full Euclidean
Fréchet derivative square as a genuinely integrable function under the actual
standard Gaussian. Its integral equals the source frozen-slope energy exactly.
No square-integrability premise on `u` is used. -/
theorem observation11EuclideanPullback_derivative_energy_transport
    (u : GaussianObservationTest)
    (hEnergy : Integrable (fun z : Observation 1 1 =>
      (observationLocalSlope u z) ^ 2) gaussianObservationLaw) :
    Integrable (fun x : observation11EuclideanSpace =>
      ‖fderiv ℝ (observation11EuclideanPullback u) x‖ ^ 2)
        standardGaussianObservationEuclideanLaw ∧
      (∫ x : observation11EuclideanSpace,
        ‖fderiv ℝ (observation11EuclideanPullback u) x‖ ^ 2
          ∂standardGaussianObservationEuclideanLaw) =
        ∫ z : Observation 1 1, (observationLocalSlope u z) ^ 2
          ∂gaussianObservationLaw := by
  let g : observation11EuclideanSpace → ℝ := fun x =>
    ‖fderiv ℝ (observation11EuclideanPullback u) x‖ ^ 2
  have hderivSqMeas : Measurable (fun z : Observation 1 1 =>
      ‖fderiv ℝ (observation11EuclideanPullback u)
        (observationToEuclidean z)‖ ^ 2) :=
    (continuous_norm.measurable.comp
      (measurable_observation11EuclideanFDeriv u)).pow_const 2
  have hderivEuMeas : Measurable g := by
    simpa only [g] using measurable_observation11Euclidean_deriv_sq u
  have hderivSqMapMeas : AEStronglyMeasurable g
      (gaussianObservationLaw.map
        (observationToEuclidean : Observation 1 1 → observation11EuclideanSpace)) := by
    rw [observation11_gaussian_map_eq_standardGaussian]
    exact hderivEuMeas.aestronglyMeasurable
  have hSlopeEq : (fun z : Observation 1 1 =>
      (observationLocalSlope u z) ^ 2) =ᵐ[gaussianObservationLaw]
      (fun z => ‖fderiv ℝ (observation11EuclideanPullback u)
        (observationToEuclidean z)‖ ^ 2) := by
    filter_upwards [ae_gaussianObservationLaw_observationLocalSlope_eq_fderiv u]
      with z hz
    rw [hz]
  have hPullbackEnergy : Integrable (fun z : Observation 1 1 =>
      ‖fderiv ℝ (observation11EuclideanPullback u)
        (observationToEuclidean z)‖ ^ 2) gaussianObservationLaw :=
    hEnergy.congr hSlopeEq
  have hPullbackEnergy' : Integrable (fun z : Observation 1 1 =>
      g (observationToEuclidean z)) gaussianObservationLaw := by
    exact hPullbackEnergy
  have hEuclideanEnergyMap : Integrable g
      (gaussianObservationLaw.map
        (observationToEuclidean : Observation 1 1 → observation11EuclideanSpace)) :=
    (integrable_map_measure hderivSqMapMeas
      observationCoordinateContinuousLinearEquiv.continuous.measurable.aemeasurable).2
        hPullbackEnergy'
  have hEuclideanEnergy : Integrable g standardGaussianObservationEuclideanLaw := by
    rw [← observation11_gaussian_map_eq_standardGaussian]
    exact hEuclideanEnergyMap
  refine ⟨by simpa [g] using hEuclideanEnergy, ?_⟩
  calc
    (∫ x : observation11EuclideanSpace, g x ∂standardGaussianObservationEuclideanLaw) =
      ∫ z : Observation 1 1, g (observationToEuclidean z)
        ∂gaussianObservationLaw := by
          rw [← observation11_gaussian_map_eq_standardGaussian]
          exact integral_map
            observationCoordinateContinuousLinearEquiv.continuous.measurable.aemeasurable
            hderivSqMapMeas
    _ = ∫ z : Observation 1 1, (observationLocalSlope u z) ^ 2
        ∂gaussianObservationLaw := by
          apply integral_congr_ae
          filter_upwards [hSlopeEq] with z hz
          exact hz.symm

private theorem measurable_observation11EuclideanSquare
    (u : GaussianObservationTest) :
    Measurable (observation11EuclideanSquare u) := by
  have hF : Continuous (observation11EuclideanPullback u) :=
    (observation11EuclideanPullback_locallyLipschitz u).continuous
  change Measurable (fun x : observation11EuclideanSpace =>
    (observation11EuclideanPullback u x) ^ 2)
  exact ((continuous_pow 2).comp hF).measurable

private theorem measurable_observation11EuclideanSquareLogSquare
    (u : GaussianObservationTest) :
    Measurable (observation11EuclideanSquareLogSquare u) := by
  have hF : Continuous (observation11EuclideanPullback u) :=
    (observation11EuclideanPullback_locallyLipschitz u).continuous
  have hSquare : Continuous (fun x : observation11EuclideanSpace =>
      (observation11EuclideanPullback u x) ^ 2) :=
    (continuous_pow 2).comp hF
  change Measurable (fun x : observation11EuclideanSpace =>
    (observation11EuclideanPullback u x) ^ 2 *
      Real.log ((observation11EuclideanPullback u x) ^ 2))
  exact (Real.continuous_mul_log.comp hSquare).measurable

private theorem observation11Square_comp_eq (u : GaussianObservationTest) :
    (fun z : Observation 1 1 =>
      observation11EuclideanSquare u (observationToEuclidean z)) =
        observation11Square u := by
  funext z
  simp [observation11EuclideanSquare, observation11Square,
    observation11EuclideanPullback]

private theorem observation11SquareLogSquare_comp_eq
    (u : GaussianObservationTest) :
    (fun z : Observation 1 1 =>
      observation11EuclideanSquareLogSquare u (observationToEuclidean z)) =
        observation11SquareLogSquare u := by
  funext z
  simp [observation11EuclideanSquareLogSquare, observation11SquareLogSquare,
    observation11EuclideanPullback]

/-- Square integrability transports in both directions between the actual
Gaussian observation law and its actual standard-Gaussian Euclidean image. -/
theorem integrable_gaussianObservation_square_iff
    (u : GaussianObservationTest) :
    Integrable (fun z : Observation 1 1 => u.1 z ^ 2) gaussianObservationLaw ↔
      Integrable (fun x : observation11EuclideanSpace =>
        (observation11EuclideanPullback u x) ^ 2)
          standardGaussianObservationEuclideanLaw := by
  change Integrable (observation11Square u) gaussianObservationLaw ↔
    Integrable (observation11EuclideanSquare u)
      standardGaussianObservationEuclideanLaw
  rw [← observation11Square_comp_eq u]
  exact observation11_integrable_pullback_iff
    (g := observation11EuclideanSquare u)
    (measurable_observation11EuclideanSquare u)

/-- The square integral is exactly preserved by the literal observation to
Euclidean coordinate map. -/
theorem integral_gaussianObservation_square_eq
    (u : GaussianObservationTest) :
    (∫ z : Observation 1 1, u.1 z ^ 2 ∂gaussianObservationLaw) =
      ∫ x : observation11EuclideanSpace,
        (observation11EuclideanPullback u x) ^ 2
          ∂standardGaussianObservationEuclideanLaw := by
  change (∫ z, observation11Square u z ∂gaussianObservationLaw) =
    ∫ x, observation11EuclideanSquare u x
      ∂standardGaussianObservationEuclideanLaw
  rw [← observation11Square_comp_eq u]
  exact observation11_integral_pullback_eq
    (g := observation11EuclideanSquare u)
    (measurable_observation11EuclideanSquare u)

/-- Absolute integrability of the actual `u² log(u²)` integrand transports
in both directions. Continuity at zero is supplied by `Real.continuous_mul_log`.
-/
theorem integrable_gaussianObservation_squareLogSquare_iff
    (u : GaussianObservationTest) :
    Integrable (fun z : Observation 1 1 =>
      u.1 z ^ 2 * Real.log (u.1 z ^ 2)) gaussianObservationLaw ↔
      Integrable (fun x : observation11EuclideanSpace =>
        (observation11EuclideanPullback u x) ^ 2 *
          Real.log ((observation11EuclideanPullback u x) ^ 2))
        standardGaussianObservationEuclideanLaw := by
  change Integrable (observation11SquareLogSquare u) gaussianObservationLaw ↔
    Integrable (observation11EuclideanSquareLogSquare u)
      standardGaussianObservationEuclideanLaw
  rw [← observation11SquareLogSquare_comp_eq u]
  exact observation11_integrable_pullback_iff
    (g := observation11EuclideanSquareLogSquare u)
    (measurable_observation11EuclideanSquareLogSquare u)

/-- The signed square-log-square integral is exactly preserved by Gaussian
coordinate transport. -/
theorem integral_gaussianObservation_squareLogSquare_eq
    (u : GaussianObservationTest) :
    (∫ z : Observation 1 1,
      u.1 z ^ 2 * Real.log (u.1 z ^ 2) ∂gaussianObservationLaw) =
      ∫ x : observation11EuclideanSpace,
        (observation11EuclideanPullback u x) ^ 2 *
          Real.log ((observation11EuclideanPullback u x) ^ 2)
            ∂standardGaussianObservationEuclideanLaw := by
  change (∫ z, observation11SquareLogSquare u z ∂gaussianObservationLaw) =
    ∫ x, observation11EuclideanSquareLogSquare u x
      ∂standardGaussianObservationEuclideanLaw
  rw [← observation11SquareLogSquare_comp_eq u]
  exact observation11_integral_pullback_eq
    (g := observation11EuclideanSquareLogSquare u)
    (measurable_observation11EuclideanSquareLogSquare u)

/-- Under the genuine square and square-log-square integrability admissions,
the manuscript's entropy expression for `u²` agrees exactly with that of its
literal Euclidean pullback. This is a transport identity, not an admission of
either integrability condition. -/
theorem gaussianObservation_entropy_transport
    (u : GaussianObservationTest)
    (hSquare : Integrable (fun z : Observation 1 1 => u.1 z ^ 2)
      gaussianObservationLaw)
    (hSquareLog : Integrable (fun z : Observation 1 1 =>
      u.1 z ^ 2 * Real.log (u.1 z ^ 2))
      gaussianObservationLaw) :
    (Integrable (fun x : observation11EuclideanSpace =>
        (observation11EuclideanPullback u x) ^ 2)
          standardGaussianObservationEuclideanLaw ∧
      Integrable (fun x : observation11EuclideanSpace =>
        (observation11EuclideanPullback u x) ^ 2 *
          Real.log ((observation11EuclideanPullback u x) ^ 2))
          standardGaussianObservationEuclideanLaw) ∧
    ((∫ z : Observation 1 1,
        u.1 z ^ 2 * Real.log (u.1 z ^ 2) ∂gaussianObservationLaw) -
        (∫ z : Observation 1 1, u.1 z ^ 2 ∂gaussianObservationLaw) *
          Real.log (∫ z : Observation 1 1, u.1 z ^ 2 ∂gaussianObservationLaw) =
      (∫ x : observation11EuclideanSpace,
        (observation11EuclideanPullback u x) ^ 2 *
          Real.log ((observation11EuclideanPullback u x) ^ 2)
            ∂standardGaussianObservationEuclideanLaw) -
        (∫ x : observation11EuclideanSpace,
          (observation11EuclideanPullback u x) ^ 2
            ∂standardGaussianObservationEuclideanLaw) *
          Real.log (∫ x : observation11EuclideanSpace,
            (observation11EuclideanPullback u x) ^ 2
              ∂standardGaussianObservationEuclideanLaw)) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact (integrable_gaussianObservation_square_iff u).mp hSquare
  · exact (integrable_gaussianObservation_squareLogSquare_iff u).mp hSquareLog
  · rw [integral_gaussianObservation_squareLogSquare_eq u,
      integral_gaussianObservation_square_eq u]

end LOOConcentration
