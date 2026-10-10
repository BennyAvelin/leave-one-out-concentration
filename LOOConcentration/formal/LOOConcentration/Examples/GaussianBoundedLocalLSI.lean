import LOOConcentration.Examples.GaussianCutoffEnergy
import LOOConcentration.Examples.GaussianObservationEnergyTransport
import LOOConcentration.Concentration.EntropyCalculus
import LOOConcentration.FunctionalInequalities.OneSpacePoincareLimit
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-!
# Bounded locally Lipschitz Gaussian entropy inequality by cutoff passage

This file passes an explicit bounded globally Lipschitz Gaussian inequality
to the actual bounded locally Lipschitz test class on `Observation 1 1`. The
conditional public theorems state that single universal premise literally.
The cutoff energy, integrability, and entropy endpoints are obtained from the
accepted actual Gaussian cutoff and observation transport modules.
-/

set_option autoImplicit false

open Filter MeasureTheory
open scoped NNReal Topology

namespace LOOConcentration

private theorem gaussianObservation_square_integrable_of_bound
    (u : GaussianObservationTest) (B : ℝ) (hB : 0 ≤ B)
    (hu : ∀ z, |u.1 z| ≤ B) :
    Integrable (fun z : Observation 1 1 => u.1 z ^ 2) gaussianObservationLaw := by
  have hmeas : Measurable (fun z : Observation 1 1 => u.1 z ^ 2) :=
    ((oneObservationLip_continuous u).pow 2).measurable
  apply Integrable.of_bound hmeas.aestronglyMeasurable (B ^ 2)
  filter_upwards with z
  rw [Real.norm_of_nonneg (sq_nonneg _), ← sq_abs]
  have hleft : 0 ≤ B - |u.1 z| := sub_nonneg.mpr (hu z)
  have hright : 0 ≤ B + |u.1 z| := by positivity
  nlinarith [mul_nonneg hleft hright]

private theorem gaussianObservation_entropyDensity_integrable_of_bound
    (u : GaussianObservationTest) (B : ℝ)
    (hu : ∀ z, |u.1 z| ≤ B) :
    Integrable (fun z : Observation 1 1 =>
      u.1 z ^ 2 * Real.log (u.1 z ^ 2)) gaussianObservationLaw := by
  have hcont : Continuous (fun x : ℝ => x ^ 2 * Real.log (x ^ 2)) :=
    Real.continuous_mul_log.comp (by fun_prop)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Set.Icc (-B) B) hcont.continuousOn
  let M' := max M 0
  have hmeas : Measurable (fun z : Observation 1 1 =>
      u.1 z ^ 2 * Real.log (u.1 z ^ 2)) :=
    hcont.measurable.comp (oneObservationLip_continuous u).measurable
  apply Integrable.of_bound hmeas.aestronglyMeasurable M'
  filter_upwards with z
  have hz : u.1 z ∈ Set.Icc (-B) B := abs_le.mp (hu z)
  have hφ : ‖u.1 z ^ 2 * Real.log (u.1 z ^ 2)‖ ≤ M := hM _ hz
  exact hφ.trans (le_max_left _ _)

private theorem tendsto_cutoff_looconcentrationEntropy
    (u : observation11EuclideanSpace → ℝ)
    (huLip : LocallyLipschitz u) (B : ℝ) (hB : 0 ≤ B)
    (hu : ∀ x, |u x| ≤ B) :
    Tendsto
      (fun n : ℕ => looconcentrationEntropy standardGaussianObservationEuclideanLaw
        (fun x => boundedGaussianCutoffApproximation u
          (gaussianIntegerRadius n) B hB x ^ 2))
      atTop
      (𝓝 (looconcentrationEntropy standardGaussianObservationEuclideanLaw (fun x => u x ^ 2))) := by
  let cut : ℕ → observation11EuclideanSpace → ℝ := fun n x =>
    boundedGaussianCutoffApproximation u (gaussianIntegerRadius n) B hB x
  have hmass := boundedGaussianCutoffApproximation_tendsto_squareMass
    (ν := standardGaussianObservationEuclideanLaw) u huLip B hB hu
  have hdensity := boundedGaussianCutoffApproximation_tendsto_entropy
    (ν := standardGaussianObservationEuclideanLaw) u huLip B hB hu
  have hmassLog : Tendsto
      (fun n : ℕ => (∫ x, cut n x ^ 2 ∂standardGaussianObservationEuclideanLaw) *
        Real.log (∫ x, cut n x ^ 2 ∂standardGaussianObservationEuclideanLaw))
      atTop
      (𝓝 ((∫ x, u x ^ 2 ∂standardGaussianObservationEuclideanLaw) *
        Real.log (∫ x, u x ^ 2 ∂standardGaussianObservationEuclideanLaw))) := by
    have hcont : Continuous (fun r : ℝ => r * Real.log r) := Real.continuous_mul_log
    have h := hcont.continuousAt.tendsto.comp hmass
    change Tendsto
      ((fun r : ℝ => r * Real.log r) ∘
        (fun n : ℕ => ∫ x, cut n x ^ 2 ∂standardGaussianObservationEuclideanLaw))
      atTop
      (𝓝 ((∫ x, u x ^ 2 ∂standardGaussianObservationEuclideanLaw) *
        Real.log (∫ x, u x ^ 2 ∂standardGaussianObservationEuclideanLaw)))
    exact h
  have h := hdensity.sub hmassLog
  simpa [cut, looconcentrationEntropy, cutoffSquareLogSquare] using h

/-- The actual bounded locally Lipschitz entropy inequality on the frozen
observation carrier, conditional on the single bounded-global Euclidean core
inequality. The source square and square-log-square integrability conclusions
are returned as genuine Bochner integrability facts. -/
theorem gaussianObservation_boundedLocallyLipschitz_entropy_of_boundedGlobalCore
    (hCore : ∀ (f : observation11EuclideanSpace → ℝ) (K : ℝ≥0) (B : ℝ),
      0 ≤ B → LipschitzWith K f → (∀ x, |f x| ≤ B) →
        looconcentrationEntropy standardGaussianObservationEuclideanLaw (fun x => f x ^ 2) ≤
          2 * (∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂standardGaussianObservationEuclideanLaw))
    (u : GaussianObservationTest) (B : ℝ)
    (huBound : ∀ z, |u.1 z| ≤ B)
    (hEnergy : Integrable (fun z : Observation 1 1 =>
      (observationLocalSlope u z) ^ 2) gaussianObservationLaw) :
    Integrable (fun z : Observation 1 1 => u.1 z ^ 2) gaussianObservationLaw ∧
    Integrable (fun z : Observation 1 1 =>
      u.1 z ^ 2 * Real.log (u.1 z ^ 2)) gaussianObservationLaw ∧
    ((∫ z : Observation 1 1,
        u.1 z ^ 2 * Real.log (u.1 z ^ 2) ∂gaussianObservationLaw) -
      (∫ z : Observation 1 1, u.1 z ^ 2 ∂gaussianObservationLaw) *
        Real.log (∫ z : Observation 1 1, u.1 z ^ 2 ∂gaussianObservationLaw) ≤
      2 * (∫ z : Observation 1 1,
        (observationLocalSlope u z) ^ 2 ∂gaussianObservationLaw)) := by
  have hB : 0 ≤ B := (abs_nonneg (u.1 0)).trans (huBound 0)
  have hSquare := gaussianObservation_square_integrable_of_bound u B hB huBound
  have hSquareLog := gaussianObservation_entropyDensity_integrable_of_bound u B huBound
  have hTransport := gaussianObservation_entropy_transport u hSquare hSquareLog
  have hF := observation11EuclideanPullback_locallyLipschitz u
  have hFBound : ∀ x : observation11EuclideanSpace,
      |observation11EuclideanPullback u x| ≤ B := by
    intro x
    exact huBound (observationFromEuclidean x)
  have hEnergyTransport :=
    observation11EuclideanPullback_derivative_energy_transport u hEnergy
  let F : observation11EuclideanSpace → ℝ := observation11EuclideanPullback u
  let E : ℝ := ∫ x : observation11EuclideanSpace,
    ‖fderiv ℝ F x‖ ^ 2 ∂standardGaussianObservationEuclideanLaw
  have hE : 0 ≤ E := by
    dsimp [E]
    exact integral_nonneg fun x => sq_nonneg _
  have hAbsCont := standardGaussian_absolutelyContinuous_volume
    (ι := ObservationCoordinate 1 1)
  let cut : ℕ → observation11EuclideanSpace → ℝ := fun n x =>
    boundedGaussianCutoffApproximation F (gaussianIntegerRadius n) B hB x
  have hCutInequality (n : ℕ) :
      looconcentrationEntropy standardGaussianObservationEuclideanLaw
          (fun x => cut n x ^ 2) ≤
        2 * (∫ x : observation11EuclideanSpace,
          ‖fderiv ℝ (cut n) x‖ ^ 2 ∂standardGaussianObservationEuclideanLaw) := by
    obtain ⟨L, hL⟩ := boundedGaussianCutoffApproximation_exists_globalLipschitz
      F hF (gaussianIntegerRadius n) B hB
    have hCutBound (x : observation11EuclideanSpace) : |cut n x| ≤ B := by
      exact boundedGaussianCutoffApproximation_abs_le F
        (gaussianIntegerRadius n) B hB hFBound x
    simpa only [cut] using hCore (cut n) L B hB hL hCutBound
  have hUpperBound (n : ℕ) :
      2 * (∫ x : observation11EuclideanSpace,
          ‖fderiv ℝ (cut n) x‖ ^ 2 ∂standardGaussianObservationEuclideanLaw) ≤
        2 * (Real.sqrt E +
          B * gaussianCutoffDerivativeConstant
            (ι := ObservationCoordinate 1 1) /
              (gaussianIntegerRadius n).1) ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    simpa [cut, E, F] using
      (boundedGaussianCutoffApproximation_energy_le
        (ν := standardGaussianObservationEuclideanLaw)
        F hF (gaussianIntegerRadius n) B hB hFBound hAbsCont
        hEnergyTransport.1)
  have hCutLimit : Tendsto
      (fun n : ℕ => looconcentrationEntropy standardGaussianObservationEuclideanLaw
        (fun x => cut n x ^ 2))
      atTop (𝓝 (looconcentrationEntropy standardGaussianObservationEuclideanLaw (fun x => F x ^ 2))) := by
    simpa [cut, F] using
      tendsto_cutoff_looconcentrationEntropy F hF B hB hFBound
  have hRootBound : Tendsto
      (fun n : ℕ => Real.sqrt E +
        B * gaussianCutoffDerivativeConstant
          (ι := ObservationCoordinate 1 1) /
            (gaussianIntegerRadius n).1)
      atTop (𝓝 (Real.sqrt E)) := by
    have h := (boundedGaussianCutoffApproximation_sqrtEnergyBound_tendsto
      (ν := standardGaussianObservationEuclideanLaw) F B).comp
        gaussianIntegerRadius_tendsto_atTop
    change Tendsto
      ((fun R : GaussianPositiveRadius => Real.sqrt E +
        B * gaussianCutoffDerivativeConstant
          (ι := ObservationCoordinate 1 1) / R.1) ∘ gaussianIntegerRadius)
      atTop (𝓝 (Real.sqrt E))
    exact h
  have hUpperLimit : Tendsto
      (fun n : ℕ => 2 * (Real.sqrt E +
        B * gaussianCutoffDerivativeConstant
          (ι := ObservationCoordinate 1 1) /
            (gaussianIntegerRadius n).1) ^ 2)
      atTop (𝓝 (2 * E)) := by
    have h := (hRootBound.pow 2).const_mul 2
    convert h using 1
    rw [Real.sq_sqrt hE]
  have hEuclideanEntropy :
      (∫ x : observation11EuclideanSpace,
          F x ^ 2 * Real.log (F x ^ 2)
            ∂standardGaussianObservationEuclideanLaw) -
        (∫ x : observation11EuclideanSpace, F x ^ 2
          ∂standardGaussianObservationEuclideanLaw) *
          Real.log (∫ x : observation11EuclideanSpace, F x ^ 2
            ∂standardGaussianObservationEuclideanLaw) ≤ 2 * E := by
    have hEventually : ∀ᶠ n : ℕ in atTop,
        looconcentrationEntropy standardGaussianObservationEuclideanLaw
            (fun x => cut n x ^ 2) ≤
          2 * (Real.sqrt E +
            B * gaussianCutoffDerivativeConstant
              (ι := ObservationCoordinate 1 1) /
                (gaussianIntegerRadius n).1) ^ 2 :=
      Filter.Eventually.of_forall fun n =>
        (hCutInequality n).trans (hUpperBound n)
    have hLimit := le_of_tendsto_of_tendsto
      hCutLimit hUpperLimit hEventually
    simpa [looconcentrationEntropy] using hLimit
  rcases hTransport with ⟨⟨_, _⟩, hEntropyTransport⟩
  refine ⟨hSquare, hSquareLog, ?_⟩
  calc
    (∫ z : Observation 1 1,
        u.1 z ^ 2 * Real.log (u.1 z ^ 2) ∂gaussianObservationLaw) -
      (∫ z : Observation 1 1, u.1 z ^ 2 ∂gaussianObservationLaw) *
        Real.log (∫ z : Observation 1 1, u.1 z ^ 2 ∂gaussianObservationLaw) =
      (∫ x : observation11EuclideanSpace,
          F x ^ 2 * Real.log (F x ^ 2)
            ∂standardGaussianObservationEuclideanLaw) -
        (∫ x : observation11EuclideanSpace, F x ^ 2
          ∂standardGaussianObservationEuclideanLaw) *
          Real.log (∫ x : observation11EuclideanSpace, F x ^ 2
            ∂standardGaussianObservationEuclideanLaw) := by
      exact hEntropyTransport
    _ ≤ 2 * E := hEuclideanEntropy
    _ = 2 * (∫ z : Observation 1 1,
        (observationLocalSlope u z) ^ 2 ∂gaussianObservationLaw) := by
      change 2 * (∫ x : observation11EuclideanSpace,
        ‖fderiv ℝ (observation11EuclideanPullback u) x‖ ^ 2
          ∂standardGaussianObservationEuclideanLaw) = _
      exact congrArg (fun e : ℝ => 2 * e) hEnergyTransport.2

/-- The exact bounded-entropy interface used by the finite-energy admission
assembly, obtained from the bounded-global core by the actual cutoff passage. -/
theorem gaussianObservation_boundedEntropy_of_boundedGlobalCore
    (hCore : ∀ (f : observation11EuclideanSpace → ℝ) (K : ℝ≥0) (B : ℝ),
      0 ≤ B → LipschitzWith K f → (∀ x, |f x| ≤ B) →
        looconcentrationEntropy standardGaussianObservationEuclideanLaw (fun x => f x ^ 2) ≤
          2 * (∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂standardGaussianObservationEuclideanLaw))
    (u : GaussianObservationTest) (B : ℝ)
    (huBound : ∀ z, |u.1 z| ≤ B)
    (hEnergy : Integrable (fun z : Observation 1 1 =>
      (observationLocalSlope u z) ^ 2) gaussianObservationLaw) :
    (∫ z : Observation 1 1,
        u.1 z ^ 2 * Real.log (u.1 z ^ 2) ∂gaussianObservationLaw) -
      (∫ z : Observation 1 1, u.1 z ^ 2 ∂gaussianObservationLaw) *
        Real.log (∫ z : Observation 1 1, u.1 z ^ 2 ∂gaussianObservationLaw) ≤
      2 * (∫ z : Observation 1 1,
        (observationLocalSlope u z) ^ 2 ∂gaussianObservationLaw) := by
  exact (gaussianObservation_boundedLocallyLipschitz_entropy_of_boundedGlobalCore
    hCore u B huBound hEnergy).2.2

#print axioms gaussianObservation_boundedLocallyLipschitz_entropy_of_boundedGlobalCore
#print axioms gaussianObservation_boundedEntropy_of_boundedGlobalCore

end LOOConcentration
