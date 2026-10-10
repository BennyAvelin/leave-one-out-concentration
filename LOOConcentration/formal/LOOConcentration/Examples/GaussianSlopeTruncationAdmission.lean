import LOOConcentration.Examples.GaussianVolumeDomination
import LOOConcentration.Geometry.LocallyLipschitzDifferentiability
import LOOConcentration.Geometry.LocalSlopeFacts
import LOOConcentration.Geometry.LocalSlopeTruncation
import LOOConcentration.Analysis.ClipMollify
import LOOConcentration.Geometry.SmoothObservationSlope
import LOOConcentration.Geometry.LipschitzCoordinateEnergy
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.Tactic

set_option autoImplicit false

open MeasureTheory
open scoped Topology

namespace LOOConcentration

/-- The frozen locally Lipschitz test class on the actual `Observation 1 1`
carrier. -/
abbrev GaussianObservationTest :=
  {g : Observation 1 1 → ℝ //
    ∀ z, ∃ U ∈ 𝓝 z, ∃ C : ℝ, 0 ≤ C ∧
      ∀ w ∈ U, ∀ v ∈ U,
        |g w - g v| ≤ C * observationNorm (w - v)}

/-- Pull an actual frozen observation test back to its flattened Euclidean
coordinates. -/
def observation11EuclideanPullback (u : GaussianObservationTest) :
    EuclideanSpace ℝ (ObservationCoordinate 1 1) → ℝ :=
  fun x => u.1 (observationFromEuclidean x)

/-- The literal Euclidean pullback is locally Lipschitz, even when the frozen
observation test is not globally Lipschitz. -/
theorem observation11EuclideanPullback_locallyLipschitz
    (u : GaussianObservationTest) :
    LocallyLipschitz (observation11EuclideanPullback u) := by
  intro x
  obtain ⟨U, hU, C, hC, hLip⟩ := u.2 (observationFromEuclidean x)
  let K : NNReal := ⟨C, hC⟩
  have hfrom : Continuous (observationFromEuclidean :
      EuclideanSpace ℝ (ObservationCoordinate 1 1) → Observation 1 1) := by
    exact observationCoordinateContinuousLinearEquiv.symm.continuous
  refine ⟨K, observationFromEuclidean ⁻¹' U,
    hfrom.continuousAt.preimage_mem_nhds hU, ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro y hy z hz
  have hy' : observationFromEuclidean y ∈ U := hy
  have hz' : observationFromEuclidean z ∈ U := hz
  have hlocal := hLip (observationFromEuclidean y) hy'
    (observationFromEuclidean z) hz'
  change dist (u.1 (observationFromEuclidean y))
      (u.1 (observationFromEuclidean z)) ≤ (K : ℝ) * dist y z
  have hreal :
      dist (u.1 (observationFromEuclidean y))
          (u.1 (observationFromEuclidean z)) ≤ C * dist y z := by
    simpa [Real.dist_eq, dist_eq_norm, observationNorm_sub_eq_euclidean,
      observationToEuclidean_sub] using hlocal
  change dist (u.1 (observationFromEuclidean y))
      (u.1 (observationFromEuclidean z)) ≤ C * dist y z
  exact hreal

private theorem observation11_pullback_subtype_eq (u : GaussianObservationTest) :
    u = locallyLipschitzObservationPullback (observation11EuclideanPullback u)
      (observation11EuclideanPullback_locallyLipschitz u) := by
  apply Subtype.ext
  funext z
  simp [observation11EuclideanPullback, locallyLipschitzObservationPullback]

/-- The full Euclidean Fréchet derivative of the literal pullback is measurable
on the whole actual observation carrier. -/
theorem measurable_observation11EuclideanFDeriv (u : GaussianObservationTest) :
    Measurable (fun z : Observation 1 1 =>
      fderiv ℝ (observation11EuclideanPullback u) (observationToEuclidean z)) := by
  have hmap : Measurable
      (observationToEuclidean : Observation 1 1 →
        EuclideanSpace ℝ (ObservationCoordinate 1 1)) :=
    observationCoordinateContinuousLinearEquiv.continuous.measurable
  exact (measurable_fderiv (𝕜 := ℝ)
    (f := observation11EuclideanPullback u)).comp hmap

/-- Under the actual transported Gaussian law, the frozen local slope of an
arbitrary locally Lipschitz Observation(1,1) test equals the norm of the full
Euclidean derivative of its literal pullback almost everywhere. -/
theorem ae_gaussianObservationLaw_observationLocalSlope_eq_fderiv
    (u : GaussianObservationTest) :
    ∀ᵐ z ∂gaussianObservationLaw,
      observationLocalSlope u z =
        ‖fderiv ℝ (observation11EuclideanPullback u)
          (observationToEuclidean z)‖ := by
  let f := observation11EuclideanPullback u
  let hf := observation11EuclideanPullback_locallyLipschitz u
  have hstd := standardGaussian_ae_differentiableAt_of_locallyLipschitz f hf
  have hdiffMap : ∀ᵐ x ∂gaussianObservationLaw.map
      (observationToEuclidean : Observation 1 1 →
        EuclideanSpace ℝ (ObservationCoordinate 1 1)),
      DifferentiableAt ℝ f x := by
    simpa only [gaussianObservationLaw_map_observationToEuclidean] using hstd
  have hdiff : ∀ᵐ z ∂gaussianObservationLaw,
      DifferentiableAt ℝ f (observationToEuclidean z) := by
    exact (ae_map_iff
      (observationCoordinateContinuousLinearEquiv.continuous.measurable.aemeasurable)
      (measurableSet_of_differentiableAt ℝ f)).mp hdiffMap
  filter_upwards [hdiff] with z hz
  rw [observation11_pullback_subtype_eq u]
  exact observationLocalSlope_locallyLipschitzPullback_eq f hf z hz

/-- The squared actual frozen local slope is Gaussian-a.e. strongly
measurable, by identification with the measurable full derivative norm. -/
theorem aestronglyMeasurable_gaussianObservationLaw_observationLocalSlope_sq
    (u : GaussianObservationTest) :
    AEStronglyMeasurable (fun z : Observation 1 1 =>
      (observationLocalSlope u z) ^ 2) gaussianObservationLaw := by
  have hderivMeas := measurable_observation11EuclideanFDeriv u
  have hnormSqMeas : Measurable (fun z : Observation 1 1 =>
      ‖fderiv ℝ (observation11EuclideanPullback u)
        (observationToEuclidean z)‖ ^ 2) :=
    (continuous_norm.measurable.comp hderivMeas).pow_const 2
  have hsqEq : (fun z : Observation 1 1 =>
      (observationLocalSlope u z) ^ 2) =ᵐ[gaussianObservationLaw]
      (fun z => ‖fderiv ℝ (observation11EuclideanPullback u)
        (observationToEuclidean z)‖ ^ 2) := by
    filter_upwards [ae_gaussianObservationLaw_observationLocalSlope_eq_fderiv u]
      with z hz
    rw [hz]
  exact hnormSqMeas.aestronglyMeasurable.congr hsqEq.symm

/-- A positive literal truncation radius bounds the actual frozen clipped
function; the returned value remains in the locally Lipschitz subtype. -/
theorem clippedObservationFunction_abs_le
    (u : GaussianObservationTest) {A : ℝ} (hA : 0 < A) (z : Observation 1 1) :
    |(clippedObservationFunction u A).1 z| ≤ A := by
  change |clipValue A (u.1 z)| ≤ A
  exact abs_le.mpr (clipValue_bounds (u := u.1 z) hA.le)

/-- Literal clipping admits the finite-energy test class: its actual squared
frozen slope is integrable and its energy is no larger than that of `u`. No
log-Sobolev assumption is used. -/
theorem clippedObservationFunction_energy_admission
    (u : GaussianObservationTest) {A : ℝ}
    (hEnergy : Integrable (fun z : Observation 1 1 =>
      (observationLocalSlope u z) ^ 2) gaussianObservationLaw) :
    Integrable (fun z : Observation 1 1 =>
      (observationLocalSlope (clippedObservationFunction u A) z) ^ 2)
        gaussianObservationLaw ∧
      (∫ z, (observationLocalSlope (clippedObservationFunction u A) z) ^ 2
        ∂gaussianObservationLaw) ≤
      ∫ z, (observationLocalSlope u z) ^ 2 ∂gaussianObservationLaw := by
  let uA := clippedObservationFunction u A
  have hmeas :=
    aestronglyMeasurable_gaussianObservationLaw_observationLocalSlope_sq uA
  have hsq (z : Observation 1 1) :
      (observationLocalSlope uA z) ^ 2 ≤ (observationLocalSlope u z) ^ 2 := by
    have hA0 := observationLocalSlope_nonneg uA z
    have hu0 := observationLocalSlope_nonneg u z
    have hle := observationLocalSlope_clip_le u A z
    nlinarith [mul_nonneg (sub_nonneg.mpr hle) (add_nonneg hA0 hu0)]
  have hclipEnergy : Integrable
      (fun z : Observation 1 1 => (observationLocalSlope uA z) ^ 2)
      gaussianObservationLaw := by
    apply hEnergy.mono' hmeas
    filter_upwards [] with z
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hsq z
  refine ⟨hclipEnergy, ?_⟩
  exact integral_mono_ae hclipEnergy hEnergy (ae_of_all _ hsq)

#print axioms observation11EuclideanPullback_locallyLipschitz
#print axioms measurable_observation11EuclideanFDeriv
#print axioms ae_gaussianObservationLaw_observationLocalSlope_eq_fderiv
#print axioms aestronglyMeasurable_gaussianObservationLaw_observationLocalSlope_sq
#print axioms clippedObservationFunction_abs_le
#print axioms clippedObservationFunction_energy_admission

end LOOConcentration
