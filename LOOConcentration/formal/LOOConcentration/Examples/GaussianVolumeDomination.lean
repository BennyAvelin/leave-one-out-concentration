import LOOConcentration.Geometry.LocallyLipschitzDifferentiability
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic

/-!
# Gaussian volume domination and almost-everywhere differentiability

This module derives absolute continuity of the actual standard Gaussian laws
from scalar Gaussian densities and finite products, then transfers Euclidean
volume-a.e. differentiability of locally Lipschitz functions to the Gaussian
law. The PiLp coordinate map is used with Mathlib's volume-preserving theorem,
so the max norm on a function space is never identified with the Euclidean
norm.
-/

set_option autoImplicit false

open MeasureTheory

namespace LOOConcentration

theorem standardGaussianReal_absolutelyContinuous_volume :
    ProbabilityTheory.gaussianReal 0 1 ≪ (volume : Measure ℝ) := by
  exact ProbabilityTheory.gaussianReal_absolutelyContinuous 0 (v := 1) (by norm_num)

private theorem iidStandardGaussianCoordinates_absolutelyContinuous_fin
    (n : ℕ) :
    Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1) ≪
      (volume : Measure (Fin n → ℝ)) := by
  induction n with
  | zero =>
      rw [Measure.pi_of_empty, Measure.volume_pi_eq_dirac]
  | succ n ih =>
      let e : MeasurableEquiv (Fin (n + 1) → ℝ) (ℝ × (Fin n → ℝ)) :=
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
      have hgauss :
          MeasurePreserving e
            (Measure.pi (fun _ : Fin (n + 1) => ProbabilityTheory.gaussianReal 0 1))
            ((ProbabilityTheory.gaussianReal 0 1).prod
              (Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1))) := by
        simpa [e] using
          (measurePreserving_piFinSuccAbove
            (fun _ : Fin (n + 1) => ProbabilityTheory.gaussianReal 0 1)
            (0 : Fin (n + 1)))
      have hvolume :
          MeasurePreserving e (volume : Measure (Fin (n + 1) → ℝ))
            ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) := by
        simpa [e, volume_pi] using
          (measurePreserving_piFinSuccAbove
            (fun _ : Fin (n + 1) => (volume : Measure ℝ))
            (0 : Fin (n + 1)))
      have hprod :
          (ProbabilityTheory.gaussianReal 0 1).prod
              (Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)) ≪
            (volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)) := by
        exact
          Measure.AbsolutelyContinuous.prod
            standardGaussianReal_absolutelyContinuous_volume ih
      have hmap := hprod.map e.symm.measurable
      simpa only [hgauss.symm.map_eq, hvolume.symm.map_eq] using hmap

theorem iidStandardGaussianCoordinates_absolutelyContinuous
    {ι : Type*} [Fintype ι] :
    Measure.pi (fun _ : ι => ProbabilityTheory.gaussianReal 0 1) ≪
      (volume : Measure (ι → ℝ)) := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let E := MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e
  have hgauss :
      MeasurePreserving E
        (Measure.pi (fun _ : Fin (Fintype.card ι) => ProbabilityTheory.gaussianReal 0 1))
        (Measure.pi (fun _ : ι => ProbabilityTheory.gaussianReal 0 1)) := by
    simpa [E] using
      (measurePreserving_piCongrLeft
        (fun _ : ι => ProbabilityTheory.gaussianReal 0 1) e)
  have hvolume :
      MeasurePreserving E (volume : Measure (Fin (Fintype.card ι) → ℝ))
        (volume : Measure (ι → ℝ)) := by
    simpa [E] using
      (volume_measurePreserving_piCongrLeft (fun _ : ι => ℝ) e)
  have hmap :=
    (iidStandardGaussianCoordinates_absolutelyContinuous_fin (Fintype.card ι)).map
      E.measurable
  simpa only [hgauss.map_eq, hvolume.map_eq] using hmap

theorem standardGaussian_absolutelyContinuous_volume
    {ι : Type*} [Fintype ι] :
    ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι) ≪
      (volume : Measure (EuclideanSpace ℝ ι)) := by
  have hcoord := iidStandardGaussianCoordinates_absolutelyContinuous (ι := ι)
  have hmap := hcoord.map
    ((PiLp.continuous_toLp (p := (2 : ENNReal)) (β := fun _ : ι => ℝ)).measurable)
  have hvolume := PiLp.volume_preserving_toLp ι
  simpa only [ProbabilityTheory.map_pi_eq_stdGaussian, hvolume.map_eq] using hmap

theorem standardGaussian_ae_differentiableAt_of_locallyLipschitz
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : EuclideanSpace ℝ ι → ℝ) (hf : LocallyLipschitz f) :
    ∀ᵐ x ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)),
      DifferentiableAt ℝ f x := by
  exact locallyLipschitz_ae_differentiableAt_of_absolutelyContinuous f hf
    (standardGaussian_absolutelyContinuous_volume (ι := ι))

#print axioms standardGaussianReal_absolutelyContinuous_volume
#print axioms iidStandardGaussianCoordinates_absolutelyContinuous
#print axioms standardGaussian_absolutelyContinuous_volume
#print axioms standardGaussian_ae_differentiableAt_of_locallyLipschitz

end LOOConcentration
