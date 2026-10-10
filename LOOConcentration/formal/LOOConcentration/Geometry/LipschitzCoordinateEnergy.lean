import LOOConcentration.Examples.GaussianVolumeDomination
import LOOConcentration.Examples.GaussianObservationTransport
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Tactic

/-!
# Gaussian collective coordinate energy

For a differentiable Euclidean function, the derivatives of its scalar
coordinate sections are the coefficients of its Fréchet derivative in the
canonical orthonormal basis. Their squared sum is therefore the squared full
derivative norm. The same identity holds almost everywhere under the standard
Gaussian for globally Lipschitz functions, and transports to the literal
finite product Gaussian law and the frozen Observation(1,1) local slope.
-/

set_option autoImplicit false

open MeasureTheory
open scoped NNReal

noncomputable section

namespace LOOConcentration

local instance (ι : Type*) [Fintype ι] : DecidableEq ι := Classical.decEq ι

/-- The affine path that varies coordinate `i` and freezes all other
coordinates at `x`. -/
noncomputable def euclideanCoordinatePath {ι : Type*} [Fintype ι]
    (x : EuclideanSpace ℝ ι) (i : ι) : ℝ → EuclideanSpace ℝ ι :=
  fun t => x + (t - x i) • EuclideanSpace.single i (1 : ℝ)

/-- A scalar section of a Euclidean function along one coordinate line. -/
noncomputable def euclideanCoordinateSection {ι : Type*} [Fintype ι]
    (f : EuclideanSpace ℝ ι → ℝ) (x : EuclideanSpace ℝ ι) (i : ι) : ℝ → ℝ :=
  fun t => f (euclideanCoordinatePath x i t)

/-- At a differentiability point, the derivative of a scalar coordinate
section is the Fréchet derivative applied to that coordinate basis vector. -/
theorem deriv_euclideanCoordinateSection_eq_fderiv
    {ι : Type*} [Fintype ι]
    (f : EuclideanSpace ℝ ι → ℝ) (x : EuclideanSpace ℝ ι) (i : ι)
    (hdiff : DifferentiableAt ℝ f x) :
    deriv (euclideanCoordinateSection f x i) (x i) =
      fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ)) := by
  have hscalar : HasDerivAt (fun t : ℝ => t - x i) 1 (x i) :=
    (hasDerivAt_id (x i)).sub_const (x i)
  have hpath : HasDerivAt (euclideanCoordinatePath x i)
      (EuclideanSpace.single i (1 : ℝ)) (x i) := by
    have hpath' : HasDerivAt
        (fun t => x + (t - x i) • EuclideanSpace.single i (1 : ℝ))
        ((1 : ℝ) • EuclideanSpace.single i (1 : ℝ)) (x i) :=
      (hasDerivAt_const_add_iff x).2
        (hscalar.smul_const (EuclideanSpace.single i (1 : ℝ)))
    change HasDerivAt
      (fun t => x + (t - x i) • EuclideanSpace.single i (1 : ℝ))
      (EuclideanSpace.single i (1 : ℝ)) (x i)
    simpa only [one_smul] using hpath'
  have hbase : x = euclideanCoordinatePath x i (x i) := by
    simp [euclideanCoordinatePath]
  have hcomp := hdiff.hasFDerivAt.comp_hasDerivAt_of_eq
    (x i) hpath hbase
  change deriv (fun t => f (euclideanCoordinatePath x i t)) (x i) = _
  exact hcomp.deriv

/-- The sum of the squared scalar coordinate-section derivatives is exactly
the squared norm of the full Fréchet derivative. -/
theorem sum_euclideanCoordinateSection_deriv_sq_eq_fderiv_norm_sq
    {ι : Type*} [Fintype ι]
    (f : EuclideanSpace ℝ ι → ℝ) (x : EuclideanSpace ℝ ι)
    (hdiff : DifferentiableAt ℝ f x) :
    (∑ i : ι,
      (deriv (euclideanCoordinateSection f x i) (x i)) ^ 2) =
        ‖fderiv ℝ f x‖ ^ 2 := by
  classical
  calc
    (∑ i : ι,
      (deriv (euclideanCoordinateSection f x i) (x i)) ^ 2) =
        ∑ i : ι, (fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ))) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [deriv_euclideanCoordinateSection_eq_fderiv f x i hdiff]
    _ = ‖fderiv ℝ f x‖ ^ 2 := by
      simpa only [EuclideanSpace.basisFun_apply] using
        (OrthonormalBasis.norm_dual (EuclideanSpace.basisFun ι ℝ)
          (fderiv ℝ f x)).symm

private theorem euclideanCoordinatePath_dist
    {ι : Type*} [Fintype ι]
    (x : EuclideanSpace ℝ ι) (i : ι) (s t : ℝ) :
    dist (euclideanCoordinatePath x i s) (euclideanCoordinatePath x i t) =
      dist s t := by
  rw [dist_eq_norm]
  have hvec : euclideanCoordinatePath x i s - euclideanCoordinatePath x i t =
      (s - t) • EuclideanSpace.single i (1 : ℝ) := by
    rw [euclideanCoordinatePath, euclideanCoordinatePath,
      add_sub_add_left_eq_sub, ← sub_smul]
    congr 1
    ring
  rw [hvec, norm_smul]
  simp [Real.dist_eq]

/-- A globally Lipschitz Euclidean function has equally Lipschitz scalar
coordinate sections, with the same constant, because each coordinate path is
an isometric affine inclusion. -/
theorem lipschitzWith_euclideanCoordinateSection
    {ι : Type*} [Fintype ι]
    {K : ℝ≥0} (f : EuclideanSpace ℝ ι → ℝ)
    (hf : LipschitzWith K f) (x : EuclideanSpace ℝ ι) (i : ι) :
    LipschitzWith K (euclideanCoordinateSection f x i) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  change dist (f (euclideanCoordinatePath x i s))
      (f (euclideanCoordinatePath x i t)) ≤ (K : ℝ) * dist s t
  calc
    dist (f (euclideanCoordinatePath x i s))
        (f (euclideanCoordinatePath x i t)) ≤
      (K : ℝ) * dist (euclideanCoordinatePath x i s)
        (euclideanCoordinatePath x i t) := hf.dist_le_mul _ _
    _ = (K : ℝ) * dist s t := by rw [euclideanCoordinatePath_dist]

/-- The coordinate energy identity holds almost everywhere for the actual
standard Gaussian whenever the function is globally Lipschitz. -/
theorem ae_standardGaussian_euclideanCoordinateEnergy
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (K : ℝ≥0) (f : EuclideanSpace ℝ ι → ℝ)
    (hf : LipschitzWith K f) :
    ∀ᵐ x ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)),
      (∑ i : ι,
        (deriv (euclideanCoordinateSection f x i) (x i)) ^ 2) =
          ‖fderiv ℝ f x‖ ^ 2 := by
  filter_upwards
    [standardGaussian_ae_differentiableAt_of_locallyLipschitz f hf.locallyLipschitz]
    with x hx
  exact sum_euclideanCoordinateSection_deriv_sq_eq_fderiv_norm_sq f x hx

/-- The scalar finite-product carrier for independent standard Gaussian
coordinates. It is a measurable product space; Euclidean geometry is applied
only after the PiLp `toLp` map. -/
noncomputable def standardGaussianPiLaw (ι : Type*) [Fintype ι] :
    Measure (ι → ℝ) :=
  Measure.pi fun _ : ι => ProbabilityTheory.gaussianReal 0 1

/-- Transfer the Gaussian coordinate-energy identity to literal scalar
finite-product coordinates using Mathlib's `map_pi_eq_stdGaussian`. -/
theorem ae_standardGaussianPi_euclideanCoordinateEnergy
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (K : ℝ≥0) (f : EuclideanSpace ℝ ι → ℝ)
    (hf : LipschitzWith K f) :
    ∀ᵐ y ∂(standardGaussianPiLaw ι),
      (∑ i : ι,
        (deriv (euclideanCoordinateSection f (WithLp.toLp (2 : ENNReal) y) i)
          ((WithLp.toLp (2 : ENNReal) y) i)) ^ 2) =
          ‖fderiv ℝ f (WithLp.toLp (2 : ENNReal) y)‖ ^ 2 := by
  have hstd := standardGaussian_ae_differentiableAt_of_locallyLipschitz
    f hf.locallyLipschitz
  have hmap : (standardGaussianPiLaw ι).map
      (WithLp.toLp (2 : ENNReal) : (ι → ℝ) → EuclideanSpace ℝ ι) =
        ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι) := by
    simpa [standardGaussianPiLaw] using
      (ProbabilityTheory.map_pi_eq_stdGaussian (ι := ι))
  have hdiff : ∀ᵐ y ∂(standardGaussianPiLaw ι),
      DifferentiableAt ℝ f (WithLp.toLp (2 : ENNReal) y) := by
    have hdiffMap : ∀ᵐ x ∂(standardGaussianPiLaw ι).map
        (WithLp.toLp (2 : ENNReal) : (ι → ℝ) → EuclideanSpace ℝ ι),
        DifferentiableAt ℝ f x := by
      simpa [hmap] using hstd
    exact (ae_map_iff
      ((PiLp.continuous_toLp (p := (2 : ENNReal))
        (β := fun _ : ι => ℝ)).measurable.aemeasurable)
      (measurableSet_of_differentiableAt ℝ f)).mp hdiffMap
  filter_upwards [hdiff] with y hy
  exact sum_euclideanCoordinateSection_deriv_sq_eq_fderiv_norm_sq f _ hy

/-- The measure equivalence from a pair of scalar values to the flattened
Observation(1,1) coordinate carrier. -/
noncomputable def gaussianPairCoordinateEquiv :
    (ℝ × ℝ) ≃ᵐ (ObservationCoordinate 1 1 → ℝ) :=
  (MeasurableEquiv.prodCongr
    (MeasurableEquiv.funUnique (Fin 1) ℝ).symm
    (MeasurableEquiv.funUnique (Fin 1) ℝ).symm).trans
    (MeasurableEquiv.sumPiEquivProdPi
      (fun _ : ObservationCoordinate 1 1 => ℝ)).symm

@[simp]
theorem gaussianPairCoordinateEquiv_apply_apply (p : ℝ × ℝ)
    (q : ObservationCoordinate 1 1) :
  gaussianPairCoordinateEquiv p q = Sum.elim (fun _ : Fin 1 => p.1)
      (fun _ : Fin 1 => p.2) q := by
  cases q with
  | inl i =>
      change ((Equiv.sumPiEquivProdPi (fun _ : Fin 1 ⊕ Fin 1 => ℝ)).symm
        ((Equiv.prodCongr (Equiv.funUnique (Fin 1) ℝ).symm
          (Equiv.funUnique (Fin 1) ℝ).symm) p)) (Sum.inl i) = p.1
      simp [Equiv.sumPiEquivProdPi, Equiv.funUnique]
  | inr j =>
      change ((Equiv.sumPiEquivProdPi (fun _ : Fin 1 ⊕ Fin 1 => ℝ)).symm
        ((Equiv.prodCongr (Equiv.funUnique (Fin 1) ℝ).symm
          (Equiv.funUnique (Fin 1) ℝ).symm) p)) (Sum.inr j) = p.2
      simp [Equiv.sumPiEquivProdPi, Equiv.funUnique]

/-- The actual Observation(1,1) Gaussian transports under the frozen
observation-coordinate equivalence to the standard Euclidean Gaussian. -/
theorem gaussianObservationLaw_map_observationToEuclidean :
    (gaussianObservationLaw).map
        (observationToEuclidean : Observation 1 1 →
          EuclideanSpace ℝ (ObservationCoordinate 1 1)) =
      ProbabilityTheory.stdGaussian
        (EuclideanSpace ℝ (ObservationCoordinate 1 1)) := by
  let γ := gaussianObservationCoordinateLaw
  have hfun : MeasurePreserving
      ((MeasurableEquiv.funUnique (Fin 1) ℝ).symm) γ
      (Measure.pi fun _ : Fin 1 => γ) := by
    exact (measurePreserving_funUnique γ (Fin 1)).symm
  have hsum : MeasurePreserving
      (MeasurableEquiv.sumPiEquivProdPi
        (fun _ : ObservationCoordinate 1 1 => ℝ)).symm
      ((Measure.pi fun _ : Fin 1 => γ).prod
        (Measure.pi fun _ : Fin 1 => γ))
      (Measure.pi fun _ : ObservationCoordinate 1 1 => γ) := by
    simpa [ObservationCoordinate] using
      (measurePreserving_sumPiEquivProdPi_symm
        (fun _ : Fin 1 ⊕ Fin 1 => γ))
  have hpair : MeasurePreserving gaussianPairCoordinateEquiv
      gaussianObservationPairLaw
      (Measure.pi fun _ : ObservationCoordinate 1 1 => γ) := by
    simpa [gaussianPairCoordinateEquiv, gaussianObservationPairLaw,
      ObservationCoordinate] using (hfun.prod hfun).trans hsum
  have hcomp :
      (fun p : ℝ × ℝ => observationToEuclidean (gaussianPairObservationCLE p)) =
      (fun p => WithLp.toLp (2 : ENNReal) (gaussianPairCoordinateEquiv p)) := by
    funext p
    apply PiLp.ext
    intro q
    cases q <;>
      simp [observationToEuclidean, gaussianPairObservationCLE_apply,
        gaussianPairCoordinateEquiv_apply_apply]
  have hObsMeas : Measurable
      (observationToEuclidean : Observation 1 1 →
        EuclideanSpace ℝ (ObservationCoordinate 1 1)) :=
    observationCoordinateContinuousLinearEquiv.continuous.measurable
  rw [gaussianObservationLaw,
    Measure.map_map hObsMeas gaussianPairObservationCLE_measurable,
    show observationToEuclidean ∘ gaussianPairObservationCLE =
      (fun p => observationToEuclidean (gaussianPairObservationCLE p)) from rfl,
    hcomp]
  change gaussianObservationPairLaw.map
      ((WithLp.toLp (2 : ENNReal) : (ObservationCoordinate 1 1 → ℝ) →
        EuclideanSpace ℝ (ObservationCoordinate 1 1)) ∘ gaussianPairCoordinateEquiv) = _
  rw [← Measure.map_map
    (PiLp.continuous_toLp (p := (2 : ENNReal))
      (β := fun _ : ObservationCoordinate 1 1 => ℝ)).measurable
    gaussianPairCoordinateEquiv.measurable]
  rw [hpair.map_eq]
  exact ProbabilityTheory.map_pi_eq_stdGaussian

/-- For the frozen Observation(1,1) law, the squared local slope of the
actual locally Lipschitz pullback equals the collective coordinate energy
almost everywhere. The assertion uses the source's nonsmooth local slope and
does not assert a pointwise identity at nondifferentiability points. -/
theorem ae_gaussianObservationLaw_observationLocalSlope_sq_eq_coordinateEnergy
    (K : ℝ≥0)
    (f : EuclideanSpace ℝ (ObservationCoordinate 1 1) → ℝ)
    (hf : LipschitzWith K f) :
    ∀ᵐ z ∂gaussianObservationLaw,
      (observationLocalSlope
        (locallyLipschitzObservationPullback f hf.locallyLipschitz) z) ^ 2 =
        ∑ i : ObservationCoordinate 1 1,
          (deriv (euclideanCoordinateSection f (observationToEuclidean z) i)
            ((observationToEuclidean z) i)) ^ 2 := by
  have hstd := standardGaussian_ae_differentiableAt_of_locallyLipschitz
    f hf.locallyLipschitz
  have hObsDiff : ∀ᵐ z ∂gaussianObservationLaw,
      DifferentiableAt ℝ f (observationToEuclidean z) := by
    have hmap : ∀ᵐ x ∂gaussianObservationLaw.map
        (observationToEuclidean : Observation 1 1 →
          EuclideanSpace ℝ (ObservationCoordinate 1 1)),
        DifferentiableAt ℝ f x := by
      simpa [gaussianObservationLaw_map_observationToEuclidean] using hstd
    exact (ae_map_iff
      (observationCoordinateContinuousLinearEquiv.continuous.measurable.aemeasurable)
      (measurableSet_of_differentiableAt ℝ f)).mp hmap
  filter_upwards [hObsDiff] with z hz
  rw [observationLocalSlope_locallyLipschitzPullback_eq f
    hf.locallyLipschitz z hz]
  exact (sum_euclideanCoordinateSection_deriv_sq_eq_fderiv_norm_sq
    f (observationToEuclidean z) hz).symm

#print axioms deriv_euclideanCoordinateSection_eq_fderiv
#print axioms sum_euclideanCoordinateSection_deriv_sq_eq_fderiv_norm_sq
#print axioms lipschitzWith_euclideanCoordinateSection
#print axioms ae_standardGaussian_euclideanCoordinateEnergy
#print axioms ae_standardGaussianPi_euclideanCoordinateEnergy
#print axioms gaussianObservationLaw_map_observationToEuclidean
#print axioms ae_gaussianObservationLaw_observationLocalSlope_sq_eq_coordinateEnergy

end LOOConcentration

end
