import LOOConcentrationRevision.Correspondence.ParameterizedGradient

/-!
# Measurable candidate derivatives for parameterized functions

The measurable coordinate derivative representatives define a jointly
measurable continuous linear map.  At points where a section is actually
differentiable, this map is its Fréchet derivative.
-/

set_option autoImplicit false

namespace LOOConcentration.Correspondence

open MeasureTheory

variable {ι α : Type*} [Fintype ι] [DecidableEq ι]

local notation "E" => EuclideanSpace ℝ ι

/-- The vector whose Euclidean coordinates are the measurable coordinate
derivative representatives. -/
noncomputable def candidateGradientVector (F : E × α → ℝ) (p : E × α) : E :=
  (EuclideanSpace.equiv ι ℝ).symm
    (fun i => coordinateDerivativeRepresentative F i p)

/-- A continuous linear map formed from the coordinate derivative
representatives. -/
noncomputable def candidateContinuousLinearMap (F : E × α → ℝ) (p : E × α) :
    E →L[ℝ] ℝ :=
  InnerProductSpace.toDual ℝ E (candidateGradientVector F p)

theorem measurable_candidateGradientVector [MeasurableSpace α] [MeasurableSpace E]
    [BorelSpace E] (F : E × α → ℝ) (hF : Measurable F) :
    Measurable (candidateGradientVector F) := by
  have hcoords : Measurable (fun p : E × α => fun i : ι =>
      coordinateDerivativeRepresentative F i p) :=
    measurable_pi_iff.2 fun i =>
      measurable_coordinateDerivativeRepresentative F hF i
  change Measurable (fun p : E × α => (EuclideanSpace.equiv ι ℝ).symm
    (fun i : ι => coordinateDerivativeRepresentative F i p))
  exact (EuclideanSpace.equiv ι ℝ).symm.continuous.measurable.comp hcoords

theorem measurable_candidateContinuousLinearMap [MeasurableSpace α]
    [MeasurableSpace E] [BorelSpace E]
    (F : E × α → ℝ) (hF : Measurable F) :
    Measurable (candidateContinuousLinearMap F) := by
  change Measurable (fun p : E × α =>
    InnerProductSpace.toDual ℝ E (candidateGradientVector F p))
  exact (InnerProductSpace.toDual ℝ E).continuous.measurable.comp
    (measurable_candidateGradientVector F hF)

theorem candidateGradientVector_eq_gradient (F : E × α → ℝ) (x : E) (z : α)
    (hF : DifferentiableAt ℝ (fun y : E => F (y, z)) x) :
    candidateGradientVector F (x, z) = gradient (fun y : E => F (y, z)) x := by
  let f : E → ℝ := fun y => F (y, z)
  have hcoord (i : ι) :
      coordinateDerivativeRepresentative F i (x, z) = gradient f x i := by
    rw [coordinateDerivativeRepresentative_eq_fderiv F x z i hF]
    rw [← inner_gradient_left]
    change inner ℝ (gradient f x) (EuclideanSpace.single i (1 : ℝ)) = gradient f x i
    rw [EuclideanSpace.inner_single_right]
    simp
  apply (EuclideanSpace.equiv ι ℝ).injective
  funext i
  simpa [candidateGradientVector, EuclideanSpace.equiv, f] using hcoord i

theorem candidateContinuousLinearMap_eq_fderiv (F : E × α → ℝ) (x : E) (z : α)
    (hF : DifferentiableAt ℝ (fun y : E => F (y, z)) x) :
    candidateContinuousLinearMap F (x, z) = fderiv ℝ (fun y : E => F (y, z)) x := by
  rw [candidateContinuousLinearMap, candidateGradientVector_eq_gradient F x z hF]
  exact toDual_gradient

theorem differentiableAt_hasFDerivAt_candidate (F : E × α → ℝ) (x : E) (z : α)
    (hF : DifferentiableAt ℝ (fun y : E => F (y, z)) x) :
    HasFDerivAt (fun y : E => F (y, z))
      (candidateContinuousLinearMap F (x, z)) x := by
  rw [candidateContinuousLinearMap_eq_fderiv F x z hF]
  exact hF.hasFDerivAt

theorem locallyLipschitz_section_ae_hasFDerivAt_candidate (F : E × α → ℝ) (z : α)
    (hF : LocallyLipschitz (fun y : E => F (y, z))) :
    ∀ᵐ x ∂(volume : Measure E),
      HasFDerivAt (fun y : E => F (y, z))
        (candidateContinuousLinearMap F (x, z)) x := by
  filter_upwards [locallyLipschitz_ae_differentiableAt (fun y : E => F (y, z)) hF]
    with x hx
  exact differentiableAt_hasFDerivAt_candidate F x z hx

end LOOConcentration.Correspondence
