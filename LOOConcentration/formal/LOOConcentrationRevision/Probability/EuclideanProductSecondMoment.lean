import LOOConcentrationRevision.Geometry.ProductEuclidean
import Mathlib.MeasureTheory.Integral.Pi

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory

private theorem norm_sq_productToEuclidean
    {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (D : κ → EuclideanSpace ℝ ι) :
    ‖productToEuclidean D‖^2 = ∑ i : κ, ‖D i‖^2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, productToEuclidean, Fintype.sum_prod_type]

/-- The actual flattened finite product has a raw squared-norm moment produced
from the one-space moment, including empty coordinate and product families. -/
theorem integrable_euclideanProductLaw_norm_sq
    {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hM2 : Integrable (fun x => ‖x‖^2) μ) :
    Integrable (fun x : EuclideanSpace ℝ (κ × ι) => ‖x‖^2)
      (euclideanProductLaw (κ := κ) μ) := by
  have hcoord (i : κ) : Integrable (fun D : κ → EuclideanSpace ℝ ι => ‖D i‖^2)
      (Measure.pi fun _ : κ => μ) :=
    (measurePreserving_eval (μ := fun _ : κ => μ) i).integrable_comp_of_integrable hM2
  have hsum : Integrable (fun D : κ → EuclideanSpace ℝ ι => ∑ i : κ, ‖D i‖^2)
      (Measure.pi fun _ : κ => μ) := integrable_finsetSum Finset.univ (fun i _ => hcoord i)
  have hcomp : Integrable
      ((fun x : EuclideanSpace ℝ (κ × ι) => ‖x‖^2) ∘ productToEuclidean)
      (Measure.pi fun _ : κ => μ) := by
    simpa only [Function.comp_def, norm_sq_productToEuclidean] using hsum
  exact (integrable_map_measure (continuous_norm.pow 2).aestronglyMeasurable
    continuous_productToEuclidean.measurable.aemeasurable).2 hcomp

end LOOConcentration.Revision
