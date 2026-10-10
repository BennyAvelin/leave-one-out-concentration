import LOOConcentrationRevision.Probability.EuclideanProductSecondMoment
import LOOConcentrationRevision.Probability.MonotoneExponentialLimit
import Mathlib.MeasureTheory.Integral.Pi

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory Filter
open scoped Topology ENNReal

/-- The same flattened product norm has the source expectation, with no
independence or moment package supplied beyond the base raw second moment. -/
theorem integral_euclideanProductLaw_norm_sq
    {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hM2 : Integrable (fun x => ‖x‖ ^ 2) μ) :
    (∫ x : EuclideanSpace ℝ (κ × ι), ‖x‖ ^ 2 ∂euclideanProductLaw (κ := κ) μ) =
      (Fintype.card κ : ℝ) * ∫ z, ‖z‖ ^ 2 ∂μ := by
  have hmeas : Measurable (fun x : EuclideanSpace ℝ (κ × ι) => ‖x‖ ^ 2) := by fun_prop
  rw [integral_euclideanProductLaw (κ := κ) μ (fun x => ‖x‖ ^ 2) hmeas]
  have hnorm (D : κ → EuclideanSpace ℝ ι) :
      ‖productToEuclidean D‖ ^ 2 = ∑ i : κ, ‖D i‖ ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, productToEuclidean, Fintype.sum_prod_type]
  simp_rw [hnorm]
  have hcoord (i : κ) : Integrable (fun D : κ → EuclideanSpace ℝ ι => ‖D i‖ ^ 2)
      (Measure.pi fun _ : κ => μ) :=
    (measurePreserving_eval (μ := fun _ : κ => μ) i).integrable_comp_of_integrable hM2
  rw [integral_finsetSum Finset.univ (fun i _ => hcoord i)]
  have hid (i : κ) : (∫ D : κ → EuclideanSpace ℝ ι, ‖D i‖ ^ 2
      ∂Measure.pi fun _ : κ => μ) = ∫ z, ‖z‖ ^ 2 ∂μ := by
    exact integral_comp_eval (μ := fun _ : κ => μ) (i := i) hM2.aestronglyMeasurable
  simp_rw [hid]
  simp

/-- The manuscript's actual cap expectations increase to the same product
second moment, including empty coordinate and product families. -/
theorem product_norm_cap_expectation_monotone_tendsto
    {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hM2 : Integrable (fun x => ‖x‖ ^ 2) μ) :
    let ν := euclideanProductLaw (κ := κ) μ
    Monotone (fun j : ℕ => ∫ x : EuclideanSpace ℝ (κ × ι),
      ((j+1 : ℕ) : ℝ) * (1 - Real.exp (-‖x‖ ^ 2 / ((j+1 : ℕ) : ℝ))) ∂ν) ∧
    Tendsto (fun j : ℕ => ∫ x : EuclideanSpace ℝ (κ × ι),
      ((j+1 : ℕ) : ℝ) * (1 - Real.exp (-‖x‖ ^ 2 / ((j+1 : ℕ) : ℝ))) ∂ν)
      atTop (𝓝 ((Fintype.card κ : ℝ) * ∫ z, ‖z‖ ^ 2 ∂μ)) := by
  let ν := euclideanProductLaw (κ := κ) μ
  have hmeas : Measurable (fun x : EuclideanSpace ℝ (κ × ι) => ‖x‖ ^ 2) := by fun_prop
  have h := actual_cap_expectation_monotone_tendsto ν (fun x => ‖x‖ ^ 2)
    hmeas (fun x => sq_nonneg ‖x‖) (integrable_euclideanProductLaw_norm_sq μ hM2)
  have hmean := integral_euclideanProductLaw_norm_sq (κ := κ) μ hM2
  change (∫ x, ‖x‖ ^ 2 ∂ν) = _ at hmean
  rw [hmean] at h
  exact h

end LOOConcentration.Revision
