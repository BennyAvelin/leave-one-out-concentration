import LOOConcentrationRevision.Geometry.EuclideanBlocks
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Constructions.Pi
import LOOConcentration.FunctionalInequalities.EntropyTensorization

set_option autoImplicit false
namespace LOOConcentration.Revision
open MeasureTheory
variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]

/-- Flatten the ordered array without permuting any observation coordinates. -/
noncomputable def productToEuclidean (D : κ → EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ (κ × ι) := WithLp.toLp 2 (fun q => D q.1 q.2)

/-- Recover each observation block in the same index order. -/
noncomputable def productOfEuclidean (x : EuclideanSpace ℝ (κ × ι)) :
    κ → EuclideanSpace ℝ ι := fun i => WithLp.toLp 2 (fun a => x (i, a))

omit [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι] in
@[simp] theorem productOfEuclidean_productToEuclidean (D : κ → EuclideanSpace ℝ ι) :
    productOfEuclidean (productToEuclidean D) = D := by
  funext i
  apply PiLp.ext
  intro a
  rfl

omit [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι] in
@[simp] theorem productToEuclidean_productOfEuclidean (x : EuclideanSpace ℝ (κ × ι)) :
    productToEuclidean (productOfEuclidean x) = x := by
  apply PiLp.ext
  rintro ⟨i, a⟩
  rfl

omit [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι] in
/-- The actual flattening is continuous for the product and Euclidean topologies. -/
theorem continuous_productToEuclidean :
    Continuous (productToEuclidean : (κ → EuclideanSpace ℝ ι) → EuclideanSpace ℝ (κ × ι)) := by
  apply (PiLp.continuous_toLp 2 (fun _ : κ × ι => ℝ)).comp
  exact continuous_pi fun q =>
    (PiLp.continuous_apply 2 (fun _ : ι => ℝ) q.2).comp (continuous_apply q.1)

omit [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι] in
theorem continuous_productOfEuclidean :
    Continuous (productOfEuclidean : EuclideanSpace ℝ (κ × ι) → κ → EuclideanSpace ℝ ι) := by
  apply continuous_pi
  intro i
  apply (PiLp.continuous_toLp 2 (fun _ : ι => ℝ)).comp
  exact continuous_pi fun a => PiLp.continuous_apply 2 (fun _ : κ × ι => ℝ) (i, a)

/-- Product law on the literal flattened Euclidean carrier. -/
noncomputable def euclideanProductLaw (μ : Measure (EuclideanSpace ℝ ι)) :
    Measure (EuclideanSpace ℝ (κ × ι)) :=
  (Measure.pi fun _ : κ => μ).map productToEuclidean

omit [DecidableEq κ] [DecidableEq ι] in
theorem euclideanProductLaw_isProbabilityMeasure
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (euclideanProductLaw (κ := κ) μ) := by
  unfold euclideanProductLaw
  exact Measure.isProbabilityMeasure_map continuous_productToEuclidean.measurable.aemeasurable

omit [DecidableEq κ] [DecidableEq ι] in
/-- Integration follows the actual pushforward law, without changing witnesses. -/
theorem integral_euclideanProductLaw
    (μ : Measure (EuclideanSpace ℝ ι))
    (F : EuclideanSpace ℝ (κ × ι) → ℝ) (hF : Measurable F) :
    (∫ x, F x ∂euclideanProductLaw (κ := κ) μ) =
      ∫ D, F (productToEuclidean D) ∂Measure.pi fun _ : κ => μ := by
  unfold euclideanProductLaw
  exact integral_map continuous_productToEuclidean.measurable.aemeasurable hF.aestronglyMeasurable

omit [DecidableEq κ] [DecidableEq ι] in
/-- Literal integral-entropy transport for the same density. Integrability for
entropy inequalities is discharged separately in the bounded generator class. -/
theorem entropy_euclideanProductLaw
    (μ : Measure (EuclideanSpace ℝ ι))
    (F : EuclideanSpace ℝ (κ × ι) → ℝ) (hF : Measurable F) :
    LOOConcentration.entropy (euclideanProductLaw (κ := κ) μ) F =
      LOOConcentration.entropy (Measure.pi fun _ : κ => μ)
        (fun D => F (productToEuclidean D)) := by
  unfold LOOConcentration.entropy
  rw [integral_euclideanProductLaw μ (fun x => F x * Real.log (F x)) (hF.mul hF.log),
      integral_euclideanProductLaw μ F hF]

omit [DecidableEq ι] in
/-- Actual sections on the flattened carrier are precisely coordinate replacement
in the same ordered raw array. -/
theorem euclideanCoordinateSection_productToEuclidean
    (F : EuclideanSpace ℝ (κ × ι) → ℝ)
    (D : κ → EuclideanSpace ℝ ι) (i : κ) (z : EuclideanSpace ℝ ι) :
    euclideanCoordinateSection F (productToEuclidean D) i z =
      F (productToEuclidean (Function.update D i z)) := by
  change F (productToEuclidean D + euclideanBlockInclusion i
    (z - WithLp.toLp 2 (fun a => productToEuclidean D (i, a)))) = _
  congr 1
  apply PiLp.ext
  rintro ⟨j, a⟩
  change D j a + (if j = i then z a - D i a else 0) = (Function.update D i z) j a
  by_cases hji : j = i
  · subst j
    simp
  · simp [hji]
end LOOConcentration.Revision
