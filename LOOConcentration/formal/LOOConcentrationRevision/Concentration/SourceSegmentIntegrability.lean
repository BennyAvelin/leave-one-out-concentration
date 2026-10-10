import LOOConcentrationRevision.Frozen.Bridges.Ae_gradient_segment_estimate
import LOOConcentrationRevision.Geometry.ProductEuclidean
import LOOConcentrationRevision.Probability.EuclideanProductSecondMoment

/-! Source-facing segment bounds and integrability under the actual finite-product law. -/

set_option autoImplicit false
namespace LOOConcentration.Revision

open MeasureTheory

/-- The source gradient hypothesis gives the exact segment estimate and, from
the raw second moment, integrability of the original function. -/
theorem source_segment_estimate_and_integrable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hM2 : Integrable (fun x : EuclideanSpace ℝ ι => ‖x‖ ^ 2) μ)
    (F : EuclideanSpace ℝ ι → ℝ) (hloc : LocallyLipschitz F) (a b : NNReal)
    (hgrad : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ ι)),
      DifferentiableAt ℝ F x ∧ ‖gradient F x‖ ≤ (a : ℝ) + (b : ℝ) * ‖x‖) :
    (∀ x y, |F x - F y| ≤
      ‖x - y‖ * ((a : ℝ) + (b : ℝ) / 2 * (‖x‖ + ‖y‖))) ∧ Integrable F μ := by
  refine ⟨?_, ?_⟩
  · intro x y
    exact ae_gradient_segment_estimate F hloc a b hgrad x y
  · let C : ℝ := |F 0| + (a : ℝ)
    let D : ℝ := (a : ℝ) + (b : ℝ) / 2
    have hC : 0 ≤ C := by
      dsimp [C]
      positivity
    have hD : 0 ≤ D := by
      dsimp [D]
      positivity
    have hmajor :=
      (hM2.add (integrable_const (μ := μ) (1 : ℝ))).const_mul (C + D)
    have hbound (x : EuclideanSpace ℝ ι) :
        ‖F x‖ ≤ C + D * ‖x‖ ^ 2 := by
      have hseg := ae_gradient_segment_estimate F hloc a b hgrad x 0
      have hseg' : |F x - F 0| ≤
          ‖x‖ * ((a : ℝ) + (b : ℝ) / 2 * ‖x‖) := by
        simpa only [sub_zero, norm_zero, add_zero] using hseg
      have htriangle : |F x| ≤ |F x - F 0| + |F 0| := by
        calc
          |F x| = ‖(F x - F 0) + F 0‖ := by
            rw [← Real.norm_eq_abs]
            congr 1
            ring
          _ ≤ ‖F x - F 0‖ + ‖F 0‖ := norm_add_le _ _
          _ = |F x - F 0| + |F 0| := by rw [Real.norm_eq_abs, Real.norm_eq_abs]
      have hr : ‖x‖ ≤ 1 + ‖x‖ ^ 2 := by
        nlinarith [sq_nonneg (‖x‖ - 1)]
      have ha : 0 ≤ (a : ℝ) := by exact_mod_cast a.2
      have hb : 0 ≤ (b : ℝ) := by exact_mod_cast b.2
      dsimp [C, D]
      nlinarith [hseg', htriangle, hr, ha, hb, sq_nonneg (‖x‖)]
    apply hmajor.mono' hloc.continuous.aestronglyMeasurable
    filter_upwards [] with x
    simp only [Pi.add_apply]
    calc
      ‖F x‖ ≤ C + D * ‖x‖ ^ 2 := hbound x
      _ ≤ (C + D) * (‖x‖ ^ 2 + 1) := by
        nlinarith [mul_nonneg hC (sq_nonneg (‖x‖)), hD]

/-- The same source estimate on the literal flattened finite product. Its raw
second moment is produced internally from the base-law moment. -/
theorem source_product_segment_estimate_and_integrable
    {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hM2 : Integrable (fun x : EuclideanSpace ℝ ι => ‖x‖ ^ 2) μ)
    (F : EuclideanSpace ℝ (κ × ι) → ℝ)
    (hloc : LocallyLipschitz F) (a b : NNReal)
    (hgrad : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (κ × ι))),
      DifferentiableAt ℝ F x ∧ ‖gradient F x‖ ≤ (a : ℝ) + (b : ℝ) * ‖x‖) :
    (∀ x y, |F x - F y| ≤
      ‖x - y‖ * ((a : ℝ) + (b : ℝ) / 2 * (‖x‖ + ‖y‖))) ∧
      Integrable F (euclideanProductLaw (κ := κ) μ) := by
  let ν := euclideanProductLaw (κ := κ) μ
  have hνM2 : Integrable (fun x : EuclideanSpace ℝ (κ × ι) => ‖x‖ ^ 2) ν :=
    integrable_euclideanProductLaw_norm_sq (κ := κ) μ hM2
  exact @source_segment_estimate_and_integrable (κ × ι) inferInstance inferInstance ν
    (euclideanProductLaw_isProbabilityMeasure μ) hνM2 F hloc a b hgrad

end LOOConcentration.Revision
