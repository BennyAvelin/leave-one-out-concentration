import LOOConcentrationManuscript.Internal.MeanQuadraticIntegrability
import LOOConcentrationManuscript.Frozen.Results.EmpiricalMeanQuadraticRiskFormula
import LOOConcentrationManuscript.Frozen.Results.EmpiricalMeanQuadraticLossDeleteBias

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LOOConcentration.Manuscript.Internal

open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem empiricalMean_quadraticRisk_product_consumer
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hSecond : Integrable (fun x : ℝ => x ^ 2) μ)
    (r : ℕ) :
    (∀ z : ℝ,
      Integrable (fun D : Fin (r + 1) → ℝ =>
        (empiricalMean r (WithLp.toLp 2 D) - z) ^ 2)
          (Measure.pi (fun _ : Fin (r + 1) => μ))) ∧
    (∀ z : ℝ,
      (∫ D : Fin (r + 1) → ℝ,
        (empiricalMean r (WithLp.toLp 2 D) - z) ^ 2
          ∂(Measure.pi (fun _ : Fin (r + 1) => μ))) =
        (z - ∫ x : ℝ, x ∂μ) ^ 2 +
          variance (id : ℝ → ℝ) μ / (r + 1 : ℝ)) := by
  let P : Measure (Fin (r + 1) → ℝ) := Measure.pi (fun _ : Fin (r + 1) => μ)
  have hLaw : ∀ i : Fin (r + 1),
      IdentDistrib (fun D : Fin (r + 1) → ℝ => D i) (id : ℝ → ℝ) P μ := by
    intro i
    refine ⟨(measurable_pi_apply i).aemeasurable, aemeasurable_id, ?_⟩
    simpa [P] using (Measure.pi_map_eval (μ := fun _ : Fin (r + 1) => μ) i)
  have hInd : iIndepFun
      (fun i : Fin (r + 1) => fun D : Fin (r + 1) → ℝ => D i) P := by
    exact iIndepFun_pi (X := fun _ : Fin (r + 1) => id)
      (fun _ => aemeasurable_id)
  change
    (∀ z : ℝ,
      Integrable (fun D : Fin (r + 1) → ℝ =>
        (empiricalMean r (WithLp.toLp 2 D) - z) ^ 2) P) ∧
    (∀ z : ℝ,
      (∫ D : Fin (r + 1) → ℝ,
        (empiricalMean r (WithLp.toLp 2 D) - z) ^ 2 ∂P) =
        (z - ∫ x : ℝ, x ∂μ) ^ 2 +
          variance (id : ℝ → ℝ) μ / (r + 1 : ℝ))
  refine ⟨?_, ?_⟩
  · intro z
    exact empiricalMean_quadraticLoss_integrable P μ hSecond r
      (fun i D => D i) hLaw z
  · intro z
    exact LOOConcentration.Manuscript.empiricalMean_quadraticRisk_formula
      P μ hSecond r (fun i D => D i) hLaw hInd z

theorem empiricalMean_quadraticDelete_product_consumer
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hSecond : Integrable (fun x : ℝ => x ^ 2) μ)
    (n : ℕ) :
    (∀ i : Fin (n + 2),
      Integrable (fun D : Fin (n + 3) → ℝ =>
        (empiricalMean n (WithLp.toLp 2
          (fun j : Fin (n + 1) => D ((i.succAbove j).castSucc))) -
          D i.castSucc) ^ 2) (Measure.pi (fun _ : Fin (n + 3) => μ)) ∧
      Integrable (fun D : Fin (n + 3) → ℝ =>
        (empiricalMean (n + 1) (WithLp.toLp 2
          (fun j : Fin (n + 2) => D j.castSucc)) -
          D (Fin.last (n + 2))) ^ 2) (Measure.pi (fun _ : Fin (n + 3) => μ))) ∧
    (∀ i : Fin (n + 2),
      |(∫ D : Fin (n + 3) → ℝ,
          (empiricalMean n (WithLp.toLp 2
            (fun j : Fin (n + 1) => D ((i.succAbove j).castSucc))) -
            D i.castSucc) ^ 2 ∂(Measure.pi (fun _ : Fin (n + 3) => μ))) -
        (∫ D : Fin (n + 3) → ℝ,
          (empiricalMean (n + 1) (WithLp.toLp 2
            (fun j : Fin (n + 2) => D j.castSucc)) -
            D (Fin.last (n + 2))) ^ 2 ∂(Measure.pi (fun _ : Fin (n + 3) => μ)))| =
        variance (id : ℝ → ℝ) μ /
          ((n + 2 : ℝ) * (n + 1 : ℝ))) := by
  let P : Measure (Fin (n + 3) → ℝ) := Measure.pi (fun _ : Fin (n + 3) => μ)
  have hLaw : ∀ j : Fin (n + 3),
      IdentDistrib (fun D : Fin (n + 3) → ℝ => D j) (id : ℝ → ℝ) P μ := by
    intro j
    refine ⟨(measurable_pi_apply j).aemeasurable, aemeasurable_id, ?_⟩
    simpa [P] using (Measure.pi_map_eval (μ := fun _ : Fin (n + 3) => μ) j)
  have hInd : iIndepFun
      (fun j : Fin (n + 3) => fun D : Fin (n + 3) → ℝ => D j) P := by
    exact iIndepFun_pi (X := fun _ : Fin (n + 3) => id)
      (fun _ => aemeasurable_id)
  change
    (∀ i : Fin (n + 2),
      Integrable (fun D : Fin (n + 3) → ℝ =>
        (empiricalMean n (WithLp.toLp 2
          (fun j : Fin (n + 1) => D ((i.succAbove j).castSucc))) -
          D i.castSucc) ^ 2) P ∧
      Integrable (fun D : Fin (n + 3) → ℝ =>
        (empiricalMean (n + 1) (WithLp.toLp 2
          (fun j : Fin (n + 2) => D j.castSucc)) -
          D (Fin.last (n + 2))) ^ 2) P) ∧
    (∀ i : Fin (n + 2),
      |(∫ D : Fin (n + 3) → ℝ,
          (empiricalMean n (WithLp.toLp 2
            (fun j : Fin (n + 1) => D ((i.succAbove j).castSucc))) -
            D i.castSucc) ^ 2 ∂P) -
        (∫ D : Fin (n + 3) → ℝ,
          (empiricalMean (n + 1) (WithLp.toLp 2
            (fun j : Fin (n + 2) => D j.castSucc)) -
            D (Fin.last (n + 2))) ^ 2 ∂P)| =
        variance (id : ℝ → ℝ) μ /
          ((n + 2 : ℝ) * (n + 1 : ℝ)))
  refine ⟨?_, ?_⟩
  · exact empiricalMean_deleteAndFull_quadraticLoss_integrable
      P μ hSecond n (fun j D => D j) hLaw
  · intro i
    exact LOOConcentration.Manuscript.empiricalMean_quadraticLoss_delete_bias
      P μ hSecond n (fun j D => D j) hLaw hInd i

end LOOConcentration.Manuscript.Internal
