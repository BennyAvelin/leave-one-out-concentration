import LOOConcentrationManuscript.Internal.MeanQuadraticQueryRegularity
import LOOConcentrationManuscript.Internal.MeanQuadraticIntegrabilityConsumer
import Mathlib.Analysis.Calculus.ContDiff.RCLike

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open MeasureTheory ProbabilityTheory
open scoped ContDiff

/-- The actual scalar-product expected loss, evaluated on every feature/response
query, has the manuscript's unchanged expected-loss gradient bound. -/
theorem empiricalMean_scalarProduct_expectedLoss_whole_query_regular
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hSecond : Integrable (fun x : ℝ => x ^ 2) μ) (r : ℕ) :
    let q := fun x : EuclideanSpace ℝ (Fin 1 ⊕ Fin 1) =>
      ∫ D : Fin (r + 1) → ℝ,
        (empiricalMean r (WithLp.toLp 2 D) - x (Sum.inr (0 : Fin 1))) ^ 2
        ∂(Measure.pi fun _ : Fin (r + 1) => μ)
    ContDiff ℝ ∞ q ∧ LocallyLipschitz q ∧
    ∀ x : EuclideanSpace ℝ (Fin 1 ⊕ Fin 1),
      DifferentiableAt ℝ q x ∧
      ‖gradient q x‖ ≤ 2 * |∫ t : ℝ, t ∂μ| + 2 * ‖x‖ := by
  intro q
  have hRisk := (empiricalMean_quadraticRisk_product_consumer μ hSecond r).2
  have hFun : q = (fun x : EuclideanSpace ℝ (Fin 1 ⊕ Fin 1) =>
      (x (Sum.inr (0 : Fin 1)) - ∫ t : ℝ, t ∂μ) ^ 2 +
        variance (id : ℝ → ℝ) μ / (r + 1 : ℝ)) := by
    funext x
    exact hRisk (x (Sum.inr (0 : Fin 1)))
  rw [hFun]
  obtain ⟨hSmooth, hGradient⟩ := quadraticMean_responseQuery_polynomial_regular
    (∫ t : ℝ, t ∂μ) (variance (id : ℝ → ℝ) μ / (r + 1 : ℝ))
  exact ⟨hSmooth, (hSmooth.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)).locallyLipschitz,
    hGradient⟩

end LOOConcentration.Manuscript.Internal
