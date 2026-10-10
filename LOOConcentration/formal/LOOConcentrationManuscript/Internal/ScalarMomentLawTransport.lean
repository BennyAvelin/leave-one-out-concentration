import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LOOConcentration.Manuscript.Internal

open MeasureTheory
open scoped ENNReal

theorem scalar_linearIsometry_moment_product_transport
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hSecond : Integrable (fun x : ℝ => x ^ 2) μ)
    (e : ℝ →ₗᵢ[ℝ] EuclideanSpace ℝ κ) :
    let ν := μ.map e
    (∀ x : ℝ, ‖e x‖ ^ 2 = x ^ 2) ∧
    Integrable (fun y : EuclideanSpace ℝ κ => ‖y‖ ^ 2) ν ∧
    ((∫ y : EuclideanSpace ℝ κ, ‖y‖ ^ 2 ∂ν) = ∫ x : ℝ, x ^ 2 ∂μ) ∧
    (∀ r : ℕ,
      (Measure.pi fun _ : Fin (r + 1) => μ).map
        (fun D : Fin (r + 1) → ℝ => fun i => e (D i)) =
          Measure.pi fun _ : Fin (r + 1) => ν) ∧
    (∀ (r : ℕ) (D : Fin (r + 1) → ℝ),
      (∑ i : Fin (r + 1), ‖e (D i)‖ ^ 2) =
        ∑ i : Fin (r + 1), (D i) ^ 2) := by
  let ν : Measure (EuclideanSpace ℝ κ) := μ.map e
  have heMeas : Measurable e := e.continuous.measurable
  have hnorm (x : ℝ) : ‖e x‖ ^ 2 = x ^ 2 := by
    calc
      ‖e x‖ ^ 2 = ‖x‖ ^ 2 := congrArg (fun z : ℝ => z ^ 2) (e.norm_map x)
      _ = x ^ 2 := by simp [Real.norm_eq_abs, sq_abs]
  have hν : Integrable (fun y : EuclideanSpace ℝ κ => ‖y‖ ^ 2) ν := by
    apply (integrable_map_measure
      (f := e) (g := fun y : EuclideanSpace ℝ κ => ‖y‖ ^ 2)
      (by fun_prop) heMeas.aemeasurable).2
    exact hSecond.congr (Filter.Eventually.of_forall fun x => (hnorm x).symm)
  have hmoment : (∫ y : EuclideanSpace ℝ κ, ‖y‖ ^ 2 ∂ν) =
      ∫ x : ℝ, x ^ 2 ∂μ := by
    calc
      (∫ y : EuclideanSpace ℝ κ, ‖y‖ ^ 2 ∂ν) =
          ∫ x : ℝ, ‖e x‖ ^ 2 ∂μ :=
        integral_map heMeas.aemeasurable hν.aestronglyMeasurable
      _ = ∫ x : ℝ, x ^ 2 ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => hnorm x)
  have hνprob : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map heMeas.aemeasurable
  have hνfinite : ν Set.univ < ∞ := by
    rw [hνprob.measure_univ]
    exact ENNReal.one_lt_top
  have hνsigma : SigmaFinite ν :=
    ⟨⟨⟨fun _ => Set.univ, fun _ => Set.mem_univ _,
      fun _ => hνfinite, by ext x; simp⟩⟩⟩
  refine ⟨hnorm, hν, hmoment, ?_, ?_⟩
  · intro r
    have hSigmaFamily : ∀ _i : Fin (r + 1), SigmaFinite ((μ).map e) :=
      fun _ => hνsigma
    simpa [ν] using (Measure.pi_map_pi (hμ := hSigmaFamily)
      (fun _ : Fin (r + 1) => heMeas.aemeasurable))
  · intro r D
    exact Finset.sum_congr rfl fun i _ => hnorm (D i)

end LOOConcentration.Manuscript.Internal
