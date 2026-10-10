import LOOConcentrationManuscript.Internal.KernelDensityExpectedQuery
import LOOConcentrationManuscript.Frozen.Definitions.KernelDensityEstimator
import LOOConcentration.Frozen.Foundations.FittedLoss

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open MeasureTheory Filter
open scoped Topology ENNReal

/-- The actual public KDE's expected fitted loss is the single-kernel expectation. -/
theorem kde_actual_expected_loss_single_kernel
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (K : {K : ℝ → ℝ // ContDiff ℝ 1 K ∧ (∀ x, 0 ≤ K x) ∧
      (∃ B : ℝ, ∀ x, |K x| ≤ B) ∧ (∫ x : ℝ, K x) = 1 ∧
      (∃ B : ℝ, ∀ x, |deriv K x| ≤ B)})
    (h : {t : ℝ // 0 < t}) :
    let φ := fun x : ℝ => ((fun _ : Fin 1 => x), (fun _ : Fin 1 => (0 : ℝ)))
    let ν := μ.map φ
    let T := fun r : ℕ => LOOConcentration.Manuscript.kernelDensityEstimator K h r
    let L := fun a _ : LOOConcentration.Responses 1 => |a 0|
    ∀ (r : ℕ) (z : LOOConcentration.Observation 1 1),
      Integrable (fun D => LOOConcentration.fittedLoss (T r) L D z)
        (Measure.pi fun _ : Fin (r + 1) => ν) ∧
      (∫ D, LOOConcentration.fittedLoss (T r) L D z ∂(Measure.pi fun _ => ν)) =
        ∫ x : ℝ, K.val ((z.1 0 - x) / h.val) / h.val ∂μ := by
  intro φ ν T L r z
  have hφ : Measurable φ := by fun_prop
  have : IsProbabilityMeasure ν := μ.isProbabilityMeasure_map hφ.aemeasurable
  let Ψ := fun X : Fin (r + 1) → ℝ => fun j => φ (X j)
  let P := Measure.pi fun _ : Fin (r + 1) => μ
  let Q := Measure.pi fun _ : Fin (r + 1) => ν
  let F := fun D => LOOConcentration.fittedLoss (T r) L D z
  have hMP : MeasurePreserving Ψ P Q :=
    measurePreserving_pi (fun _ => μ) (fun _ => ν)
      (fun _ => (show MeasurePreserving φ μ ν from ⟨hφ, rfl⟩))
  obtain ⟨C,hC⟩ := K.property.2.2.1
  obtain ⟨M,hM⟩ := K.property.2.2.2.2
  have hScalar := genericKDE_actual_expected_loss_and_query_bound μ K.val K.property.1
    K.property.2.1 C hC M hM h.val h.property r (z.1 0)
  have hFormula (X : Fin (r + 1) → ℝ) :
      F (Ψ X) = |(r + 1 : ℝ)⁻¹ * ∑ j : Fin (r + 1), K.val ((z.1 0 - X j) / h.val) / h.val| := by
    dsimp [F, T, L, Ψ, φ, LOOConcentration.fittedLoss,
      LOOConcentration.Manuscript.kernelDensityEstimator]
    congr 1
    rw [← Finset.sum_div]
    have hn : (r + 1 : ℝ) ≠ 0 := by positivity
    field_simp [hn, h.property.ne']
  have hKC : Continuous K.val := K.property.1.continuous
  have hCont : Continuous F := by
    dsimp [F, T, L, LOOConcentration.fittedLoss,
      LOOConcentration.Manuscript.kernelDensityEstimator]
    fun_prop
  have hComp : Integrable (fun X => F (Ψ X)) P :=
    hScalar.1.congr (Eventually.of_forall fun X => (hFormula X).symm)
  have hInt : Integrable F Q := (hMP.integrable_comp hCont.aestronglyMeasurable).mp hComp
  refine ⟨hInt, ?_⟩
  have hMapMeas : AEStronglyMeasurable F (P.map Ψ) := by
    rw [hMP.map_eq]
    exact hCont.aestronglyMeasurable
  have hMap := integral_map hMP.measurable.aemeasurable hMapMeas
  rw [hMP.map_eq] at hMap
  calc
    (∫ D, F D ∂Q) = ∫ X, F (Ψ X) ∂P := hMap
    _ = ∫ X, |(r + 1 : ℝ)⁻¹ * ∑ j : Fin (r + 1), K.val ((z.1 0 - X j) / h.val) / h.val| ∂P :=
      integral_congr_ae (Eventually.of_forall hFormula)
    _ = ∫ x : ℝ, K.val ((z.1 0 - x) / h.val) / h.val ∂μ := hScalar.2.1

end LOOConcentration.Manuscript.Internal
