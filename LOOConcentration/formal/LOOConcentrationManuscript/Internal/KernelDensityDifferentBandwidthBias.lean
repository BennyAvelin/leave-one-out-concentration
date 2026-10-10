import LOOConcentrationManuscript.Internal.KernelDensityHeldoutZeroBias
import LOOConcentrationManuscript.Frozen.Definitions.KernelDensityEstimator
import LOOConcentration.Frozen.Foundations.FittedLoss
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open MeasureTheory

/-- Different bandwidths produce exactly the difference of the independent
single-kernel expectations, with genuine integrability of both actual losses. -/
theorem kde_actual_different_bandwidth_bias
    (μ : Measure (LOOConcentration.Observation 1 1)) [IsProbabilityMeasure μ]
    (K : {K : ℝ → ℝ // ContDiff ℝ 1 K ∧ (∀ x, 0 ≤ K x) ∧
      (∃ B : ℝ, ∀ x, |K x| ≤ B) ∧ (∫ x : ℝ, K x) = 1 ∧
      (∃ B : ℝ, ∀ x, |deriv K x| ≤ B)})
    (hFull hDeleted : {t : ℝ // 0 < t}) (r : ℕ) (i : Fin (r+2)) :
    let P := Measure.pi (fun _ : Fin (r+2) => μ)
    let Q := P.prod μ
    let L : LOOConcentration.Responses 1 → LOOConcentration.Responses 1 → ℝ :=
      fun a _ => |a 0|
    let held := fun D => LOOConcentration.fittedLoss
      (LOOConcentration.Manuscript.kernelDensityEstimator K hDeleted r) L
      (LOOConcentration.deleteAt D i) (D i)
    let full := fun p => LOOConcentration.fittedLoss
      (LOOConcentration.Manuscript.kernelDensityEstimator K hFull (r+1)) L p.1 p.2
    Integrable held P ∧ Integrable full Q ∧
      |(∫ p, full p ∂Q)-(∫ D, held D ∂P)| =
      |(∫ z, ∫ o, K.val ((z.1 0-o.1 0)/hFull.val)/hFull.val ∂μ ∂μ) -
        (∫ z, ∫ o, K.val ((z.1 0-o.1 0)/hDeleted.val)/hDeleted.val ∂μ ∂μ)| := by
  classical
  intro P Q L held full
  obtain ⟨B,hB⟩ := K.property.2.2.1
  let Pdel := Measure.pi (fun _ : Fin (r+1) => μ)
  let Qdel := Pdel.prod μ
  let Gdel := fun p : (Fin (r+1) → LOOConcentration.Observation 1 1) ×
      LOOConcentration.Observation 1 1 =>
    |(r+1 : ℝ)⁻¹ * ∑ j : Fin (r+1),
      K.val ((p.2.1 0-(p.1 j).1 0)/hDeleted.val)/hDeleted.val|
  let Gfull := fun p : (Fin (r+2) → LOOConcentration.Observation 1 1) ×
      LOOConcentration.Observation 1 1 =>
    |((r+1 : ℝ)+1)⁻¹ * ∑ j : Fin (r+2),
      K.val ((p.2.1 0-(p.1 j).1 0)/hFull.val)/hFull.val|
  have hDel := genericKDE_actual_joint_query_mean μ K.val K.property.1.continuous
    K.property.2.1 B hB hDeleted.val hDeleted.property r
  have hFullJoint := genericKDE_actual_joint_query_mean μ K.val K.property.1.continuous
    K.property.2.1 B hB hFull.val hFull.property (r+1)
  have hDI : Integrable Gdel Qdel := hDel.1
  have hFI : Integrable Gfull Q := by
    simpa only [Gfull,Q,P,Nat.cast_add,Nat.cast_one] using hFullJoint.1
  have hHeldFormula : held = fun D => Gdel (LOOConcentration.deleteAt D i,D i) := by
    funext D
    dsimp [held,LOOConcentration.fittedLoss,L,Gdel,
      LOOConcentration.Manuscript.kernelDensityEstimator]
    congr 1
    rw [← Finset.sum_div]
    field_simp
  have hFullFormula : full=Gfull := by
    funext p
    dsimp [full,LOOConcentration.fittedLoss,L,Gfull,
      LOOConcentration.Manuscript.kernelDensityEstimator]
    congr 1
    rw [← Finset.sum_div]
    simp only [Nat.cast_add,Nat.cast_one]
    field_simp
  have hMP := LOOConcentration.deleted_sample_and_heldout_measurePreserving μ i
  have hHeldInt : Integrable held P := by
    rw [hHeldFormula]
    exact hMP.integrable_comp_of_integrable hDI
  have hFullInt : Integrable full Q := by rw [hFullFormula]; exact hFI
  have hHeldMean : (∫ D,held D ∂P) = ∫ z,∫ o,
      K.val ((z.1 0-o.1 0)/hDeleted.val)/hDeleted.val ∂μ ∂μ := by
    have hMapMeas : AEStronglyMeasurable Gdel (Measure.map
        (fun D : Fin (r+2) → LOOConcentration.Observation 1 1 =>
          (LOOConcentration.deleteAt D i,D i)) P) := by
      rw [hMP.map_eq]
      exact hDI.aestronglyMeasurable
    have hMap := integral_map hMP.measurable.aemeasurable hMapMeas
    rw [hMP.map_eq] at hMap
    rw [hHeldFormula]
    exact hMap.symm.trans hDel.2
  have hFullMean : (∫ p,full p ∂Q) = ∫ z,∫ o,
      K.val ((z.1 0-o.1 0)/hFull.val)/hFull.val ∂μ ∂μ := by
    rw [hFullFormula]
    simpa only [Gfull,Q,P,Nat.cast_add,Nat.cast_one] using hFullJoint.2
  exact ⟨hHeldInt,hFullInt,by rw [hHeldMean,hFullMean]⟩

end LOOConcentration.Manuscript.Internal
