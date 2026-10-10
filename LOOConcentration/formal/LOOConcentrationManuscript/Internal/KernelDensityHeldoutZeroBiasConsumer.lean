import LOOConcentrationManuscript.Internal.KernelDensityHeldoutZeroBias
import LOOConcentration.Frozen.Foundations.FittedLoss

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LOOConcentration.Manuscript.Internal

open MeasureTheory

/-! The literal fixed-bandwidth KDE has zero held-out delete-one bias under the
actual ordered IID sample and independent-test laws. The fitted loss is the
source loss `|a₀|`, which does not use the response coordinate. -/
theorem genericKDE_actual_heldout_zero_bias
    (μ : Measure (LOOConcentration.Observation 1 1)) [IsProbabilityMeasure μ]
    (K : ℝ → ℝ) (hK : Continuous K)
    (hK_nonneg : ∀ x, 0 ≤ K x) (C : ℝ) (hC : ∀ x, |K x| ≤ C)
    (h : ℝ) (hh : 0 < h) (r : ℕ) (i : Fin (r + 2)) :
    let P := Measure.pi (fun _ : Fin (r + 2) => μ)
    let Q := P.prod μ
    let T : ∀ n : ℕ, LOOConcentration.Estimator 1 1 (n + 1) := fun n D =>
      ⟨fun x _ => (n + 1 : ℝ)⁻¹ * ∑ j : Fin (n + 1),
        K ((x 0 - (D j).1 0) / h) / h,
        by
          apply continuous_pi
          intro _y
          exact continuous_const.mul
            (continuous_finsetSum Finset.univ (fun j _ =>
              (hK.comp (by fun_prop)).div_const h))⟩
    let L : LOOConcentration.Responses 1 → LOOConcentration.Responses 1 → ℝ :=
      fun a _ => |a 0|
    let Lheld := fun D : Fin (r + 2) → LOOConcentration.Observation 1 1 =>
      LOOConcentration.fittedLoss (T r) L (LOOConcentration.deleteAt D i) (D i)
    let LfreshDel := fun p :
        (Fin (r + 2) → LOOConcentration.Observation 1 1) ×
          LOOConcentration.Observation 1 1 =>
      LOOConcentration.fittedLoss (T r) L (LOOConcentration.deleteAt p.1 i) p.2
    let Lfull := fun p :
        (Fin (r + 2) → LOOConcentration.Observation 1 1) ×
          LOOConcentration.Observation 1 1 =>
      LOOConcentration.fittedLoss (T (r + 1)) L p.1 p.2
    Integrable Lheld P ∧ Integrable LfreshDel Q ∧ Integrable Lfull Q ∧
      (∫ D, Lheld D ∂P) = (∫ p, LfreshDel p ∂Q) ∧
      |(∫ D, Lheld D ∂P) - (∫ p, Lfull p ∂Q)| ≤ 0 := by
  intro P Q T L Lheld LfreshDel Lfull
  let Pdel := Measure.pi (fun _ : Fin (r + 1) => μ)
  let Qdel := Pdel.prod μ
  let Gdel := fun p : (Fin (r + 1) → LOOConcentration.Observation 1 1) ×
      LOOConcentration.Observation 1 1 =>
    |(r + 1 : ℝ)⁻¹ * ∑ j : Fin (r + 1),
      K ((p.2.1 0 - (p.1 j).1 0) / h) / h|
  let Gfull := fun p : (Fin (r + 2) → LOOConcentration.Observation 1 1) ×
      LOOConcentration.Observation 1 1 =>
    |(((r + 1 : ℕ) : ℝ) + 1)⁻¹ * ∑ j : Fin (r + 2),
      K ((p.2.1 0 - (p.1 j).1 0) / h) / h|
  have hDelJoint := genericKDE_actual_joint_query_mean μ K hK hK_nonneg C hC h hh r
  have hFullJoint := genericKDE_actual_joint_query_mean μ K hK hK_nonneg C hC h hh (r + 1)
  have hDelInt : Integrable Gdel Qdel := by
    simpa [Pdel, Qdel, Gdel] using hDelJoint.1
  have hFullInt : Integrable Gfull Q := by
    simpa only [P, Q, Gfull, Nat.add_assoc] using hFullJoint.1
  have hDelMean : (∫ p, Gdel p ∂Qdel) =
      ∫ z, ∫ o, K ((z.1 0 - o.1 0) / h) / h ∂μ ∂μ := by
    simpa [Pdel, Qdel, Gdel] using hDelJoint.2
  have hFullMean : (∫ p, Gfull p ∂Q) =
      ∫ z, ∫ o, K ((z.1 0 - o.1 0) / h) / h ∂μ ∂μ := by
    simpa only [P, Q, Gfull, Nat.add_assoc] using hFullJoint.2
  have hHeldFormula : Lheld = fun D => Gdel (LOOConcentration.deleteAt D i, D i) := by
    funext D
    rfl
  have hFreshFormula : LfreshDel =
      fun p => Gdel (LOOConcentration.deleteAt p.1 i, p.2) := by
    funext p
    rfl
  have hFullFormula : Lfull = fun p => Gfull p := by
    funext p
    rfl
  have hHeldMap :=
    LOOConcentration.deleted_sample_and_heldout_measurePreserving μ i
  have hHeldInt : Integrable Lheld P := by
    rw [hHeldFormula]
    exact hHeldMap.integrable_comp_of_integrable hDelInt
  have hDeleteMap : MeasurePreserving
      (fun D : Fin (r + 2) → LOOConcentration.Observation 1 1 =>
        LOOConcentration.deleteAt D i) P Pdel :=
    measurePreserving_fst.comp hHeldMap
  have hFreshMap : MeasurePreserving
      (fun p : (Fin (r + 2) → LOOConcentration.Observation 1 1) ×
        LOOConcentration.Observation 1 1 =>
          (LOOConcentration.deleteAt p.1 i, p.2)) Q Qdel :=
    hDeleteMap.prod (MeasurePreserving.id μ)
  have hFreshInt : Integrable LfreshDel Q := by
    rw [hFreshFormula]
    exact hFreshMap.integrable_comp_of_integrable hDelInt
  have hLfullInt : Integrable Lfull Q := by
    rw [hFullFormula]
    exact hFullInt
  have hHeldIntegral : (∫ D, Lheld D ∂P) = ∫ p, Gdel p ∂Qdel := by
    have hMapMeas : AEStronglyMeasurable Gdel (Measure.map
        (fun D : Fin (r + 2) → LOOConcentration.Observation 1 1 =>
          (LOOConcentration.deleteAt D i, D i)) P) := by
      rw [hHeldMap.map_eq]
      exact hDelInt.aestronglyMeasurable
    have hMap := integral_map hHeldMap.measurable.aemeasurable hMapMeas
    rw [hHeldMap.map_eq] at hMap
    exact hMap.symm
  have hFreshIntegral : (∫ p, LfreshDel p ∂Q) = ∫ p, Gdel p ∂Qdel := by
    have hMapMeas : AEStronglyMeasurable Gdel (Measure.map
        (fun p : (Fin (r + 2) → LOOConcentration.Observation 1 1) ×
          LOOConcentration.Observation 1 1 =>
            (LOOConcentration.deleteAt p.1 i, p.2)) Q) := by
      rw [hFreshMap.map_eq]
      exact hDelInt.aestronglyMeasurable
    have hMap := integral_map hFreshMap.measurable.aemeasurable hMapMeas
    rw [hFreshMap.map_eq] at hMap
    rw [hFreshFormula]
    exact hMap.symm
  have hFullIntegral : (∫ p, Lfull p ∂Q) = ∫ p, Gfull p ∂Q := by
    rw [hFullFormula]
  have hDelFull : (∫ p, Gdel p ∂Qdel) = ∫ p, Gfull p ∂Q :=
    hDelMean.trans hFullMean.symm
  have hHeldFull : (∫ D, Lheld D ∂P) = ∫ p, Lfull p ∂Q :=
    hHeldIntegral.trans (hDelFull.trans hFullIntegral.symm)
  refine ⟨hHeldInt, hFreshInt, hLfullInt, ?_, ?_⟩
  · exact hHeldIntegral.trans hFreshIntegral.symm
  · rw [hHeldFull]
    simp

end LOOConcentration.Manuscript.Internal
