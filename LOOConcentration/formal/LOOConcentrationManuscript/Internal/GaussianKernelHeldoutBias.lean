import LOOConcentrationManuscript.Internal.GaussianKernelJointLossDeleteBiasConsumer
import LOOConcentration.Probability.SampleTestLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open MeasureTheory ProbabilityTheory

/-- The actual held-out deleted absolute loss is integrable and has the same
expectation as the deleted fit at a fresh independent test. Consequently the
source bias bound holds for the actual leave-one-out risk comparison. -/
theorem gaussianKernel_actual_heldout_delete_loss_bias
    (μ : Measure (LOOConcentration.Observation 1 1)) [IsProbabilityMeasure μ]
    (hSecond : Integrable LOOConcentration.observationNormSq μ)
    (h δ : ℝ) (hh : 0 < h) (hδ : 0 < δ) (r : ℕ) (i : Fin (r+2)) :
    let P := Measure.pi (fun _ : Fin (r+2) => μ)
    let Q := P.prod μ
    let C := (((Real.sqrt (2*Real.pi))⁻¹/h)/δ)
    let m := ∫ z : LOOConcentration.Observation 1 1, |z.2 0| ∂μ
    let Kh := fun t : ℝ => gaussianPDFReal 0 1 (t/h)/h
    let F := fun p : (Fin (r+1) → LOOConcentration.Observation 1 1) ×
        LOOConcentration.Observation 1 1 =>
      |(∑ j : Fin (r+1), Kh (p.2.1 0-(p.1 j).1 0)*(p.1 j).2 0)/
        ((∑ j : Fin (r+1), Kh (p.2.1 0-(p.1 j).1 0))+(r+1 : ℝ)*δ)-p.2.2 0|
    let Lheld := fun D : Fin (r+2) → LOOConcentration.Observation 1 1 =>
      F (LOOConcentration.deleteAt D i,D i)
    let LfreshDel := fun p : (Fin (r+2) → LOOConcentration.Observation 1 1) ×
        LOOConcentration.Observation 1 1 => F (LOOConcentration.deleteAt p.1 i,p.2)
    let Lfull := fun p : (Fin (r+2) → LOOConcentration.Observation 1 1) ×
        LOOConcentration.Observation 1 1 =>
      |(∑ j : Fin (r+2), Kh (p.2.1 0-(p.1 j).1 0)*(p.1 j).2 0)/
        ((∑ j : Fin (r+2), Kh (p.2.1 0-(p.1 j).1 0))+(r+2 : ℝ)*δ)-p.2.2 0|
    Integrable Lheld P ∧ Integrable LfreshDel Q ∧ Integrable Lfull Q ∧
      (∫ D, Lheld D ∂P) = (∫ p, LfreshDel p ∂Q) ∧
      |(∫ D, Lheld D ∂P)-(∫ p, Lfull p ∂Q)| ≤ C*m/(r+2 : ℝ)*(2+C) := by
  intro P Q C m Kh F Lheld LfreshDel Lfull
  have hJoint := gaussianKernel_actual_joint_absoluteLoss_delete_bias μ hSecond h δ hh hδ r i
  have hFullInt : Integrable Lfull Q := hJoint.1
  have hDelInt : Integrable LfreshDel Q := hJoint.2.1
  let Pdel := Measure.pi (fun _ : Fin (r+1) => μ)
  let Qdel := Pdel.prod μ
  have hHeldMap := LOOConcentration.deleted_sample_and_heldout_measurePreserving μ i
  have hDeleteMap : MeasurePreserving
      (fun D : Fin (r+2) → LOOConcentration.Observation 1 1 => LOOConcentration.deleteAt D i)
      P Pdel := measurePreserving_fst.comp hHeldMap
  have hFreshMap : MeasurePreserving
      (fun p : (Fin (r+2) → LOOConcentration.Observation 1 1) ×
        LOOConcentration.Observation 1 1 => (LOOConcentration.deleteAt p.1 i,p.2)) Q Qdel :=
    hDeleteMap.prod (MeasurePreserving.id μ)
  have hKhCont : Continuous Kh :=
    (gaussianScaledKernel_value_and_derivative_bounds h hh).1.continuous
  have hKhNonneg : ∀ x, 0 ≤ Kh x :=
    (gaussianScaledKernel_value_and_derivative_bounds h hh).2.1
  have hNum : Continuous (fun p : (Fin (r+1) → LOOConcentration.Observation 1 1) ×
      LOOConcentration.Observation 1 1 =>
        ∑ j : Fin (r+1), Kh (p.2.1 0-(p.1 j).1 0)*(p.1 j).2 0) :=
    continuous_finsetSum Finset.univ (fun j _ =>
      (hKhCont.comp (by fun_prop)).mul (by fun_prop))
  have hDen : Continuous (fun p : (Fin (r+1) → LOOConcentration.Observation 1 1) ×
      LOOConcentration.Observation 1 1 =>
        (∑ j : Fin (r+1), Kh (p.2.1 0-(p.1 j).1 0))+(r+1 : ℝ)*δ) :=
    (continuous_finsetSum Finset.univ (fun j _ => hKhCont.comp (by fun_prop))).add continuous_const
  have hDenPos (p : (Fin (r+1) → LOOConcentration.Observation 1 1) ×
      LOOConcentration.Observation 1 1) :
      0 < (∑ j : Fin (r+1), Kh (p.2.1 0-(p.1 j).1 0))+(r+1 : ℝ)*δ :=
    add_pos_of_nonneg_of_pos (Finset.sum_nonneg (fun j _ => hKhNonneg _))
      (mul_pos (by positivity) hδ)
  have hFCont : Continuous F :=
    continuous_abs.comp ((hNum.div hDen (fun p => (hDenPos p).ne')).sub (by fun_prop))
  have hFMeas : AEStronglyMeasurable F Qdel := hFCont.aestronglyMeasurable
  have hFInt : Integrable F Qdel := (hFreshMap.integrable_comp hFMeas).mp hDelInt
  have hHeldInt : Integrable Lheld P := hHeldMap.integrable_comp_of_integrable hFInt
  have hHeldEq : (∫ D, Lheld D ∂P) = ∫ p, F p ∂Qdel := by
    have hMapMeas : AEStronglyMeasurable F (Measure.map
        (fun D : Fin (r+2) → LOOConcentration.Observation 1 1 =>
          (LOOConcentration.deleteAt D i,D i)) P) := by
      rw [hHeldMap.map_eq]
      exact hFMeas
    have hMap := integral_map hHeldMap.measurable.aemeasurable hMapMeas
    rw [hHeldMap.map_eq] at hMap
    exact hMap.symm
  have hFreshEq : (∫ p, LfreshDel p ∂Q) = ∫ p, F p ∂Qdel := by
    have hMapMeas : AEStronglyMeasurable F (Measure.map
        (fun p : (Fin (r+2) → LOOConcentration.Observation 1 1) ×
          LOOConcentration.Observation 1 1 => (LOOConcentration.deleteAt p.1 i,p.2)) Q) := by
      rw [hFreshMap.map_eq]
      exact hFMeas
    have hMap := integral_map hFreshMap.measurable.aemeasurable hMapMeas
    rw [hFreshMap.map_eq] at hMap
    exact hMap.symm
  have hEq := hHeldEq.trans hFreshEq.symm
  refine ⟨hHeldInt,hDelInt,hFullInt,hEq,?_⟩
  rw [hEq,abs_sub_comm]
  exact hJoint.2.2.2.2

end LOOConcentration.Manuscript.Internal
