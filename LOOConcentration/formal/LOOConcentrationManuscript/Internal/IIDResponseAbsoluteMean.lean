import LOOConcentration.Frozen.Norms.ObservationNormSq
import LOOConcentration.Frozen.Foundations.Dataset
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Constructions.Pi

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open MeasureTheory

private theorem response_absolute_integrable
    (μ : Measure (LOOConcentration.Observation 1 1)) [IsProbabilityMeasure μ]
    (hSecond : Integrable LOOConcentration.observationNormSq μ) :
    Integrable (fun z : LOOConcentration.Observation 1 1 => |z.2 0|) μ := by
  have hSquare : Integrable (fun z : LOOConcentration.Observation 1 1 => (z.2 0)^2) μ :=
    hSecond.mono' (by fun_prop) (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      simp only [LOOConcentration.observationNormSq,Fin.sum_univ_one]
      exact le_add_of_nonneg_left (sq_nonneg _))
  have hLp : MemLp (fun z : LOOConcentration.Observation 1 1 => z.2 0) 2 μ :=
    (memLp_two_iff_integrable_sq (by fun_prop)).2 hSquare
  simpa only [Real.norm_eq_abs] using (hLp.integrable one_le_two).norm

private theorem response_coordinate_integral
    (μ : Measure (LOOConcentration.Observation 1 1)) [IsProbabilityMeasure μ]
    (hAbs : Integrable (fun z : LOOConcentration.Observation 1 1 => |z.2 0|) μ)
    (n : ℕ) (i : Fin n) :
    let P := Measure.pi (fun _ : Fin n => μ)
    Integrable (fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) n => |(D i).2 0|) P ∧
      (∫ D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) n, |(D i).2 0| ∂P) =
      ∫ z : LOOConcentration.Observation 1 1, |z.2 0| ∂μ := by
  intro P
  have hMP := measurePreserving_eval (fun _ : Fin n => μ) i
  refine ⟨hMP.integrable_comp_of_integrable hAbs,?_⟩
  have hMapMeas : AEStronglyMeasurable (fun z : LOOConcentration.Observation 1 1 => |z.2 0|)
      (Measure.map (Function.eval i) P) := by
    rw [hMP.map_eq]
    exact hAbs.aestronglyMeasurable
  have hm := integral_map hMP.measurable.aemeasurable hMapMeas
  rw [show Measure.map (Function.eval i) P = μ from hMP.map_eq] at hm
  exact hm.symm

/-- The raw response has finite first moment, and both the full and every
ordered delete-one empirical absolute mean have exactly that expectation. -/
theorem iidResponse_full_and_deleted_absolute_mean
    (μ : Measure (LOOConcentration.Observation 1 1)) [IsProbabilityMeasure μ]
    (hSecond : Integrable LOOConcentration.observationNormSq μ) :
    let m := ∫ z : LOOConcentration.Observation 1 1, |z.2 0| ∂μ
    Integrable (fun z : LOOConcentration.Observation 1 1 => |z.2 0|) μ ∧
    (∀ r : ℕ,
      let P := Measure.pi (fun _ : Fin (r+1) => μ)
      let M := fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+1) =>
        (∑ j : Fin (r+1), |(D j).2 0|)/(r+1 : ℝ)
      Integrable M P ∧ (∫ D, M D ∂P) = m ∧
      (∀ j : Fin (r+1), Integrable (fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+1) => |(D j).2 0|) P ∧
        (∫ D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+1), |(D j).2 0| ∂P) = m)) ∧
    (∀ (r : ℕ) (i : Fin (r+2)),
      let P := Measure.pi (fun _ : Fin (r+2) => μ)
      let M := fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+2) =>
        (∑ j : Fin (r+1), |(D (i.succAbove j)).2 0|)/(r+1 : ℝ)
      Integrable M P ∧ (∫ D, M D ∂P) = m) := by
  intro m
  have hAbs := response_absolute_integrable μ hSecond
  refine ⟨hAbs,?_,?_⟩
  · intro r P M
    have hc (j : Fin (r+1)) := response_coordinate_integral μ hAbs (r+1) j
    have hSum : Integrable (fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+1) =>
        ∑ j : Fin (r+1), |(D j).2 0|) P :=
      integrable_finsetSum Finset.univ (fun j _ => (hc j).1)
    refine ⟨hSum.div_const _,?_,fun j => hc j⟩
    dsimp only [M]
    rw [integral_div,integral_finsetSum Finset.univ (fun j _ => (hc j).1)]
    simp only [(hc _).2]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have hN : (r+1 : ℝ) ≠ 0 := by positivity
    simp only [Nat.cast_add,Nat.cast_one]
    change ((r+1 : ℝ)*m)/(r+1 : ℝ)=m
    field_simp
  · intro r i P M
    have hc (j : Fin (r+1)) := response_coordinate_integral μ hAbs (r+2) (i.succAbove j)
    have hSum : Integrable (fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+2) =>
        ∑ j : Fin (r+1), |(D (i.succAbove j)).2 0|) P :=
      integrable_finsetSum Finset.univ (fun j _ => (hc j).1)
    refine ⟨hSum.div_const _,?_⟩
    dsimp only [M]
    rw [integral_div,integral_finsetSum Finset.univ (fun j _ => (hc j).1)]
    simp only [(hc _).2]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have hN : (r+1 : ℝ) ≠ 0 := by positivity
    simp only [Nat.cast_add,Nat.cast_one]
    change ((r+1 : ℝ)*m)/(r+1 : ℝ)=m
    field_simp

end LOOConcentration.Manuscript.Internal
