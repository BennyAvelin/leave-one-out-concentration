import LOOConcentration.Probability.SampleTestLaw
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LOOConcentration.Manuscript.Internal

open MeasureTheory

private theorem genericKDE_observation_query_mean
    (μ : Measure (LOOConcentration.Observation 1 1)) [IsProbabilityMeasure μ]
    (K : ℝ → ℝ) (hK : Continuous K)
    (hK_nonneg : ∀ x, 0 ≤ K x) (C : ℝ) (hC : ∀ x, |K x| ≤ C)
    (h : ℝ) (hh : 0 < h) (n : ℕ) (t : ℝ) :
    let P := Measure.pi (fun _ : Fin (n + 1) => μ)
    let f := fun D : Fin (n + 1) → LOOConcentration.Observation 1 1 =>
      (n + 1 : ℝ)⁻¹ * ∑ j : Fin (n + 1), K ((t - (D j).1 0) / h) / h
    Integrable (fun D => |f D|) P ∧
      (∫ D, |f D| ∂P) = ∫ z, K ((t - z.1 0) / h) / h ∂μ := by
  intro P f
  have hCnonneg : 0 ≤ C := (abs_nonneg (K 0)).trans (hC 0)
  let a := fun z : LOOConcentration.Observation 1 1 => K ((t - z.1 0) / h) / h
  have haCont : Continuous a := (hK.comp (by fun_prop)).div_const h
  have haInt : Integrable a μ := by
    apply (integrable_const (C / h)).mono' haCont.measurable.aestronglyMeasurable
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hh]
    exact div_le_div_of_nonneg_right (hC _) hh.le
  have hCoord (j : Fin (n + 1)) :
      Integrable (fun D : Fin (n + 1) → LOOConcentration.Observation 1 1 => a (D j)) P ∧
        (∫ D, a (D j) ∂P) = ∫ z, a z ∂μ := by
    have hMP := measurePreserving_eval (fun _ : Fin (n + 1) => μ) j
    refine ⟨hMP.integrable_comp_of_integrable haInt, ?_⟩
    have hMapMeas : AEStronglyMeasurable a (Measure.map (Function.eval j) P) := by
      rw [hMP.map_eq]
      exact haInt.aestronglyMeasurable
    have hMap := integral_map hMP.measurable.aemeasurable hMapMeas
    rw [hMP.map_eq] at hMap
    exact hMap.symm
  have hfNonneg (D : Fin (n + 1) → LOOConcentration.Observation 1 1) : 0 ≤ f D := by
    dsimp [f]
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro j hj
    exact div_nonneg (hK_nonneg _) hh.le
  have hAbsEq : (fun D => |f D|) = fun D => f D := by
    funext D
    exact abs_of_nonneg (hfNonneg D)
  have hfInt : Integrable f P := by
    dsimp [f]
    exact (integrable_finsetSum Finset.univ (fun j _ => (hCoord j).1)).const_mul _
  refine ⟨?_, ?_⟩
  · rw [hAbsEq]
    exact hfInt
  · rw [hAbsEq]
    dsimp [f]
    rw [integral_const_mul]
    rw [integral_finsetSum Finset.univ (fun j _ => (hCoord j).1)]
    simp only [(hCoord _).2, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    have hn : (n + 1 : ℝ) ≠ 0 := by positivity
    rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

/-! For the literal bounded KDE, the independent test risk is the same
single-kernel mean for every actual training size. The bound also proves
integrability on the joint sample/test product law. -/
theorem genericKDE_actual_joint_query_mean
    (μ : Measure (LOOConcentration.Observation 1 1)) [IsProbabilityMeasure μ]
    (K : ℝ → ℝ) (hK : Continuous K)
    (hK_nonneg : ∀ x, 0 ≤ K x) (C : ℝ) (hC : ∀ x, |K x| ≤ C)
    (h : ℝ) (hh : 0 < h) (n : ℕ) :
    let P := Measure.pi (fun _ : Fin (n + 1) => μ)
    let Q := P.prod μ
    let F := fun p : (Fin (n + 1) → LOOConcentration.Observation 1 1) ×
        LOOConcentration.Observation 1 1 =>
      |(n + 1 : ℝ)⁻¹ * ∑ j : Fin (n + 1),
        K ((p.2.1 0 - (p.1 j).1 0) / h) / h|
    Integrable F Q ∧
      (∫ p, F p ∂Q) =
        ∫ z, ∫ o, K ((z.1 0 - o.1 0) / h) / h ∂μ ∂μ := by
  intro P Q F
  have hCnonneg : 0 ≤ C := (abs_nonneg (K 0)).trans (hC 0)
  let g := fun p : (Fin (n + 1) → LOOConcentration.Observation 1 1) ×
      LOOConcentration.Observation 1 1 =>
    (n + 1 : ℝ)⁻¹ * ∑ j : Fin (n + 1),
      K ((p.2.1 0 - (p.1 j).1 0) / h) / h
  have hgCont : Continuous g := by
    apply continuous_const.mul
    apply continuous_finsetSum
    intro j hj
    exact (hK.comp (by fun_prop)).div_const h
  have hgNonneg (p : (Fin (n + 1) → LOOConcentration.Observation 1 1) ×
      LOOConcentration.Observation 1 1) : 0 ≤ g p := by
    dsimp [g]
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro j hj
    exact div_nonneg (hK_nonneg _) hh.le
  have hTermBound (p : (Fin (n + 1) → LOOConcentration.Observation 1 1) ×
      LOOConcentration.Observation 1 1) (j : Fin (n + 1)) :
      K ((p.2.1 0 - (p.1 j).1 0) / h) / h ≤ C / h := by
    exact div_le_div_of_nonneg_right
      ((le_abs_self _).trans (hC _)) hh.le
  have hSumBound (p : (Fin (n + 1) → LOOConcentration.Observation 1 1) ×
      LOOConcentration.Observation 1 1) :
      (∑ j : Fin (n + 1), K ((p.2.1 0 - (p.1 j).1 0) / h) / h) ≤
        (n + 1 : ℝ) * (C / h) := by
    calc
      _ ≤ ∑ _j : Fin (n + 1), C / h :=
        Finset.sum_le_sum (fun j _ => hTermBound p j)
      _ = _ := by simp
  have hgBound (p : (Fin (n + 1) → LOOConcentration.Observation 1 1) ×
      LOOConcentration.Observation 1 1) : g p ≤ C / h := by
    dsimp [g]
    calc
      _ ≤ (n + 1 : ℝ)⁻¹ * ((n + 1 : ℝ) * (C / h)) :=
        mul_le_mul_of_nonneg_left (hSumBound p) (by positivity)
      _ = C / h := by
        have hn : (n + 1 : ℝ) ≠ 0 := by positivity
        rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]
  have hgAbsBound (p : (Fin (n + 1) → LOOConcentration.Observation 1 1) ×
      LOOConcentration.Observation 1 1) : |g p| ≤ C / h := by
    rw [abs_of_nonneg (hgNonneg p)]
    exact hgBound p
  have hgInt : Integrable g Q := by
    apply (integrable_const (C / h)).mono' hgCont.measurable.aestronglyMeasurable
    filter_upwards with p
    rw [Real.norm_eq_abs]
    exact hgAbsBound p
  have hFInt : Integrable F Q := by
    change Integrable (fun p => |g p|) Q
    simpa only [Real.norm_eq_abs] using hgInt.norm
  have hIter := integral_prod_symm (fun p => |g p|) hFInt
  refine ⟨hFInt, ?_⟩
  change (∫ p, |g p| ∂Q) = _
  rw [hIter]
  apply integral_congr_ae
  filter_upwards with z
  have hQuery := (genericKDE_observation_query_mean μ K hK hK_nonneg C hC h hh n
    (z.1 0)).2
  simpa only [P, g, Function.comp_apply] using hQuery

end LOOConcentration.Manuscript.Internal
