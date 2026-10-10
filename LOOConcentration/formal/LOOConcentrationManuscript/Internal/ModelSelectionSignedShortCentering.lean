import LOOConcentration.Probability.DeletedTransport
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option warningAsError true

namespace LOOConcentration.Manuscript.Internal

open MeasureTheory LOOConcentration

private theorem finite_average_integrable_and_mean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {N : ℕ} (hN : 0 < N) (g : Fin N → Ω → ℝ) (a : ℝ)
    (hg : ∀ i, Integrable (g i) P) (hmean : ∀ i, (∫ x, g i x ∂P) = a) :
    Integrable (fun x => (∑ i : Fin N, g i x) / (N : ℝ)) P ∧
    (∫ x, (∑ i : Fin N, g i x) / (N : ℝ) ∂P) = a := by
  have hsum := integrable_finsetSum Finset.univ (fun i _ => hg i)
  refine ⟨hsum.div_const (N : ℝ), ?_⟩
  rw [integral_div, integral_finsetSum Finset.univ (fun i _ => hg i)]
  simp_rw [hmean]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  exact mul_div_cancel_left₀ a hNreal

/-- The mean validation average and actual delete-one average have the same
expectation. Short product-law integrability is derived from a held-out input,
so the centered first term needs no extra short-product L¹ premise. -/
theorem modelSelection_signed_short_average_centering {k m n : ℕ}
    (μ : Measure (Observation k m)) [IsProbabilityMeasure μ]
    (F : Dataset (Observation k m) (n + 1) × Observation k m → ℝ)
    (hMeas : Measurable F)
    (hHeld : ∀ i : Fin (n + 2),
      Integrable (fun D : Dataset (Observation k m) (n + 2) =>
        F (deleteAt D i, D i)) (Measure.pi fun _ : Fin (n + 2) => μ)) :
    let P : Measure (Dataset (Observation k m) (n + 2)) :=
      Measure.pi fun _ : Fin (n + 2) => μ
    let Q : Measure (Dataset (Observation k m) (n + 1)) :=
      Measure.pi fun _ : Fin (n + 1) => μ
    let f : Observation k m → ℝ := fun z => ∫ D, F (D, z) ∂Q
    let V : Dataset (Observation k m) (n + 2) → ℝ :=
      fun D => (∑ i : Fin (n + 2), f (D i)) / (n + 2 : ℝ)
    let E : Dataset (Observation k m) (n + 2) → ℝ :=
      fun D => (∑ i : Fin (n + 2), F (deleteAt D i, D i)) / (n + 2 : ℝ)
    Integrable F (Q.prod μ) ∧ Integrable f μ ∧ Integrable V P ∧
      Integrable E P ∧ Integrable (fun D => V D - E D) P ∧
      (∫ D, V D ∂P) = ∫ p, F p ∂(Q.prod μ) ∧
      (∫ D, E D ∂P) = ∫ p, F p ∂(Q.prod μ) ∧
      (∫ D, V D - E D ∂P) = 0 := by
  dsimp only
  let P : Measure (Dataset (Observation k m) (n + 2)) :=
    Measure.pi fun _ : Fin (n + 2) => μ
  let Q : Measure (Dataset (Observation k m) (n + 1)) :=
    Measure.pi fun _ : Fin (n + 1) => μ
  let f : Observation k m → ℝ := fun z => ∫ D, F (D, z) ∂Q
  let i₀ : Fin (n + 2) := ⟨0, by omega⟩
  have hF : Integrable F (Q.prod μ) :=
    (deleted_section_integrable_iff μ i₀ F hMeas.aestronglyMeasurable).mp (hHeld i₀)
  have hf : Integrable f μ := hF.integral_prod_right
  have hcoord : ∀ i : Fin (n + 2),
      Integrable (fun D : Dataset (Observation k m) (n + 2) => f (D i)) P := by
    intro i
    exact (sample_coordinate_measurePreserving μ i).integrable_comp_of_integrable hf
  have hcoordMean : ∀ i : Fin (n + 2),
      (∫ D : Dataset (Observation k m) (n + 2), f (D i) ∂P) = ∫ z, f z ∂μ := by
    intro i
    let hmp := sample_coordinate_measurePreserving μ i
    have hfm : AEStronglyMeasurable f
        (P.map (fun D : Dataset (Observation k m) (n + 2) => D i)) := by
      rw [hmp.map_eq]
      exact hf.aestronglyMeasurable
    calc
      _ = ∫ z, f z ∂(P.map (fun D : Dataset (Observation k m) (n + 2) => D i)) :=
        (integral_map (measurable_pi_apply i).aemeasurable hfm).symm
      _ = _ := by rw [hmp.map_eq]
  have hV := finite_average_integrable_and_mean (N := n + 2) P (by omega)
    (fun i D => f (D i)) (∫ z, f z ∂μ) hcoord hcoordMean
  have hE := finite_average_integrable_and_mean (N := n + 2) P (by omega)
    (fun i D => F (deleteAt D i, D i)) (∫ p, F p ∂(Q.prod μ)) hHeld
    (fun i => deleted_section_integral μ i F hF)
  simp only [Nat.cast_add, Nat.cast_ofNat] at hV hE
  have hmean : (∫ z, f z ∂μ) = ∫ p, F p ∂(Q.prod μ) :=
    (integral_prod_symm F hF).symm
  have hVmean := hV.2.trans hmean
  refine ⟨hF, hf, hV.1, hE.1, hV.1.sub hE.1, hVmean, hE.2, ?_⟩
  rw [integral_sub hV.1 hE.1, hVmean, hE.2, sub_self]

end LOOConcentration.Manuscript.Internal
