import LOOConcentrationManuscript.Internal.GaussianKernelHeldoutBias

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open MeasureTheory ProbabilityTheory

/-- One source bias constant works for every actual held-out index and sample
size, preserving the held-out and independent-test laws and integrability. -/
theorem gaussianKernel_actual_heldout_bias_uniform_rate
    (μ : Measure (LOOConcentration.Observation 1 1)) [IsProbabilityMeasure μ]
    (hSecond : Integrable LOOConcentration.observationNormSq μ)
    (h δ : ℝ) (hh : 0 < h) (hδ : 0 < δ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (r : ℕ) (i : Fin (r+2)),
      let P := Measure.pi (fun _ : Fin (r+2) => μ)
      let Q := P.prod μ
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
        |(∫ D, Lheld D ∂P)-(∫ p, Lfull p ∂Q)| ≤ B/(r+2 : ℝ) := by
  let C := (((Real.sqrt (2*Real.pi))⁻¹/h)/δ)
  let m := ∫ z : LOOConcentration.Observation 1 1, |z.2 0| ∂μ
  let B := C*m*(2+C)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hm : 0 ≤ m := integral_nonneg (fun z => abs_nonneg _)
  refine ⟨B,mul_nonneg (mul_nonneg hC hm) (by linarith),?_⟩
  intro r i P Q Kh F Lheld LfreshDel Lfull
  have hActual := gaussianKernel_actual_heldout_delete_loss_bias μ hSecond h δ hh hδ r i
  refine ⟨hActual.1,hActual.2.1,hActual.2.2.1,hActual.2.2.2.1,?_⟩
  have hBound : |(∫ D, Lheld D ∂P)-(∫ p, Lfull p ∂Q)| ≤ C*m/(r+2 : ℝ)*(2+C) :=
    hActual.2.2.2.2
  convert hBound using 1
  dsimp [B]
  ring

end LOOConcentration.Manuscript.Internal
