import LOOConcentrationManuscript.Internal.GaussianKernelJointLossDeleteBias

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open MeasureTheory ProbabilityTheory

/-- One nonnegative bias numerator is fixed before sample size and deletion index. -/
theorem gaussianKernel_joint_delete_bias_uniform_rate
    (μ : Measure (LOOConcentration.Observation 1 1)) [IsProbabilityMeasure μ]
    (hSecond : Integrable LOOConcentration.observationNormSq μ)
    (h δ : ℝ) (hh : 0 < h) (hδ : 0 < δ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (r : ℕ) (i : Fin (r+2)),
    let P := Measure.pi (fun _ : Fin (r+2) => μ)
    let Q := P.prod μ
    let Kh := fun t : ℝ => gaussianPDFReal 0 1 (t/h)/h
    let Tfull := fun p : (LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+2)) ×
        LOOConcentration.Observation 1 1 =>
      (∑ j : Fin (r+2), Kh (p.2.1 0-(p.1 j).1 0)*(p.1 j).2 0)/
        ((∑ j : Fin (r+2), Kh (p.2.1 0-(p.1 j).1 0))+(r+2 : ℝ)*δ)
    let Tdel := fun p : (LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+2)) ×
        LOOConcentration.Observation 1 1 =>
      (∑ j : Fin (r+1), Kh (p.2.1 0-(p.1 (i.succAbove j)).1 0)*(p.1 (i.succAbove j)).2 0)/
        ((∑ j : Fin (r+1), Kh (p.2.1 0-(p.1 (i.succAbove j)).1 0))+(r+1 : ℝ)*δ)
    let Lfull := fun p => |Tfull p-(p.2.2 0)|
    let Ldel := fun p => |Tdel p-(p.2.2 0)|
    Integrable Lfull Q ∧ Integrable Ldel Q ∧
      Integrable (fun p => |Lfull p-Ldel p|) Q ∧
      (∫ p, |Lfull p-Ldel p| ∂Q) ≤ B/(r+2 : ℝ) ∧
      |(∫ p, Lfull p ∂Q)-(∫ p, Ldel p ∂Q)| ≤ B/(r+2 : ℝ) := by
  let C := (((Real.sqrt (2*Real.pi))⁻¹/h)/δ)
  let m := ∫ z : LOOConcentration.Observation 1 1, |z.2 0| ∂μ
  let B := C*m*(2+C)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hm : 0 ≤ m := integral_nonneg (fun z => abs_nonneg _)
  refine ⟨B,mul_nonneg (mul_nonneg hC hm) (by positivity),?_⟩
  intro r i P Q Kh Tfull Tdel Lfull Ldel
  have hp := gaussianKernel_actual_joint_absoluteLoss_delete_bias μ hSecond h δ hh hδ r i
  change Integrable Lfull Q ∧ Integrable Ldel Q ∧
    Integrable (fun p => |Lfull p-Ldel p|) Q ∧
    (∫ p, |Lfull p-Ldel p| ∂Q) ≤ C*m/(r+2 : ℝ)*(2+C) ∧
    |(∫ p, Lfull p ∂Q)-(∫ p, Ldel p ∂Q)| ≤ C*m/(r+2 : ℝ)*(2+C) at hp
  have hScale : C*m/(r+2 : ℝ)*(2+C) = B/(r+2 : ℝ) := by dsimp [B]; ring
  rw [hScale] at hp
  exact hp

end LOOConcentration.Manuscript.Internal
