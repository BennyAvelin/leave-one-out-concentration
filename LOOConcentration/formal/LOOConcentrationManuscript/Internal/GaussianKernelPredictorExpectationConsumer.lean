import LOOConcentrationManuscript.Internal.GaussianKernelPredictorExpectation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LOOConcentration.Manuscript.Internal

open MeasureTheory ProbabilityTheory

/-- A single source numerator controls the actual full and deleted predictor
first moments and their expected absolute difference at every size and index. -/
theorem gaussianKernel_actual_joint_predictor_expectations_uniform_rate
    (μ : Measure (LOOConcentration.Observation 1 1)) [IsProbabilityMeasure μ]
    (hSecond : Integrable LOOConcentration.observationNormSq μ)
    (h δ : ℝ) (hh : 0 < h) (hδ : 0 < δ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (r : ℕ) (i : Fin (r+2)),
    let P := Measure.pi (fun _ : Fin (r+2) => μ)
    let Q := P.prod μ
    let C := (((Real.sqrt (2*Real.pi))⁻¹/h)/δ)
    let m := ∫ z : LOOConcentration.Observation 1 1, |z.2 0| ∂μ
    let Kh := fun t : ℝ => gaussianPDFReal 0 1 (t/h)/h
    let Tfull := fun p : (LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+2)) ×
        LOOConcentration.Observation 1 1 =>
      (∑ j : Fin (r+2), Kh (p.2.1 0-(p.1 j).1 0)*(p.1 j).2 0)/
        ((∑ j : Fin (r+2), Kh (p.2.1 0-(p.1 j).1 0))+(r+2 : ℝ)*δ)
    let Tdel := fun p : (LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+2)) ×
        LOOConcentration.Observation 1 1 =>
      (∑ j : Fin (r+1), Kh (p.2.1 0-(p.1 (i.succAbove j)).1 0)*(p.1 (i.succAbove j)).2 0)/
        ((∑ j : Fin (r+1), Kh (p.2.1 0-(p.1 (i.succAbove j)).1 0))+(r+1 : ℝ)*δ)
    Integrable Tfull Q ∧ Integrable (fun p => |Tfull p|) Q ∧
      (∫ p, |Tfull p| ∂Q) ≤ C*m ∧
      Integrable Tdel Q ∧ Integrable (fun p => |Tdel p|) Q ∧
      (∫ p, |Tdel p| ∂Q) ≤ C*m ∧
      Integrable (fun p => |Tfull p-Tdel p|) Q ∧
      (∫ p, |Tfull p-Tdel p| ∂Q) ≤ B/(r+2 : ℝ) := by
  let C := (((Real.sqrt (2*Real.pi))⁻¹/h)/δ)
  let m := ∫ z : LOOConcentration.Observation 1 1, |z.2 0| ∂μ
  let B := C*m*(2+C)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hm : 0 ≤ m := integral_nonneg (fun z => abs_nonneg _)
  refine ⟨B, mul_nonneg (mul_nonneg hC hm) (by positivity), ?_⟩
  intro r i P Q C' m' Kh Tfull Tdel
  have hFull := gaussianKernel_actual_joint_predictor_first_moments μ hSecond h δ hh hδ r i
  have hDiff := gaussianKernel_actual_joint_predictor_difference_first_moment μ hSecond h δ hh hδ r i
  change Integrable Tfull Q ∧ Integrable Tdel Q ∧
      Integrable (fun p => |Tfull p|) Q ∧ (∫ p, |Tfull p| ∂Q) ≤ C'*m' ∧
      Integrable (fun p => |Tdel p|) Q ∧ (∫ p, |Tdel p| ∂Q) ≤ C'*m' at hFull
  change Integrable (fun p => |Tfull p-Tdel p|) Q ∧
      (∀ p, |Tfull p-Tdel p| ≤
        C'/(r+2 : ℝ)*(|(p.1 i).2 0|+(1+C')*
          ((∑ j : Fin (r+1), |(p.1 (i.succAbove j)).2 0|)/(r+1 : ℝ)))) ∧
      (∫ p, |Tfull p-Tdel p| ∂Q) ≤ C'*m'/(r+2 : ℝ)*(2+C') at hDiff
  have hRate : C'*m'/(r+2 : ℝ)*(2+C') = B/(r+2 : ℝ) := by
    dsimp [B, C, m]
    ring
  rw [hRate] at hDiff
  exact ⟨hFull.1, hFull.2.2.1, hFull.2.2.2.1,
    hFull.2.1, hFull.2.2.2.2.1, hFull.2.2.2.2.2,
    hDiff.1, hDiff.2.2⟩

end LOOConcentration.Manuscript.Internal
