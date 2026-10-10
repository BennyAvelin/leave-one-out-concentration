import LOOConcentrationManuscript.Internal.GaussianKernelExpectedLossQuery
import LOOConcentration.Geometry.NormTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open MeasureTheory ProbabilityTheory

/-- One positive query-Lipschitz constant for the actual expected fitted loss
is fixed before every training-sample size and every pair of test observations. -/
theorem gaussianKernel_expected_absoluteLoss_shared_query_constant
    (μ : Measure (LOOConcentration.Observation 1 1)) [IsProbabilityMeasure μ]
    (hSecond : Integrable LOOConcentration.observationNormSq μ)
    (h δ : ℝ) (hh : 0 < h) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ,
      let P := Measure.pi (fun _ : Fin (r+1) => μ)
      let Kh := fun t : ℝ => gaussianPDFReal 0 1 (t/h)/h
      let L := fun (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+1))
          (z : LOOConcentration.Observation 1 1) =>
        |(∑ i : Fin (r+1), Kh (z.1 0-(D i).1 0)*(D i).2 0)/
          ((∑ i : Fin (r+1), Kh (z.1 0-(D i).1 0))+(r+1 : ℝ)*δ)-z.2 0|
      (∀ z, Integrable (fun D => L D z) P) ∧
        ∀ z z', |(∫ D, L D z ∂P)-(∫ D, L D z' ∂P)| ≤
          C*LOOConcentration.observationNorm (z-z') := by
  let W := (Real.sqrt (2*Real.pi))⁻¹/h
  let W₁ := (Real.sqrt (2*Real.pi))⁻¹/h^2
  let A := (W₁/δ)*(1+W/δ)
  let m := ∫ z : LOOConcentration.Observation 1 1, |z.2 0| ∂μ
  have hA : 0 ≤ A := by dsimp [A,W,W₁]; positivity
  have hm : 0 ≤ m := integral_nonneg (fun z => abs_nonneg _)
  let C := A*m+1
  have hAm : 0 ≤ A*m := mul_nonneg hA hm
  refine ⟨C,add_pos_of_nonneg_of_pos hAm zero_lt_one,?_⟩
  intro r P Kh L
  have hField := gaussianKernel_expected_absoluteLoss_query_bound μ hSecond h δ hh hδ r
  refine ⟨fun z => hField.1 (z.1 0) (z.2 0),?_⟩
  intro z z'
  let q := LOOConcentration.observationNorm (z-z')
  have hq : q = Real.sqrt ((z.1 0-z'.1 0)^2+(z.2 0-z'.2 0)^2) := by
    simp only [q,LOOConcentration.observationNorm,LOOConcentration.observationNormSq,Fin.sum_univ_one]
    rfl
  have hx : |z.1 0-z'.1 0| ≤ q := by
    rw [hq,← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg _))
  have hy : |z.2 0-z'.2 0| ≤ q := by
    rw [hq,← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (le_add_of_nonneg_left (sq_nonneg _))
  have hPoint := hField.2 (z.1 0) (z.2 0) (z'.1 0) (z'.2 0)
  change |(∫ D, L D z ∂P)-(∫ D, L D z' ∂P)| ≤ A*m*|z.1 0-z'.1 0|+|z.2 0-z'.2 0| at hPoint
  apply hPoint.trans
  calc
    _ ≤ A*m*q+q := add_le_add (mul_le_mul_of_nonneg_left hx hAm) hy
    _ = C*q := by dsimp [C]; ring

end LOOConcentration.Manuscript.Internal
