import LOOConcentrationManuscript.Internal.IIDResponseAbsoluteMean
import Mathlib.Probability.Distributions.Gaussian.Real

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open MeasureTheory

/-- The Gaussian source deletion envelope is nonnegative, integrable, and
has exactly the manuscript's sample-normalized expectation. -/
theorem gaussianKernel_delete_bias_envelope_integral
    (μ : Measure (LOOConcentration.Observation 1 1)) [IsProbabilityMeasure μ]
    (hSecond : Integrable LOOConcentration.observationNormSq μ)
    (h δ : ℝ) (hh : 0 < h) (hδ : 0 < δ) (r : ℕ) (i : Fin (r+2)) :
    let C := (((Real.sqrt (2*Real.pi))⁻¹/h)/δ)
    let m := ∫ z : LOOConcentration.Observation 1 1, |z.2 0| ∂μ
    let P := Measure.pi (fun _ : Fin (r+2) => μ)
    let R := fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+2) =>
      C/(r+2 : ℝ)*(|(D i).2 0|+(1+C)*
        ((∑ j : Fin (r+1), |(D (i.succAbove j)).2 0|)/(r+1 : ℝ)))
    Integrable R P ∧ (∀ D, 0 ≤ R D) ∧
      (∫ D, R D ∂P) = C*m/(r+2 : ℝ)*(2+C) := by
  intro C m P R
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hFull := (iidResponse_full_and_deleted_absolute_mean μ hSecond).2.1 (r+1)
  have hCoord := hFull.2.2 i
  have hDel := (iidResponse_full_and_deleted_absolute_mean μ hSecond).2.2 r i
  let M := fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+2) =>
    (∑ j : Fin (r+1), |(D (i.succAbove j)).2 0|)/(r+1 : ℝ)
  have hM : Integrable M P := hDel.1
  have hMI : (∫ D, M D ∂P) = m := hDel.2
  have hSum : Integrable (fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+2) =>
      |(D i).2 0|+(1+C)*M D) P := hCoord.1.add (hM.const_mul (1+C))
  refine ⟨hSum.const_mul _,?_,?_⟩
  · intro D
    dsimp only [R]
    have hMean : 0 ≤ M D := div_nonneg (Finset.sum_nonneg (fun j _ => abs_nonneg _)) (by positivity)
    exact mul_nonneg (div_nonneg hC (by positivity))
      (add_nonneg (abs_nonneg _) (mul_nonneg (by positivity) hMean))
  · dsimp only [R]
    rw [integral_const_mul,integral_add hCoord.1 (hM.const_mul (1+C)),
      integral_const_mul,hCoord.2,hMI]
    ring

end LOOConcentration.Manuscript.Internal
