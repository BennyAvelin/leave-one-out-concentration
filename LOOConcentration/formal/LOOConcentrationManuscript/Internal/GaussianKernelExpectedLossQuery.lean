import LOOConcentrationManuscript.Internal.GaussianKernelQueryLipschitzConsumer
import LOOConcentrationManuscript.Internal.GaussianKernelResponseMeanBound
import LOOConcentrationManuscript.Internal.IIDResponseAbsoluteMean

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open MeasureTheory ProbabilityTheory

/-- Every pointwise expected absolute fitted loss exists, and its two query
coordinates have the manuscript's uniform Lipschitz constants. -/
theorem gaussianKernel_expected_absoluteLoss_query_bound
    (μ : Measure (LOOConcentration.Observation 1 1)) [IsProbabilityMeasure μ]
    (hSecond : Integrable LOOConcentration.observationNormSq μ)
    (h δ : ℝ) (hh : 0 < h) (hδ : 0 < δ) :
    let Kh := fun t : ℝ => gaussianPDFReal 0 1 (t/h)/h
    let W := (Real.sqrt (2*Real.pi))⁻¹/h
    let W₁ := (Real.sqrt (2*Real.pi))⁻¹/h^2
    let A := (W₁/δ)*(1+W/δ)
    let m := ∫ z : LOOConcentration.Observation 1 1, |z.2 0| ∂μ
    ∀ r : ℕ,
      let P := Measure.pi (fun _ : Fin (r+1) => μ)
      let T := fun (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+1)) (x : ℝ) =>
        (∑ i : Fin (r+1), Kh (x-(D i).1 0)*(D i).2 0)/
          ((∑ i : Fin (r+1), Kh (x-(D i).1 0))+(r+1 : ℝ)*δ)
      let L := fun D x y => |T D x-y|
      (∀ x y : ℝ, Integrable (fun D => L D x y) P) ∧
        ∀ x y x' y' : ℝ,
          |(∫ D, L D x y ∂P)-(∫ D, L D x' y' ∂P)| ≤
            A*m*|x-x'|+|y-y'| := by
  intro Kh W W₁ A m r P T L
  let M := fun D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+1) =>
    (∑ i : Fin (r+1), |(D i).2 0|)/(r+1 : ℝ)
  have hMean := (iidResponse_full_and_deleted_absolute_mean μ hSecond).2.1 r
  have hM : Integrable M P := hMean.1
  have hMI : (∫ D, M D ∂P) = m := hMean.2.1
  have hTMeas (x : ℝ) : Measurable (fun D => T D x) := by
    dsimp [T,Kh]
    fun_prop
  have hTInt (x : ℝ) : Integrable (fun D => T D x) P := by
    apply (hM.const_mul (W/δ)).mono' (hTMeas x).aestronglyMeasurable
    filter_upwards [] with D
    rw [Real.norm_eq_abs]
    exact gaussianKernel_actualDataset_response_mean_bound h δ hh hδ r D x
  have hLInt (x y : ℝ) : Integrable (fun D => L D x y) P :=
    ((hTInt x).sub (integrable_const y)).abs
  refine ⟨hLInt,?_⟩
  intro x y x' y'
  have hPoint (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+1)) :
      |L D x y-L D x' y'| ≤ (A*M D)*|x-x'|+|y-y'| := by
    have hLip := gaussianKernel_actualDataset_query_lipschitz_bound h δ hh hδ r D x x'
    change |T D x-T D x'| ≤ (A*M D)*|x-x'| at hLip
    calc
      _ ≤ |(T D x-y)-(T D x'-y')| := abs_abs_sub_abs_le_abs_sub _ _
      _ = |(T D x-T D x')-(y-y')| := congrArg abs (by ring)
      _ ≤ |T D x-T D x'|+|y-y'| := abs_sub _ _
      _ ≤ _ := add_le_add hLip (le_refl _)
  have hEnvelope : Integrable (fun D => (A*M D)*|x-x'|+|y-y'|) P :=
    ((hM.const_mul A).mul_const _).add (integrable_const _)
  calc
    _ = |∫ D, L D x y-L D x' y' ∂P| := by rw [integral_sub (hLInt x y) (hLInt x' y')]
    _ ≤ ∫ D, |L D x y-L D x' y'| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ D, (A*M D)*|x-x'|+|y-y'| ∂P :=
      integral_mono ((hLInt x y).sub (hLInt x' y')).abs hEnvelope hPoint
    _ = _ := by
      rw [integral_add ((hM.const_mul A).mul_const _) (integrable_const _),
        integral_mul_const,integral_const_mul,hMI,integral_const]
      simp only [measureReal_def,measure_univ,ENNReal.toReal_one,one_smul]

end LOOConcentration.Manuscript.Internal
