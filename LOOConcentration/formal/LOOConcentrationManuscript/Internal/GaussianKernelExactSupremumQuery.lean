import LOOConcentrationManuscript.Internal.GaussianKernelQueryDerivative
import LOOConcentrationManuscript.Internal.GaussianKernelResponseMeanBound
import LOOConcentrationManuscript.Internal.IIDResponseAbsoluteMean

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LOOConcentration.Manuscript.Internal
open MeasureTheory ProbabilityTheory

/-- The Gaussian value ceiling is the actual supremum, attained at zero. -/
theorem gaussianScaledKernel_value_supremum (h : ℝ) (hh : 0 < h) :
    sSup (Set.range (fun t : ℝ => |gaussianPDFReal 0 1 (t/h)/h|)) =
      (Real.sqrt (2*Real.pi))⁻¹/h := by
  let Kh := fun t : ℝ => gaussianPDFReal 0 1 (t/h)/h
  let W := (Real.sqrt (2*Real.pi))⁻¹/h
  obtain ⟨_,_,hBound,_⟩ := gaussianScaledKernel_value_and_derivative_bounds h hh
  have hBdd : BddAbove (Set.range (fun t : ℝ => |Kh t|)) := by
    refine ⟨W, ?_⟩
    rintro y ⟨t,rfl⟩
    exact hBound t
  have hZero : |Kh 0| = W := by
    have hval : Kh 0 = W := by
      dsimp [Kh,W,gaussianPDFReal]
      simp only [zero_div, sub_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
        neg_zero, mul_one, Real.exp_zero, mul_one]
    rw [hval, abs_of_nonneg (by dsimp [W]; positivity)]
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro y ⟨t,rfl⟩
    exact hBound t
  · simpa only [hZero] using le_csSup hBdd (Set.mem_range_self 0)

/-- The actual Gaussian predictor's query derivative and its source finite-response bound. -/
theorem gaussianKernel_actualDataset_query_exactSupremum_hasDerivAt_and_bound
    (h δ : ℝ) (hh : 0 < h) (hδ : 0 < δ) (r : ℕ)
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+1)) (x : ℝ) :
    let Kh := fun t : ℝ => gaussianPDFReal 0 1 (t/h)/h
    let W := (Real.sqrt (2*Real.pi))⁻¹/h
    let W₁ := sSup (Set.range (fun t : ℝ => |deriv Kh t|))
    let N := (r+1 : ℝ)
    let B := fun z : ℝ => (∑ i : Fin (r+1), Kh (z-(D i).1 0))+N*δ
    let T := fun z : ℝ => (∑ i : Fin (r+1), Kh (z-(D i).1 0)*(D i).2 0)/B z
    let S := ((∑ i : Fin (r+1), deriv Kh (x-(D i).1 0)*(D i).2 0)-
      T x*(∑ i : Fin (r+1), deriv Kh (x-(D i).1 0)))/B x
    HasDerivAt T S x ∧
      |S| ≤ (W₁/δ)*(1+W/δ)*((∑ i : Fin (r+1), |(D i).2 0|)/N) := by
  intro Kh W W₁ N B T S
  obtain ⟨_hSmooth,hNonneg,hBound,hDeriv⟩ := gaussianScaledKernel_value_and_derivative_bounds h hh
  have hN : 0 < N := by dsimp [N]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hBdd : BddAbove (Set.range (fun t : ℝ => |deriv Kh t|)) := by
    refine ⟨(Real.sqrt (2*Real.pi))⁻¹/h^2, ?_⟩
    rintro y ⟨t, rfl⟩
    exact (hDeriv t).2
  have hSup (t : ℝ) : |deriv Kh t| ≤ W₁ := le_csSup hBdd (Set.mem_range_self t)
  have hW₁ : 0 ≤ W₁ := (abs_nonneg (deriv Kh 0)).trans (hSup 0)
  have hND : 0 < N*δ := mul_pos hN hδ
  have hLower : N*δ ≤ B x := le_add_of_nonneg_left
    (Finset.sum_nonneg (fun i _ => hNonneg (x-(D i).1 0)))
  have hB : 0 < B x := lt_of_lt_of_le hND hLower
  have hWeight (i : Fin (r+1)) :
      HasDerivAt (fun z : ℝ => Kh (z-(D i).1 0)) (deriv Kh (x-(D i).1 0)) x := by
    have hk := (hDeriv (x-(D i).1 0)).1.differentiableAt.hasDerivAt
    simpa only [Function.comp_def, mul_one] using
      hk.comp x ((hasDerivAt_id' x).sub_const ((D i).1 0))
  let A := fun z : ℝ => ∑ i : Fin (r+1), Kh (z-(D i).1 0)*(D i).2 0
  let DA := ∑ i : Fin (r+1), deriv Kh (x-(D i).1 0)*(D i).2 0
  let DB := ∑ i : Fin (r+1), deriv Kh (x-(D i).1 0)
  have hA : HasDerivAt A DA x :=
    HasDerivAt.fun_sum (u:=Finset.univ) (fun i _ => (hWeight i).mul_const ((D i).2 0))
  have hBD : HasDerivAt B DB x :=
    (HasDerivAt.fun_sum (u:=Finset.univ) (fun i _ => hWeight i)).add_const (N*δ)
  have hQ := (positiveDenominator_quotient_hasFDerivAt A B _ _ x
    hA.hasFDerivAt hBD.hasFDerivAt hB).hasDerivAt
  simp only [smul_apply,sub_apply,ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul,one_mul] at hQ
  change HasDerivAt T ((B x^2)⁻¹*(B x*DA-A x*DB)) x at hQ
  have hFormula : (B x^2)⁻¹*(B x*DA-A x*DB) = S := by
    dsimp [S,T,A,DA,DB]
    field_simp
  rw [hFormula] at hQ
  refine ⟨hQ,?_⟩
  let Y := ∑ i : Fin (r+1), |(D i).2 0|
  have hY : 0 ≤ Y := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hAx : |A x| ≤ W*Y := by
    calc
      _ ≤ ∑ i : Fin (r+1), |Kh (x-(D i).1 0)*(D i).2 0| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin (r+1), W*|(D i).2 0| := Finset.sum_le_sum (fun i _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hBound _) (abs_nonneg _))
      _ = W*Y := (Finset.mul_sum _ _ _).symm
  have hT : |T x| ≤ W*Y/(N*δ) := by
    change |A x/B x| ≤ _
    rw [abs_div,abs_of_pos hB]
    exact (div_le_div_of_nonneg_right hAx hB.le).trans
      (div_le_div_of_nonneg_left (mul_nonneg hW hY) hND hLower)
  have hDA : |DA| ≤ W₁*Y := by
    calc
      _ ≤ ∑ i : Fin (r+1), |deriv Kh (x-(D i).1 0)*(D i).2 0| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin (r+1), W₁*|(D i).2 0| := Finset.sum_le_sum (fun i _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hSup _) (abs_nonneg _))
      _ = W₁*Y := (Finset.mul_sum _ _ _).symm
  have hDB : |DB| ≤ N*W₁ := by
    calc
      _ ≤ ∑ i : Fin (r+1), |deriv Kh (x-(D i).1 0)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin (r+1), W₁ := Finset.sum_le_sum (fun i _ => hSup _)
      _ = N*W₁ := by simp [N]
  have hNum : |DA-T x*DB| ≤ W₁*Y+(W*Y/(N*δ))*(N*W₁) :=
    (abs_sub _ _).trans (by
      rw [abs_mul]
      exact add_le_add hDA (mul_le_mul hT hDB (abs_nonneg _) (by positivity)))
  change |(DA-T x*DB)/B x| ≤ _
  rw [abs_div,abs_of_pos hB]
  calc
    _ ≤ (W₁*Y+(W*Y/(N*δ))*(N*W₁))/B x := div_le_div_of_nonneg_right hNum hB.le
    _ ≤ (W₁*Y+(W*Y/(N*δ))*(N*W₁))/(N*δ) :=
      div_le_div_of_nonneg_left (by positivity) hND hLower
    _ = (W₁/δ)*(1+W/δ)*(Y/N) := by field_simp


/-- Global query sensitivity of the actual stabilized Gaussian predictor, with
its sample-normalized response magnitude and fixed source parameters. -/
theorem gaussianKernel_actualDataset_query_exactSupremum_lipschitz_bound
    (h δ : ℝ) (hh : 0 < h) (hδ : 0 < δ) (r : ℕ)
    (D : LOOConcentration.Dataset (LOOConcentration.Observation 1 1) (r+1)) :
    let Kh := fun t : ℝ => gaussianPDFReal 0 1 (t/h)/h
    let W := (Real.sqrt (2*Real.pi))⁻¹/h
    let W₁ := sSup (Set.range (fun t : ℝ => |deriv Kh t|))
    let N := (r+1 : ℝ)
    let T := fun z : ℝ => (∑ i : Fin (r+1), Kh (z-(D i).1 0)*(D i).2 0)/
      ((∑ i : Fin (r+1), Kh (z-(D i).1 0))+N*δ)
    ∀ x x' : ℝ, |T x-T x'| ≤
      ((W₁/δ)*(1+W/δ)*((∑ i : Fin (r+1), |(D i).2 0|)/N))*|x-x'| := by
  intro Kh W W₁ N T
  let C := (W₁/δ)*(1+W/δ)*((∑ i : Fin (r+1), |(D i).2 0|)/N)
  have hW₁ : 0 ≤ W₁ := by
    obtain ⟨_,_,_,hDeriv⟩ := gaussianScaledKernel_value_and_derivative_bounds h hh
    have hBdd : BddAbove (Set.range (fun t : ℝ => |deriv Kh t|)) := by
      refine ⟨(Real.sqrt (2*Real.pi))⁻¹/h^2, ?_⟩
      rintro y ⟨t, rfl⟩
      exact (hDeriv t).2
    exact (abs_nonneg (deriv Kh 0)).trans (le_csSup hBdd (Set.mem_range_self 0))
  have hC : 0 ≤ C := by dsimp [C,W,N]; positivity
  let Cnn : NNReal := ⟨C,hC⟩
  have hDiff : Differentiable ℝ T := fun x =>
    (gaussianKernel_actualDataset_query_exactSupremum_hasDerivAt_and_bound h δ hh hδ r D x).1.differentiableAt
  have hBound (x : ℝ) : ‖deriv T x‖₊ ≤ Cnn := by
    obtain ⟨hDeriv,hBound⟩ := gaussianKernel_actualDataset_query_exactSupremum_hasDerivAt_and_bound h δ hh hδ r D x
    apply (NNReal.coe_le_coe).1
    change |deriv T x| ≤ C
    rw [hDeriv.deriv]
    exact hBound
  have hLip : LipschitzWith Cnn T := lipschitzWith_of_nnnorm_deriv_le hDiff hBound
  intro x x'
  have hp := hLip.dist_le_mul x x'
  have hcc : (Cnn : ℝ) = C := NNReal.coe_mk C hC
  rw [Real.dist_eq,Real.dist_eq,hcc] at hp
  exact hp


/-- Every pointwise expected absolute fitted loss exists, and its two query
coordinates have the manuscript's uniform Lipschitz constants. -/
theorem gaussianKernel_expected_absoluteLoss_exactSupremum_query_bound
    (μ : Measure (LOOConcentration.Observation 1 1)) [IsProbabilityMeasure μ]
    (hSecond : Integrable LOOConcentration.observationNormSq μ)
    (h δ : ℝ) (hh : 0 < h) (hδ : 0 < δ) :
    let Kh := fun t : ℝ => gaussianPDFReal 0 1 (t/h)/h
    let W := (Real.sqrt (2*Real.pi))⁻¹/h
    let W₁ := sSup (Set.range (fun t : ℝ => |deriv Kh t|))
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
    have hLip := gaussianKernel_actualDataset_query_exactSupremum_lipschitz_bound h δ hh hδ r D x x'
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
